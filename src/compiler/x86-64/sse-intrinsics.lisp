;;;; SSE intrinsics support for x86-64

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!VM")

(defun ea-for-sse-stack (tn &optional (base rbp-tn))
  (make-ea :qword :base base
           :disp (- (* (+ (tn-offset tn)
                          2)
                       n-word-bytes))))

(defun float-sse-pack-p (tn)
  (eq (sb!c::tn-primitive-type tn) (primitive-type-or-lose 'float-sse-pack)))
(defun int-sse-pack-p (tn)
  (eq (sb!c::tn-primitive-type tn) (primitive-type-or-lose 'int-sse-pack)))

(define-move-fun (load-sse-pack-immediate 1) (vop x y)
  ((sse-pack-immediate) (sse-reg))
  (let ((x (register-inline-constant (tn-value x))))
    (if (float-sse-pack-p y)
        (inst movaps y x)
        (inst movdqa y x))))

(define-move-fun (load-sse-pack 2) (vop x y)
    ((sse-stack) (sse-reg))
  (if (or (float-sse-pack-p x) (float-sse-pack-p y))
      (inst movups y (ea-for-sse-stack x))
      (inst movdqu y (ea-for-sse-stack x))))

(define-move-fun (store-sse-pack 2) (vop x y)
  ((sse-reg) (sse-stack))
  (if (or (float-sse-pack-p x) (float-sse-pack-p y))
      (inst movups (ea-for-sse-stack y) x)
      (inst movdqu (ea-for-sse-stack y) x)))

(define-vop (sse-pack-move)
  (:args (x :scs (sse-reg)
            :target y
            :load-if (not (location= x y))))
  (:results (y :scs (sse-reg)
               :load-if (not (location= x y))))
  (:note "SSE move")
  (:generator 0
     (move y x)))
(define-move-vop sse-pack-move :move (sse-reg) (sse-reg))

(define-vop (move-from-sse)
  (:args (x :scs (sse-reg)))
  (:results (y :scs (descriptor-reg)))
  (:node-var node)
  (:note "SSE to pointer coercion")
  (:generator 13
     (with-fixed-allocation (y
                             sse-pack-widetag
                             sse-pack-size
                             node)
       (let ((ea (make-ea-for-object-slot
                  y sse-pack-lo-value-slot other-pointer-lowtag)))
         (if (float-sse-pack-p x)
             (inst movaps ea x)
             (inst movdqa ea x))))))
(define-move-vop move-from-sse :move
  (sse-reg) (descriptor-reg))

(define-vop (move-to-sse)
  (:args (x :scs (descriptor-reg)))
  (:results (y :scs (sse-reg)))
  (:note "pointer to SSE coercion")
  (:generator 2
    (let ((ea (make-ea-for-object-slot
               x sse-pack-lo-value-slot other-pointer-lowtag)))
      (if (float-sse-pack-p y)
          (inst movaps y ea)
          (inst movdqa y ea)))))
(define-move-vop move-to-sse :move (descriptor-reg) (sse-reg))

(define-vop (move-sse-arg)
  (:args (x :scs (sse-reg) :target y)
         (fp :scs (any-reg)
             :load-if (not (sc-is y sse-reg))))
  (:results (y))
  (:note "SSE argument move")
  (:generator 4
     (sc-case y
       (sse-reg
        (unless (location= x y)
          (if (or (float-sse-pack-p x)
                  (float-sse-pack-p y))
              (inst movaps y x)
              (inst movdqa y x))))
       (sse-stack
        (if (float-sse-pack-p x)
            (inst movups (ea-for-sse-stack y fp) x)
            (inst movdqu (ea-for-sse-stack y fp) x))))))
(define-move-vop move-sse-arg :move-arg
  (sse-reg descriptor-reg) (sse-reg))

(define-move-vop move-arg :move-arg (sse-reg) (descriptor-reg))


(define-vop (%sse-pack-low)
  (:translate %sse-pack-low)
  (:args (x :scs (sse-reg)))
  (:arg-types sse-pack)
  (:results (dst :scs (unsigned-reg)))
  (:result-types unsigned-num)
  (:policy :fast-safe)
  (:generator 3
    (inst movd dst x)))

(defun %sse-pack-low (x)
  (declare (type sse-pack x))
  (%sse-pack-low x))

(define-vop (%sse-pack-high)
  (:translate %sse-pack-high)
  (:args (x :scs (sse-reg)))
  (:arg-types sse-pack)
  (:temporary (:sc sse-reg) tmp)
  (:results (dst :scs (unsigned-reg)))
  (:result-types unsigned-num)
  (:policy :fast-safe)
  (:generator 3
    (inst movdqa tmp x)
    (inst psrldq tmp 8)
    (inst movd dst tmp)))

(defun %sse-pack-high (x)
  (declare (type sse-pack x))
  (%sse-pack-high x))

(define-vop (%make-sse-pack)
  (:translate %make-sse-pack)
  (:policy :fast-safe)
  (:args (lo :scs (unsigned-reg))
         (hi :scs (unsigned-reg)))
  (:arg-types unsigned-num unsigned-num)
  (:temporary (:sc sse-stack :target dst :to :result) tmp)
  (:results (dst :scs (sse-reg sse-stack)))
  (:result-types sse-pack)
  (:generator 5
    (let ((offset (- (* (1+ (tn-offset tmp))
                        n-word-bytes))))
      (inst mov (make-ea :qword :base rbp-tn :disp (- offset 8)) lo)
      (inst mov (make-ea :qword :base rbp-tn :disp offset) hi))
    (unless (location= dst tmp)
      (inst movdqu dst (ea-for-sse-stack tmp)))))

(defun %make-sse-pack (low high)
  (declare (type (unsigned-byte 64) low high))
  (%make-sse-pack low high))


#|
(defknown widen-sse-type (sse-pack) sse-pack)
(define-vop (widen-sse-type)
  (:policy :fast-safe)
  (:translate widen-sse-type)
  (:args (x :scs (sse-reg) :target r))
  (:arg-types sse-pack)
  (:results (r :scs (sse-reg)))
  (:result-types sse-pack)
  (:generator 0
     (move r x)))

(defknown pxor (sse-pack sse-pack) (sse-pack integer))

(define-vop (pxor)
  (:policy :fast-safe)
  (:translate pxor)
  (:args (x :scs (sse-reg) :target r)
         (y :scs (sse-reg)))
  (:arg-types sse-pack sse-pack)
  (:results (r :scs (sse-reg)))
  (:result-types int-sse-pack)
  (:generator 1
     (cond ((location= x r)
            (inst pxor r y))
           ((location= y r)
            (inst pxor r x))
           (t
            (inst movaps r x)
            (inst pxor r y)))))
|#
