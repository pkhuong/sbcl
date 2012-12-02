;;;; the VM definition of division-by-multiplication VOPs for the x86-64

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!VM")

(defun emit-mul-shift-add-tag (result x rax signedp
                               multiplier shift increment tag post-increment-p
                               rdx tmp copy-x
                               &aux (mask (ldb (byte tag 0) -1)))
  "result <- [(x * multiplier + increment) >> (shift + n-w-b)] << tag

   If post-increment-p, result is incremented by one if negative, before tagging

   tmp: only used if increment is large and non-zero
   copy-x: only used for signed multiplication by > signed-word constants
   If post-increment-p, at least one of the latter two must be provided"
  (declare (type tn result x rax)
           (type boolean signedp post-increment-p)
           (type (or word signed-word) multiplier)
           (type word increment)
           (type (mod #.n-word-bits) shift tag)
           (type tn rdx)
           (type (or tn null) tmp copy-x))
  (aver (location= rax rax-tn))
  (aver (location= rdx rdx-tn))
  (unless (setf post-increment-p (and post-increment-p signedp))
    (let ((delta (min shift tag)))
      (decf shift delta)
      (decf tag delta))
    (when (and (typep (ash multiplier tag) `(signed-byte ,(1+ n-word-bits)))
               (typep (ash increment tag) 'word))
      (setf multiplier (ash multiplier tag)
            increment  (ash increment tag)
            tag        0)))
  (flet ((load-values (&optional (multiplier multiplier))
           (inst mov rdx multiplier)
           (cond ((typep increment '(signed-byte 32)))
                 ((= multiplier increment)
                  (aver (tn-p tmp))
                  (inst mov tmp rdx))
                 ((= multiplier (- increment))
                  (aver (tn-p tmp))
                  (inst mov tmp rdx)
                  (inst neg tmp))
                 (t
                  (aver (tn-p tmp))
                  (inst mov tmp increment))))
         (increment (&optional (high 0) minusp)
           (cond ((zerop increment)
                  (unless (zerop high)
                    (if minusp
                        (inst sub rdx high)
                        (inst add rdx high))))
                 (t
                  (when minusp
                    (if (tn-p high)
                        (inst neg high)
                        (setf high (- high))))
                  (inst add rax (if (typep increment '(signed-byte 32))
                                    increment
                                    tmp))
                  (inst adc rdx high)))))
    (cond ((not signedp)
           (aver (typep multiplier 'word))
           (move rax x)
           (load-values)
           (inst mul rax rdx)
           (increment))
          ((typep multiplier 'signed-word)
           (move rax x)
           (load-values)
           (inst imul rdx)
           (increment))
          ((plusp multiplier)
           ;; multiply by (2^w - multiplier) + 2^w
           (aver (tn-p copy-x))
           (move rax x)
           (move copy-x x)
           (load-values (- (ash 1 n-word-bits) multiplier))
           (inst imul rdx)
           (increment copy-x))
          ((minusp multiplier)
           ;; multiply by (multiplier + 2^w) - 2^w
           (aver (tn-p copy-x))
           (move rax x)
           (move copy-x x)
           (load-values (+ multiplier (ash 1 n-word-bits)))
           (inst imul rdx)
           (increment copy-x t)))
    (let ((bit (or tmp copy-x)))
      (when post-increment-p
        (inst mov bit rdx)
        (inst shr bit (1- n-word-bits)))
      (when (plusp shift)
        (if signedp
            (inst sar rdx shift)
            (inst shr rdx shift)))
      (when post-increment-p
        (cond ((location= rdx result)
               (inst add rdx bit))
              (t
               (inst lea result (make-ea :qword :base rdx :index bit))
               (setf rdx result)))))
    (when (plusp tag)
      (inst shl rdx tag))
    (unless (zerop (ash mask (- tag)))
      (inst and rdx (lognot mask)))
    (move result rdx)))

(defmacro with-div-by-mul-constants ((tag mul shift &optional (increment)) &body body)
  `(multiple-value-bind (,mul ,shift ,@(and increment (list increment)))
       (if (sc-is x any-reg)
           (values tagged-a tagged-shift ,@(and increment '(tagged-b)))
           (values a shift ,@(and increment '(b))))
     (let ((,tag (if (sc-is r any-reg) n-fixnum-tag-bits 0)))
       ,@body)))

(define-vop (%truncate-by-mul/unsigned)
  (:translate %truncate-by-mul)
  (:policy :fast-safe)
  (:args (x :scs (unsigned-reg) :target rax))
  (:arg-types unsigned-num
              (:constant unsigned-byte)
              (:constant unsigned-byte)
              (:constant t)
              (:constant t))
  (:results (r :scs (unsigned-reg any-reg)))
  (:result-types (:or unsigned-num positive-fixnum))
  (:info a shift tagged-a tagged-shift)
  (:temporary (:sc unsigned-reg :offset rax-offset :from (:argument 0)) rax)
  (:temporary (:sc unsigned-reg :offset rdx-offset :to (:result 0) :target r) rdx)
  (:generator 10
    (with-div-by-mul-constants (tag mul shift)
      (emit-mul-shift-add-tag r x rax nil
                              mul shift 0 tag t
                              rdx nil nil))))

(define-vop (%truncate-by-mul/positive-fixnum %truncate-by-mul/unsigned)
  (:args (x :scs (any-reg) :target rax))
  (:arg-types positive-fixnum
              (:constant t)
              (:constant t)
              (:constant unsigned-byte)
              (:constant unsigned-byte))
  (:variant-cost 9))

(define-vop (%truncate-by-mul/signed)
  (:translate %truncate-by-mul)
  (:policy :fast-safe)
  (:args (x :scs (signed-reg) :target rax))
  (:arg-types signed-num
              (:constant integer)
              (:constant integer)
              (:constant t)
              (:constant t))
  (:results (r :scs (signed-reg any-reg)))
  (:result-types (:or signed-num tagged-num))
  (:info a shift tagged-a tagged-shift)
  (:temporary (:sc signed-reg :offset rax-offset :from (:argument 0)) rax)
  (:temporary (:sc signed-reg :offset rdx-offset :to (:result 0) :target r) rdx)
  (:temporary (:sc signed-reg) tmp)
  (:generator 11
    (with-div-by-mul-constants (tag mul shift)
      (emit-mul-shift-add-tag r x rax
                              t mul shift 0 tag t
                              rdx nil tmp))))

(define-vop (%truncate-by-mul/fixnum %truncate-by-mul/signed)
  (:args (x :scs (any-reg) :target rax))
  (:arg-types tagged-num
              (:constant t)
              (:constant t)
              (:constant integer)
              (:constant integer))
  (:variant-cost 10))

(define-vop (%floor-by-mul/unsigned)
  (:translate %floor-by-mul)
  (:policy :fast-safe)
  (:args (x :scs (unsigned-reg) :target rax))
  (:arg-types unsigned-num
              (:constant unsigned-byte)
              (:constant unsigned-byte)
              (:constant unsigned-byte)
              (:constant t)
              (:constant t)
              (:constant t))
  (:results (r :scs (unsigned-reg any-reg)))
  (:result-types (:or unsigned-num positive-fixnum))
  (:info a b shift tagged-a tagged-b tagged-shift)
  (:temporary (:sc unsigned-reg :offset rax-offset :from (:argument 0)) rax)
  (:temporary (:sc unsigned-reg :offset rdx-offset :to (:result 0) :target r) rdx)
  (:temporary (:sc unsigned-reg) tmp)
  (:generator 10
    (with-div-by-mul-constants (tag mul shift increment)
      (emit-mul-shift-add-tag r x rax
                              nil mul shift increment tag nil
                              rdx tmp nil))))

(define-vop (%floor-by-mul/positive-fixnum %floor-by-mul/unsigned)
  (:args (x :scs (any-reg) :target rax))
  (:arg-types positive-fixnum
              (:constant t)
              (:constant t)
              (:constant t)
              (:constant unsigned-byte)
              (:constant unsigned-byte)
              (:constant unsigned-byte))
  (:generator 9
    (with-div-by-mul-constants (tag mul shift increment)
      (multiple-value-bind (scale rem) (truncate increment mul)
        (when (and (zerop rem)
                   (<= 0 scale fixnum-tag-mask))
          (if (location= x rax)
              (add rax scale)
              (inst lea rax (make-ea :qword :base x :disp scale)))
          (setf increment 0
                x rax)))
      (emit-mul-shift-add-tag r x rax
                              nil mul shift increment tag nil
                              rdx tmp nil))))

(define-vop (%floor-by-mul/signed)
  (:translate %floor-by-mul)
  (:policy :fast-safe)
  (:args (x :scs (signed-reg) :target rax))
  (:arg-types signed-num
              (:constant unsigned-byte)
              (:constant unsigned-byte)
              (:constant unsigned-byte)
              (:constant (or null unsigned-byte))
              (:constant (or null unsigned-byte))
              (:constant (or null unsigned-byte)))
  (:results (r :scs (signed-reg any-reg)))
  (:result-types (:or signed-num tagged-num))
  (:info a b shift tagged-a tagged-b tagged-shift)
  (:temporary (:sc signed-reg :offset rax-offset :from (:argument 0)) rax)
  (:temporary (:sc signed-reg :offset rdx-offset :to (:result 0) :target r) rdx)
  (:temporary (:sc signed-reg) tmp)
  (:temporary (:sc signed-reg) tmp2)
  (:generator 11
    (with-div-by-mul-constants (tag mul shift increment)
      (emit-mul-shift-add-tag r x rax
                              t mul shift increment tag nil
                              rdx tmp tmp2))))

(define-vop (%floor-by-mul/fixnum %floor-by-mul/signed)
  (:args (x :scs (any-reg) :target rax))
  (:arg-types tagged-num
              (:constant t)
              (:constant t)
              (:constant t)
              (:constant unsigned-byte)
              (:constant unsigned-byte)
              (:constant unsigned-byte))
  (:generator 10
    (with-div-by-mul-constants (tag mul shift increment)
      (multiple-value-bind (scale rem) (truncate increment mul)
        (when (and (zerop rem)
                   (<= 0 scale fixnum-tag-mask))
          (if (location= x rax)
              (add rax scale)
              (inst lea rax (make-ea :qword :base x :disp scale)))
          (setf increment 0
                x rax)))
      (emit-mul-shift-add-tag r x rax
                              t mul shift increment tag nil
                              rdx tmp tmp2))))
