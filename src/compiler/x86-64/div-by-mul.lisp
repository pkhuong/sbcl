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

(defun emit-mul-shift-add-tag (result x rax signed-p
                               multiplier shift increment tag
                               rdx tmp copy-x
                               &aux (mask (ldb (byte tag 0) -1)))
  "result <- [(x * multiplier + increment) >> (shift + n-w-b)] << tag

   tmp: only used if increment is large and non-zero
   copy-x: only used for signed multiplication by > signed-word constants"
  (declare (type tn result x rax)
           (type boolean signed-p)
           (type (or word signed-word) multiplier)
           (type word increment)
           (type (mod #.n-word-bits) shift tag)
           (type tn rdx)
           (type (or tn null) tmp copy-x))
  (aver (location= rax rax-tn))
  (aver (location= rdx rdx-tn))
  (let ((delta (min shift tag)))
    (decf shift delta)
    (decf tag delta))
  (when (and (typep (ash multiplier tag) `(signed-byte ,(1+ n-word-bits)))
             (typep (ash increment tag) `(signed-byte ,(1+ n-word-bits))))
    (setf multiplier (ash multiplier tag)
          increment  (ash increment tag)
          tag        0))
  (flet ((load-values (&optional (multiplier multiplier))
           (inst mov rdx-tn multiplier)
           (cond ((typep increment '(signed-byte 32)))
                 ((= multiplier increment)
                  (aver (tn-p tmp))
                  (inst mov tmp rdx-tn))
                 (t
                  (aver (tn-p tmp))
                  (inst mov tmp increment))))
         (increment (&optional (high 0) minusp)
           (cond ((zerop increment)
                  (unless (zerop high)
                    (if minusp
                        (inst sub rax-tn high)
                        (inst add rax-tn high))))
                 (t
                  (when minusp
                    (if (tn-p high)
                        (inst neg high)
                        (setf high (- high))))
                  (inst add rdx-tn (if (typep increment '(signed-byte 32))
                                       increment
                                       tmp))
                  (inst adc rax-tn high)))))
    (cond ((not signed-p)
           (aver (typep multiplier 'word))
           (move rax x)
           (load-values)
           (inst mul rax-tn rdx-tn)
           (increment))
          ((typep multiplier 'signed-word)
           (move rax x)
           (load-values)
           (inst imul rdx-tn)
           (increment))
          ((plusp multiplier)
           ;; multiply by (2^w - multiplier) + 2^w
           (aver (tn-p copy-x))
           (move rax x)
           (move copy-x x)
           (load-values (- (ash 1 n-word-bits) multiplier))
           (inst imul rdx-tn)
           (increment copy-x))
          ((minusp multiplier)
           ;; multiply by (multiplier + 2^w) - 2^w
           (aver (tn-p copy-x))
           (move rax x)
           (move copy-x x)
           (load-values (+ multiplier (ash 1 n-word-bits)))
           (inst imul rdx-tn)
           (increment copy-x t)))
    (when (plusp shift)
      (if signed-p
          (inst sar rdx-tn shift)
          (inst shr rdx-tn shift)))
    (when (plusp tag)
      (inst shl rdx-tn tag))
    (unless (zerop (ash mask (- tag)))
      (inst and rdx-tn (lognot mask)))
    (move result rdx-tn)))

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
                              mul shift 0 tag
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
                              t mul shift 0 tag
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
                              nil mul shift increment tag
                              rdx nil tmp))))

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
      (when (= mul increment)
        (if (location= x rax)
            (add rax 1)
            (inst lea rax (make-ea :qword :base x :disp 1)))
        (setf increment 0
              x rax))
      (emit-mul-shift-add-tag r x rax
                              nil mul shift increment tag
                              rdx nil tmp))))

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
                              t mul shift increment tag
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
      (when (= mul increment)
        (if (location= x rax)
            (add rax 1)
            (inst lea rax (make-ea :qword :base x :disp 1)))
        (setf increment 0
              x rax))
      (emit-mul-shift-add-tag r x rax
                              t mul shift increment tag
                              rdx tmp tmp2))))
