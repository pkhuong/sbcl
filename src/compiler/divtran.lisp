;;;; This file contains code to (rounded) strnegth-reduce division by
;;;; constants.

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!C")

;;;; Convert division by constant floats into multiplication by a
;;;; reciprocal when exact.

;;; Return the reciprocal of X if it can be represented exactly, NIL otherwise.
(defun maybe-exact-reciprocal (x)
  (unless (zerop x)
    (handler-case
        (multiple-value-bind (significand exponent sign)
            (integer-decode-float x)
          ;; only powers of 2 can be inverted exactly
          (unless (zerop (logand significand (1- significand)))
            (return-from maybe-exact-reciprocal nil))
          (let ((expected   (/ sign significand (expt 2 exponent)))
                (reciprocal (/ x)))
            (multiple-value-bind (significand exponent sign)
                (integer-decode-float reciprocal)
              ;; Denorms can't be inverted safely.
              (and (eql expected (* sign significand (expt 2 exponent)))
                   reciprocal))))
      (error () (return-from maybe-exact-reciprocal nil)))))

;;;; Generic truncate-by-mul code-path

;;; Replace constant division by multiplication with exact reciprocal,
;;; if one exists.
(macrolet ((def (type)
             `(deftransform / ((x y) (,type (constant-arg ,type)) *
                               :node node)
                "convert to multiplication by reciprocal"
                (let ((n (lvar-value y)))
                  (if (policy node (zerop float-accuracy))
                      `(* x ,(/ n))
                      (let ((r (maybe-exact-reciprocal n)))
                        (if r
                            `(* x ,r)
                            (give-up-ir1-transform
                             "~S does not have an exact reciprocal"
                             n))))))))
  (def single-float)
  (def double-float))

;;; Return an expression to calculate the integer quotient of X and
;;; constant Y, using multiplication, shift and add/sub instead of
;;; division. Both arguments must be unsigned, fit in a machine word and
;;; Y must neither be zero nor a power of two. The quotient is rounded
;;; towards zero.
;;; The algorithm is taken from the paper "Division by Invariant
;;; Integers using Multiplication", 1994 by Torbj\"{o}rn Granlund and
;;; Peter L. Montgomery, Figures 4.2 and 6.2, modified to exclude the
;;; case of division by powers of two.
;;; The algorithm includes an adaptive precision argument.  Use it, since
;;; we often have sub-word value ranges.  Careful, in this case, we need
;;; p s.t 2^p > n, not the ceiling of the binary log.
;;; Also, for some reason, the paper prefers shifting to masking.  Mask
;;; instead.  Masking is equivalent to shifting right, then left again;
;;; all the intermediate values are still words, so we just have to shift
;;; right a bit more to compensate, at the end.
;;;
;;; The following two examples show an average case and the worst case
;;; with respect to the complexity of the generated expression, under
;;; a word size of 64 bits:
;;;
;;; (UNSIGNED-DIV-TRANSFORMER 10 MOST-POSITIVE-WORD) ->
;;; (ASH (%MULTIPLY (LOGANDC2 X 0) 14757395258967641293) -3)
;;;
;;; (UNSIGNED-DIV-TRANSFORMER 7 MOST-POSITIVE-WORD) ->
;;; (LET* ((NUM X)
;;;        (T1 (%MULTIPLY NUM 2635249153387078803)))
;;;   (ASH (LDB (BYTE 64 0)
;;;             (+ T1 (ASH (LDB (BYTE 64 0)
;;;                             (- NUM T1))
;;;                        -1)))
;;;        -2))
;;;
#!-div-by-mul-vops
(defun gen-unsigned-div-by-constant-expr (y max-x)
  (declare (type (integer 3 #.most-positive-word) y)
           (type word max-x))
  (aver (not (zerop (logand y (1- y)))))
  (labels ((ld (x)
             ;; the floor of the binary logarithm of (positive) X
             (integer-length (1- x)))
           (choose-multiplier (y precision)
             (do* ((l (ld y))
                   (shift l (1- shift))
                   (expt-2-n+l (expt 2 (+ sb!vm:n-word-bits l)))
                   (m-low (truncate expt-2-n+l y) (ash m-low -1))
                   (m-high (truncate (+ expt-2-n+l
                                        (ash expt-2-n+l (- precision)))
                                     y)
                           (ash m-high -1)))
                  ((not (and (< (ash m-low -1) (ash m-high -1))
                             (> shift 0)))
                   (values m-high shift)))))
    (let ((n (expt 2 sb!vm:n-word-bits))
          (precision (integer-length max-x))
          (shift1 0))
      (multiple-value-bind (m shift2)
          (choose-multiplier y precision)
        (when (and (>= m n) (evenp y))
          (setq shift1 (ld (logand y (- y))))
          (multiple-value-setq (m shift2)
            (choose-multiplier (/ y (ash 1 shift1))
                               (- precision shift1))))
        (cond ((>= m n)
               (flet ((word (x)
                        `(truly-the word ,x)))
                 `(let* ((num x)
                         (t1 (%multiply-high num ,(- m n))))
                    (ash ,(word `(+ t1 (ash ,(word `(- num t1))
                                            -1)))
                         ,(- 1 shift2)))))
              ((and (zerop shift1) (zerop shift2))
               (let ((max (truncate max-x y)))
                 ;; Explicit TRULY-THE needed to get the FIXNUM=>FIXNUM
                 ;; VOP.
                 `(truly-the (integer 0 ,max)
                             (%multiply-high x ,m))))
              (t
               `(ash (%multiply-high (logandc2 x ,(1- (ash 1 shift1))) ,m)
                     ,(- (+ shift1 shift2)))))))))

;;; If the divisor is constant and both args are positive and fit in a
;;; machine word, replace the division by a multiplication and possibly
;;; some shifts and an addition. Calculate the remainder by a second
;;; multiplication and a subtraction. Dead code elimination will
;;; suppress the latter part if only the quotient is needed. If the type
;;; of the dividend allows to derive that the quotient will always have
;;; the same value, emit much simpler code to handle that. (This case
;;; may be rare but it's easy to detect and the compiler doesn't find
;;; this optimization on its own.)
#!-div-by-mul-vops
(progn
  (defun transform-positive-truncate (x y)
    (let* ((y      (lvar-value y))
           (x-type (lvar-type x))
           (max-x  (or (and (numeric-type-p x-type)
                            (numeric-type-high x-type))
                       most-positive-word)))
      ;; Division by zero, one or powers of two is handled elsewhere.
      (when (zerop (logand y (1- y)))
        (give-up-ir1-transform))
      `(let* ((quot ,(gen-unsigned-div-by-constant-expr y max-x))
              (rem (ldb (byte #.sb!vm:n-word-bits 0)
                        (- x (* quot ,y)))))
         (values quot rem))))

  (deftransform truncate ((x y) (word (constant-arg word))
                          *
                          :policy (and (> speed compilation-speed)
                                       (> speed space)))
    "convert integer division to multiplication"
    (transform-positive-truncate x y))

  (deftransform floor ((x y) (word (constant-arg word))
                       *
                       :policy (and (> speed compilation-speed)
                                    (> speed space)))
    "convert integer division to multiplication"
    (transform-positive-truncate x y)))


;;;; Exploit specialised div-by-mul VOPs

;;; These should only be called from the compiler (constant folding)
#!+div-by-mul-vops
(defun %truncate-by-mul (x a shift tagged-a tagged-shift)
  (declare (ignore tagged-a tagged-shift))
  (ash (* x a)
       (- (+ shift sb!vm:n-word-bits))))

#!+div-by-mul-vops
(defun %floor-by-mul (x a b shift tagged-a tagged-b tagged-shift)
  (declare (ignore tagged-a tagged-b tagged-shift))
  (ash (+ (* x a) b)
       (- (+ shift sb!vm:n-word-bits))))

;;; Support code to determine whether an approximation is exact over
;;; a given range, and to find a practically optimal one if possible.

;;; First, truncate, with [x/d] approximated by [ax/2^k] + (1 if result is -ve)
#!+div-by-mul-vops
(progn
  (defun truncate-approximation-ok-p (divisor
                                      multiplier shift
                                      input-magnitude
                                      tag-bits)
    (declare (type integer divisor multiplier)
             (type unsigned-byte shift input-magnitude tag-bits))
    (let* ((reciprocal (/ divisor))
           (approximation (/ multiplier (ash 1 shift))))
      (aver (>= (abs approximation) (abs reciprocal)))
      (aver (= (signum divisor) (signum multiplier)))
      (let ((error (abs (- approximation reciprocal))))
        (< (* error input-magnitude) (* (abs reciprocal) (ash 1 tag-bits))))))

  (defun maybe-truncate-approximation (divisor shift input-magnitude tag-bits)
    (let ((multiplier (* (ceiling (ash 1 shift) (abs divisor))
                         (signum divisor))))
      (and (truncate-approximation-ok-p divisor
                                        multiplier shift
                                        input-magnitude tag-bits)
           multiplier)))

  (defun truncate-approximation (divisor input-magnitude tag-bits)
    (flet ((probe (delta-shift)
             (let ((multiplier
                     (maybe-truncate-approximation divisor (+ sb!vm:n-word-bits
                                                              delta-shift)
                                                   input-magnitude tag-bits)))
               (when multiplier
                 (aver (typep multiplier '(or word sb!vm:signed-word)))
                 (return-from truncate-approximation
                   (values multiplier delta-shift))))))
      (probe 0)
      (probe (- (integer-length (1- divisor))
                2))
      (probe (1- (integer-length (1- divisor))))))

  (defun %truncate-form (x divisor input-magnitude)
    (multiple-value-bind (multiplier shift)
        (truncate-approximation divisor input-magnitude 0)
      (multiple-value-bind (tagged-multiplier tagged-shift)
          (truncate-approximation (ash divisor sb!vm:n-fixnum-tag-bits)
                                  (ash input-magnitude sb!vm:n-fixnum-tag-bits)
                                  sb!vm:n-fixnum-tag-bits)
        (and multiplier shift
             `(%truncate-by-mul ,x
                                ,multiplier ,shift
                                ,tagged-multiplier ,tagged-shift))))))

;;; Second, floor, with [x/d] approximated with [(ax+b)/2^k]
#!+div-by-mul-vops
(progn
  (defun floor-approximation-ok-p (divisor
                                   multiplier shift
                                   input-magnitude
                                   tag-bits)
    (declare (type integer divisor multiplier)
             (type unsigned-byte shift input-magnitude tag-bits))
    (let* ((reciprocal (/ divisor))
           (approximation (/ multiplier (ash 1 shift))))
      (aver (<= approximation reciprocal))
      (aver (= (signum divisor) (signum multiplier)))
      (let ((error (* (abs (- approximation reciprocal)) input-magnitude))
            (max-error (abs reciprocal)))
        (cond ((< error (* max-error (1- (ash 1 tag-bits))))
               :quick)
              ((< error (* max-error (ash 1 tag-bits)))
               :slow)))))

  (defun maybe-floor-approximation (divisor shift input-magnitude tag-bits)
    (let* ((multiplier (floor (ash 1 shift) divisor))
           (ok (floor-approximation-ok-p divisor
                                         multiplier shift
                                         input-magnitude tag-bits)))
      (and ok (values multiplier (ecase ok
                                   (:quick (* (abs multiplier)
                                              (1- (ash 1 tag-bits))))
                                   (:slow (ash (abs multiplier) tag-bits)))))))

  (defun floor-approximation (divisor input-magnitude tag-bits)
    (flet ((probe (delta-shift)
             (multiple-value-bind (multiplier increment)
                 (maybe-floor-approximation divisor (+ sb!vm:n-word-bits
                                                       delta-shift)
                                            input-magnitude tag-bits)
               (when multiplier
                 (aver (typep multiplier '(or word sb!vm:signed-word)))
                 (aver (typep increment 'word))
                 (return-from floor-approximation
                   (values multiplier increment delta-shift))))))
      (probe 0)
      (probe (- (integer-length (1- divisor))
                2))
      (probe (1- (integer-length (1- divisor))))))

  (defun %floor-form (x divisor input-magnitude)
    (multiple-value-bind (multiplier increment shift)
        (floor-approximation divisor input-magnitude 0)
      (multiple-value-bind (tagged-multiplier tagged-increment tagged-shift)
          (floor-approximation (ash divisor sb!vm:n-fixnum-tag-bits)
                               (ash input-magnitude sb!vm:n-fixnum-tag-bits)
                               sb!vm:n-fixnum-tag-bits)
        (and multiplier shift increment
             `(%floor-by-mul
               ,x
               ,multiplier ,increment ,shift
               ,tagged-multiplier ,tagged-increment ,tagged-shift))))))

;;; Call these generators
#!+div-by-mul-vops
(deftransform truncate ((x y)
                        (sb!vm:signed-word (constant-arg sb!vm:signed-word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (>= speed space)))
  "convert integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     (truncate most-positive-word 2)))
         (min-x  (or (and (numeric-type-p x-type)
                          (numeric-type-low x-type))
                     (- (1+ (truncate most-positive-word 2)))))
         (magnitude-x (max max-x (- min-x)))
         (min-result (truncate min-x y))
         (max-result (truncate max-x y)))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand y (1- y)))
      (give-up-ir1-transform))
    `(let* ((quot ,(if (= min-result max-result)
                       min-result
                       `(truly-the (integer ,min-result ,max-result)
                                   ,(or (%truncate-form 'x y magnitude-x)
                                        (give-up-ir1-transform)))))
            (rem (mask-signed-field ,sb!vm:n-word-bits
                                    (- x (* quot ,y)))))
       (values quot rem))))

#!+div-by-mul-vops
(deftransform floor ((x y)
                     (sb!vm:signed-word (constant-arg sb!vm:signed-word))
                     *
                     :policy (and (> speed compilation-speed)
                                  (>= speed space)))
  "convert integer division to multiplication"
  (let* ((y      (lvar-value y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     (truncate most-positive-word 2)))
         (min-x  (or (and (numeric-type-p x-type)
                          (numeric-type-low x-type))
                     (- (1+ (truncate most-positive-word 2)))))
         (magnitude-x (max max-x (- min-x)))
         (min-result (floor min-x y))
         (max-result (floor max-x y)))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (zerop (logand y (1- y)))
      (give-up-ir1-transform))
    `(let* ((quot ,(if (= min-result max-result)
                       min-result
                       `(truly-the (integer ,(floor min-x y) ,(floor max-x y))
                                   ,(or (%floor-form 'x y magnitude-x)
                                        (give-up-ir1-transform)))))
            (rem (mask-signed-field ,sb!vm:n-word-bits
                                    (- x (* quot ,y)))))
       (values quot rem))))

;;; Positive-only truncate/floor are easiest. Define these transforms last so
;;; they fire first.  The trick is that they are equivalent, so we can always
;;; use TRUNCATE if possible (quicker), and FLOOR otherwise (better than
;;; the classic TRUNCATE slow-path).
#!+div-by-mul-vops
(progn
  (defun transform-positive-truncate (x y)
    (let* ((y      (lvar-value y))
           (x-type (lvar-type x))
           (max-x  (or (and (numeric-type-p x-type)
                            (numeric-type-high x-type))
                       most-positive-word))
           (max-result (truncate max-x y)))
      ;; Division by zero, one or powers of two is handled elsewhere.
      (when (zerop (logand y (1- y)))
        (give-up-ir1-transform))
      `(let* ((quot ,(if (zerop max-result)
                         0
                         `(truly-the (integer 0 ,max-result)
                                     ,(or (%truncate-form 'x y max-x)
                                          (%floor-form 'x y max-x)
                                          (give-up-ir1-transform)))))
              (rem (ldb (byte #.sb!vm:n-word-bits 0)
                        (- x (* quot ,y)))))
         (values quot rem))))

  (deftransform truncate ((x y) (word (constant-arg word))
                          *
                          :policy (and (> speed compilation-speed)
                                       (>= speed space)))
    "convert integer division to multiplication"
    (transform-positive-truncate x y))

  (deftransform truncate ((x y) (word (constant-arg (and sb!vm:signed-word (not word))))
                          *
                          :policy (and (> speed compilation-speed)
                                       (>= speed space)))
    "Flip sign of word/negative-signed-word truncate"
    `(- (truncate x ,(- (lvar-value y)))))

  (deftransform floor ((x y) (word (constant-arg word))
                       *
                       :policy (and (> speed compilation-speed)
                                    (>= speed space)))
    "convert integer division to multiplication"
    (transform-positive-truncate x y)))