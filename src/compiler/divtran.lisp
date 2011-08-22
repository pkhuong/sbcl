;;;; Optimizations for integer division operations.
;;;; Some type-related functionality is in srctran.lisp

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!C")
;;; Note that all the integer division functions are available for
;;; inline expansion.

(macrolet ((deffrob (fun)
             `(define-source-transform ,fun (x &optional (y nil y-p))
                (declare (ignore y))
                (if y-p
                    (values nil t)
                    `(,',fun ,x 1)))))
  (deffrob truncate)
  (deffrob round)
  #-sb-xc-host ; (See CROSS-FLOAT-INFINITY-KLUDGE.)
  (deffrob floor)
  #-sb-xc-host ; (See CROSS-FLOAT-INFINITY-KLUDGE.)
  (deffrob ceiling))

;;; These must come before the ones below, so that they are tried
;;; first. Since %FLOOR and %CEILING are inlined, this allows
;;; the general case to be handled by TRUNCATE transforms.
(deftransform floor ((x y))
  `(%floor x y))

(deftransform ceiling ((x y))
  `(%ceiling x y))


;;; Operations with powers of two are converted to shift and mask.
;;; If arg is a constant power of two, turn FLOOR into a shift and
;;; mask. If CEILING, add in (1- (ABS Y)), do FLOOR and correct a
;;; remainder.
(flet ((frob (y ceil-p)
         (unless (constant-lvar-p y)
           (give-up-ir1-transform))
         (let* ((y (lvar-value y))
                (y-abs (abs y))
                (len (1- (integer-length y-abs))))
           (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
             (give-up-ir1-transform))
           (let ((shift (- len))
                 (mask (1- y-abs))
                 (delta (if ceil-p (* (signum y) (1- y-abs)) 0)))
             `(let ((x (+ x ,delta)))
                ,(if (minusp y)
                     `(values (ash (- x) ,shift)
                              (- (- (logand (- x) ,mask)) ,delta))
                     `(values (ash x ,shift)
                              (- (logand x ,mask) ,delta))))))))
  (deftransform floor ((x y) (integer integer) *)
    "convert division by 2^k to shift"
    (frob y nil))
  (deftransform ceiling ((x y) (integer integer) *)
    "convert division by 2^k to shift"
    (frob y t)))

;;; Do the same for MOD.
(deftransform mod ((x y) (integer integer) *)
  "convert remainder mod 2^k to LOGAND"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let ((mask (1- y-abs)))
      (if (minusp y)
          `(- (logand (- x) ,mask))
          `(logand x ,mask)))))

;;; If arg is a constant power of two, turn TRUNCATE into a shift and mask.
(deftransform truncate ((x y) (integer integer))
  "convert division by 2^k to shift"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let* ((shift (- len))
           (mask (1- y-abs)))
      `(if (minusp x)
           (values ,(if (minusp y)
                        `(ash (- x) ,shift)
                        `(- (ash (- x) ,shift)))
                   (- (logand (- x) ,mask)))
           (values ,(if (minusp y)
                        `(ash (- ,mask x) ,shift)
                        `(ash x ,shift))
                   (logand x ,mask))))))

;;; And the same for REM.
(deftransform rem ((x y) (integer integer) *)
  "convert remainder mod 2^k to LOGAND"
  (unless (constant-lvar-p y)
    (give-up-ir1-transform))
  (let* ((y (lvar-value y))
         (y-abs (abs y))
         (len (1- (integer-length y-abs))))
    (unless (and (> y-abs 0) (= y-abs (ash 1 len)))
      (give-up-ir1-transform))
    (let ((mask (1- y-abs)))
      `(if (minusp x)
           (- (logand (- x) ,mask))
           (logand x ,mask)))))


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
(deftransform truncate ((x y) (word (constant-arg word))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert integer division to multiplication"
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


;;; KLUDGE: Shouldn't (/ 0.0 0.0), etc. cause exceptions in these
;;; transformations?
;;; Perhaps we should have to prove that the denominator is nonzero before
;;; doing them?  -- WHN 19990917
(macrolet ((def (name)
             `(deftransform ,name ((x y) ((constant-arg (integer 0 0)) integer)
                                   *)
                "fold zero arg"
                0)))
  (def ash)
  (def /))

(macrolet ((def (name)
             `(deftransform ,name ((x y) ((constant-arg (integer 0 0)) integer)
                                   *)
                "fold zero arg"
                '(values 0 0))))
  (def truncate)
  (def round)
  (def floor)
  (def ceiling))
