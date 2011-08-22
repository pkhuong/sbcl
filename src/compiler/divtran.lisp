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


;;;; Multiply/shift generator
;;;;
;;;; Computes (x*m)>>s without overflow, for m and s constant
;;;; and x a word.
;;;;
;;;; Returns a cost value, and the expression itself.
;;;; If no generator is available (e.g. s > 2 n-word-bits), returns nil.
;;;; Currently used only to transform TRUNCATE by constants, but can
;;;; probably be reused.
(declaim (inline emit-trivial-mul-shift emit-mulhi-shift emit-slow-mul-shift))
(defun emit-trivial-mul-shift (max mul shift)
  "If everything fits in a word, life's simple"
  (when (and (typep mul 'word)
             #-sb-xc-host
             (zerop (sb!kernel:%multiply-high max mul))
             #+sb-xc-host
             (typep (* max mul) 'word))
    (list 1 `(ash (* x ,mul) ,(- shift)))))

(defun emit-mulhi-shift (max mul shift)
  "When shift >= word-size, and multiplier is a word,
 we can use a multiply-high."
  (cond ((< shift sb!vm:n-word-bits) nil)
        ((typep mul 'word)
         (list 2
               (if (= shift sb!vm:n-word-bits)
                   `(truly-the (integer 0 ,#+sb-xc-host (ash (* max mul) (- shift))
                                           #-sb-xc-host (sb!kernel:%multiply-high max mul))
                               (sb!kernel:%multiply-high x ,mul))
                   `(ash (sb!kernel:%multiply-high x ,mul)
                         ,(- sb!vm:n-word-bits shift)))))
        ((<= (integer-length mul) (1+ sb!vm:n-word-bits))
         (list 3
               (let* ((mullo (ldb (byte sb!vm:n-word-bits 0) mul))
                      (result #+sb-xc-host (ash (* max mul) (- shift))
                              #-sb-xc-host (ash (+ max (sb!kernel:%multiply-high max mullo))
                                                (- shift sb!vm:n-word-bits))))
                 `(let ((high (sb!kernel:%multiply-high x ,mullo)))
                    ,(if (= shift sb!vm:n-word-bits)
                         `(truly-the (integer 0 ,result)
                                     (+ x (truly-the (integer 0
                                                              ,#-sb-xc-host (sb!kernel:%multiply-high max mullo)
                                                              #+sb-xc-host (ash (* max mullo) (- sb!vm:n-word-bits)))
                                                     high)))
                         `(ash (truly-the word (+ high (ash (truly-the word (- x high)) -1)))
                               ,(- 1 (- shift sb!vm:n-word-bits))))))))))

(defun emit-slow-mul-shift (max mul shift)
  "If we can let shift = 2*word-size, and mul fit in a double word as well,
emit this sequence."
  (let ((remaining-shift (- (* 2 sb!vm:n-word-bits) shift)))
    (when (<= (+ remaining-shift (integer-length max))
              sb!vm:n-word-bits)
      (list 6
            (let ((mulh (ash mul (- sb!vm:n-word-bits)))
                  (mull (ldb (byte sb!vm:n-word-bits 0) mul)))
              `(let* ((x   (ash x ,remaining-shift))
                      (low (sb!kernel:%multiply-high x ,mull)))
                 (values (sb!bignum:%multiply-and-add x ,mulh low))))))))

(defun maybe-emit-mul-shift (max mul shift &optional (errorp nil))
  "Sequentially try more expensive generators until one applies."
  (declare (type word max)
           (type unsigned-byte mul)
           (type (integer 0 #.(* 2 sb!vm:n-word-bits)) shift))
  (macrolet ((try (value)
               ` (let ((value ,value))
                   (when value
                     (return-from maybe-emit-mul-shift value)))))
    ;; are we lucky?
    (try (emit-trivial-mul-shift max mul shift))
    ;; try and increase shift to at least n-word-bits by only
    ;; scaling the multiplier
    (when (< shift sb!vm:n-word-bits)
      (let ((len (min (- sb!vm:n-word-bits (integer-length mul))
                      (- sb!vm:n-word-bits shift))))
        (when (> len 0)
          (setf mul    (ash mul len)
                shift  (+ shift len)))))
    (try (emit-mulhi-shift max mul shift))
    ;; again, increase shift, but frob the argument as well
    (let ((max     (- sb!vm:n-word-bits (integer-length max)))
          (unshift (- sb!vm:n-word-bits shift)))
      (when (<= unshift max)
        (let ((sequence (emit-mulhi-shift max mul (+ shift unshift))))
          (try (and sequence
                    (list (+ 2 (first sequence))
                          `(let ((x (ash x ,unshift)))
                             ,(second sequence))))))))
    ;; final case: get the shift amount to exactly 2*n-word-bits,
    ;; and emit the general case.
    (let ((reshift (min (- (* 2 sb!vm:n-word-bits) shift)
                        (- (* 2 sb!vm:n-word-bits) (integer-length mul)))))
      (when (plusp reshift)
        (setf shift (+ shift reshift)
              mul   (ash mul reshift))))
    (try (emit-slow-mul-shift max mul shift))
    (when errorp
      (error "Unable to emit multiply/shift sequence for (~S ~A ~A ~A)"
             'maybe-emit-mul-shift max mul shift))))

;;;; Truncate generator
;;;;
;;;; We usually use the over-approximation scheme, as it's very easy to
;;;; find good constants (see function below).
;;;;
;;;; However, when dividing by a constant (e.g. multiplying by 1/d), and
;;;; when X can be safely incremented by one, we try to use the under-
;;;; approximation scheme as well.
(declaim (ftype (function (word word word)
                          (values unsigned-byte (integer 0 #. (* 2 sb!vm:n-word-bits))
                                  &optional))
                find-mul-div-constants))
(defun find-over-approximation-constants (n m d)
  "Find the smallest constant mul and shift value s such that
 [x*mul/2^s] = [x*m/d], for all x <= n"
  (declare (type word n m d))
  (let* ((max-shift (* 2 sb!vm:n-word-bits))
         (low       (truncate (ash m max-shift) d))
         (high      (truncate (+ (ash m max-shift)
                                 ;; could under-approximate with a power of two
                                 (1- (ceiling (ash 1 max-shift) n)))
                              d))
         (max-unshift (1- (integer-length (logxor low high))))
         (min-shift (- max-shift max-unshift)))
    (values (ash high (- max-unshift))
            min-shift)))

(declaim (inline find-under-approximation-constants))
(defun find-under-approximation-constants (n d)
  "Work in the under-approximatiom scheme: [x/d] = [(x+d)*mul/2^s]."
  (declare (type word n d))
  (when (>= n (1- (ash 1 sb!vm:n-word-bits)))
    (return-from find-under-approximation-constants nil))
  (let* ((shift (+ sb!vm:n-word-bits (1- (integer-length d))))
         (approx (truncate (ash 1 shift) d))
         (round  (round (ash 1 shift) d)))
    (assert (typep shift 'word))
    (when (= approx round)
      (values approx shift))))

(defun find-under-approximation-emitter (n d)
  (declare (type word n d))
  (multiple-value-bind (mul shift) (find-under-approximation-constants n d)
    (and mul shift
         (if (= shift sb!vm:n-word-bits)
             `(truly-the (integer 0 ,(truncate n d))
                         (sb!kernel:%multiply-high (1+ x) ,mul))
             `(ash (sb!kernel:%multiply-high (1+ x) ,mul)
                   ,(- sb!vm:n-word-bits shift))))))

(defun emit-truncate-sequence-1 (max-n d)
  "Generate code for a truncated division.
First, check for powers of two (:
Then, go for the straightforward over-approximation sequence
when it's cheap enough (an in-word multiply/shift or a multiply-high).
Otherwise, try to exploit an under-approximation, or to mask away
low bits.
When all of these fail, go for the generic over-approximation."
  (declare (type word max-n d))
  (when (zerop (logand d (1- d)))
    `(ash x ,(- (integer-length (1- d)))))
  (let ((vanilla (multiple-value-call #'maybe-emit-mul-shift max-n
                   (find-over-approximation-constants max-n 1 d) t))
        (gcd     (1- (integer-length (logand d (- d))))))
    (cond ((<= (first vanilla) 2)
           (second vanilla))
          ((find-under-approximation-emitter max-n d))
          ((plusp gcd)
           (let ((mask (1- (ash 1 gcd))))
             `(let ((x (logandc2 x ,mask)))
                ,(second (multiple-value-call #'maybe-emit-mul-shift
                           (logandc2 max-n mask)
                           (multiple-value-bind (mul shift)
                               (find-over-approximation-constants (ash max-n (- gcd))
                                                                  1 (ash d (- gcd)))
                             (values mul (+ shift gcd)))
                           t)))))
          (t
           (second vanilla)))))

(defun emit-truncate-sequence-2 (max-n m d)
  "Generate code for a truncated multiplication by a fraction < 1.
Go for the generic over-approximation scheme, except when we hit the full
2-word code sequence.
In that case, try to simplify the truncation by factorising the multiplier
in a simply \"perfect\" multiply-high sequence and a division."
  (declare (type word max-n m d))
  (assert (< m d))
  (let* ((vanilla (multiple-value-call #'maybe-emit-mul-shift max-n
                    (find-over-approximation-constants max-n m d) t))
         (gcd     (min (1- (integer-length (logand d (- d))))
                       (- sb!vm:n-word-bits (integer-length m))))
         (preshift (- sb!vm:n-word-bits gcd))
         (temp    (ash (* m max-n) (- gcd))))
    (if (or (< (first vanilla) 6)
            (zerop gcd)
            (> (+ (integer-length m) preshift) sb!vm:n-word-bits)
            (plusp #-sb-xc-host (ash (sb!kernel:%multiply-high m max-n) (- gcd))
                   #+sb-xc-host (ash (* m max-n) (- (+ gcd sb!vm:n-word-bits)))))
        (second vanilla)
        `(let ((x (sb!kernel:%multiply-high x ,(ash m preshift))))
           ,(emit-truncate-sequence-1 temp (ash d (- gcd)))))))

(defun emit-truncate-sequence-3 (max-n m d)
  "Generate code for a truncated multiplication by a fraction > 1.
Go for the generic over-approximation if possible. Otherwise, split
the fraction in its integral and fractional parts, and emit a truncated
multiplication by a fraction < 1."
  (declare (type word max-n m d))
  (or (multiple-value-call #'maybe-emit-mul-shift max-n
        (find-over-approximation-constants max-n m d))
      (multiple-value-bind (q r) (truncate m d)
        `(+ (* x ,q)
            ,(if (= r 1)
                 (emit-truncate-sequence-1 max-n d)
                 (emit-truncate-sequence-2 max-n r d))))))

(defun emit-truncate-sequence (max-n m d)
  (declare (type word max-n m d))
  (cond ((= 1 d)
         `(* x ,m))
        ((= 1 m)
         (emit-truncate-sequence-1 max-n d))
        ((< m d)
         (emit-truncate-sequence-2 max-n m d))
        (t
         (emit-truncate-sequence-3 max-n m d))))

;;; If the divisor is constant and both args are positive and fit in a
;;; machine word, replace the division by a multiplication and possibly
;;; some shifts and an addition.  The transform is generalized for fractions
;;; when both the numerator and denominator are word-sized.
;;;
;;; Calculate the remainder by a second multiplication and a subtraction.
;;; Dead code elimination will suppress the latter part if only the quotient
;;; is needed.
(deftransform truncate ((x y) (word (constant-arg (rational (0))))
                        *
                        :policy (and (> speed compilation-speed)
                                     (> speed space)))
  "convert truncated division by rationals to multiplication"
  (let* ((y      (lvar-value y))
         (m      (denominator y))
         (d      (numerator y))
         (x-type (lvar-type x))
         (max-x  (or (and (numeric-type-p x-type)
                          (numeric-type-high x-type))
                     most-positive-word)))
    ;; Division by zero, one or powers of two is handled elsewhere.
    (when (or (and (integerp y)
                   (zerop (logand y (1- y))))
              (not (typep m 'word))
              (not (typep d 'word)))
      (give-up-ir1-transform))
    `(let* ((quot (truly-the (integer 0 ,(truncate max-x y))
                             ,(emit-truncate-sequence max-x m d)))
            (rem  (truly-the (rational 0 (,y))
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
