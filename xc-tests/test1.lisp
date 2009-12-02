;;;
;;; xc-tests/test1.lisp
;;;

(in-package "SB!IMPL")

(defun no-arg-test ()
  (%primitive print "in no-arg-test"))

(defun !cold-init ()
  (%primitive print "initial function start")
  (no-arg-test)
  (%primitive sb!c:halt))

;;; EOF
