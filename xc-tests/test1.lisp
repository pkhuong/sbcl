;;;
;;; xc-tests/test1.lisp
;;;

(in-package "SB!IMPL")

(defun no-arg-test ()
  (%primitive print "in no-arg-test"))

(defun !cold-init ()
  (%primitive print "initial function start")
  (no-arg-test)
  (rest-key-args-test :foo :bar :baz :quux)
  (%primitive sb!c:halt))

(defun rest-key-args-test (&rest initargs
                           &key (args nil argsp)
                           &allow-other-keys)
  (if argsp
      args
      (apply #'rest-key-args-test-2 initargs)))

(defun rest-key-args-test-2 (a1 a2 a3 a4)
  (when (eq a1 :foo)
    (%primitive print "rkat2: foo is right"))
  (when (eq a2 :bar)
    (%primitive print "rkat2: bar is right"))
  (when (eq a3 :baz)
    (%primitive print "rkat2: baz is right"))
  (when (eq a4 :quux)
    (%primitive print "rkat2: quux is right")))

;;; EOF
