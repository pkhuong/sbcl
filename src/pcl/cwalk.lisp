;;;; Composable code walking

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.

;;;; This software is in the public domain and is provided with
;;;; absolutely no warranty. See the COPYING and CREDITS files for
;;;; more information.

(in-package "SB-IMPL")

(fmakunbound 'sb-cwalk:macro)
(defgeneric sb-cwalk:macro (hook form lexenv))

(fmakunbound 'sb-cwalk:code)
(defgeneric sb-cwalk:code (hook reason form lexenv))

(defvar sb-cwalk:*current-code-hook* nil)

(defvar sb-cwalk:*current-macro-hook* nil)

(defvar sb-cwalk:*parent-lexenv* nil)

(defun sb-cwalk:wrap (form &key
                             (code-hook sb-cwalk:*current-code-hook*)
                             (macro-hook sb-cwalk:*current-macro-hook*)
                             (lexenv sb-cwalk:*parent-lexenv*))
  (sb-cwalk:make-wrapper form
                         :codewalking-hooks (if (listp code-hook)
                                                code-hook
                                                (list code-hook))
                         :premacro-hooks (if (listp macro-hook)
                                             macro-hook
                                             (list macro-hook))
                         :lexenv lexenv))

(defclass sb-cwalk:macro (standard-object)
  ())

(defmethod sb-cwalk:macro :around ((hook sb-cwalk:macro) form lexenv)
  (declare (ignore form lexenv))
  (let ((sb-cwalk:*current-code-hook* nil)
        (sb-cwalk:*current-macro-hook* hook)
        (sb-cwalk:*parent-lexenv* nil))
    (call-next-method)))

(defclass sb-cwalk:code (standard-object)
  ())

(defmethod sb-cwalk:code :around ((hook sb-cwalk:code) reason form lexenv)
  (declare (ignore reason form lexenv))
  (let ((sb-cwalk:*current-code-hook* hook)
        (sb-cwalk:*current-macro-hook* nil)
        (sb-cwalk:*parent-lexenv* nil))
    (call-next-method)))
