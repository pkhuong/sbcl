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

(defvar sb-cwalk:*parent-lexenv*)

(defun sb-cwalk:wrap (form &key
                             (code-hook sb-cwalk:*current-code-hook*)
                             (macro-hook sb-cwalk:*current-macro-hook*)
                             (lexenv sb-cwalk:*parent-lexenv*))
  (sb-c::make-lexenv-wrapper form
                             :codewalking-hooks code-hook
                             :premacro-hooks macro-hook
                             :lexenv lexenv))
