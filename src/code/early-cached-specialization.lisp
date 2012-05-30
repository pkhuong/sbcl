(in-package "SB!IMPL")
(!begin-collecting-cold-init-forms)
(defvar *specialized-function-cache* (make-hash-table
                                      :test 'equal))
(!cold-init-forms
  (setq *specialized-function-cache* (make-hash-table
                                      :test 'equal
                                      #-sb-xc-host :weakness #-sb-xc-host :value)))

(defun ensure-specialized-function (key function)
  (unless (boundp '*specialized-function-cache*)
    (return-from ensure-specialized-function function))
  (let ((table *specialized-function-cache*))
    (#-sb-xc-host with-locked-hash-table #-sb-xc-host (table)
     #+sb-xc-host progn
      (or (gethash key table)
          (setf (gethash key table) (compile nil function))))))

(!defun-from-collected-cold-init-forms !cached-specialization-cold-init)
