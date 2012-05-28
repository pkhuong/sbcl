(in-package "SB!C")

(defun useful-function-p (fun-name)
  (or (info :function :inline-expansion-designator fun-name)
      (info :function :source-transform fun-name)
      (info :function :info fun-name)
      (info :function :compiler-macro-function fun-name)))

(defun lvar-fun-designator-name (lvar &key default if-null)
  (declare (type (or null lvar) lvar))
  (when (null lvar)
    (return-from lvar-fun-designator-name (values if-null nil)))
  (let ((use (lvar-uses lvar)))
    (and (ref-p use)
         (let* ((*lexenv* (node-lexenv use))
                (leaf (ref-leaf use))
                (name
                 (cond ((global-var-p leaf)
                        (and (eq (global-var-kind leaf) :global-function)
                             (leaf-source-name leaf)))
                       ((constant-p leaf)
                        (let ((value (constant-value leaf)))
                          (typecase value
                            (symbol (or value if-null))
                            (sb!kernel:simple-fun
                             (let ((name (sb!kernel:%simple-fun-name value)))
                               (and name
                                    (symbolp name)
                                    (eql (symbol-package name)
                                         (find-package "COMMON-LISP"))
                                    (fboundp name)
                                    (eql value (fdefinition name))
                                    name)))))))))
           (if (and name
                    (symbolp name)
                    (not (fun-lexically-notinline-p name))
                    (useful-function-p name))
               (values name t)
               (values default nil))))))

(defun maybe-specialize-call (combination)
  (declare (type combination combination))
  (unless (policy combination (plusp out-of-line-specialized-calls))
    (return-from maybe-specialize-call nil))
  (multiple-value-bind (key source remaining)
      (let ((specializer
              (fun-info-specializer
               (combination-fun-info combination))))
        (and specializer
             (funcall specializer combination)))
    (unless key
      (return-from maybe-specialize-call nil))
    (let* ((args (combination-args combination))
           (syms (mapcar (lambda (x)
                           (cons x (gensym "ARG")))
                         args)))
      (transform-call
       combination
       `(lambda ,(mapcar 'cdr syms)
          (declare (ignorable ,@(mapcar 'cdr syms)))
          (funcall (load-time-value
                    (sb!impl::ensure-specialized-function
                     ',key
                     (the function
                          (locally
                              (declare
                               (optimize (out-of-line-specialized-calls 0)
                                         speed (space 0))
                               (muffle-conditions compiler-note))
                            ,source)))
                    t)
                   ,@(mapcar (lambda (arg)
                               (or (cdr (assoc arg syms))
                                   (bug "Unknown argument ~A" arg)))
                             remaining)))
       (combination-fun-source-name combination))))
  t)

(defun upgraded-sequence-type (type &optional default)
  (declare (type ctype type))
  (macrolet ((check (&rest cases)
               `(cond ,@(loop for case in cases collect
                              `((csubtypep type (specifier-type ',case))
                                ',case))
                      (t default)))
             (do-it (&rest cases)
               `(check
                 ,@cases
                 ,@(loop
                     for saetp
                     across sb!vm:*specialized-array-element-type-properties*
                     for eltype = (sb!vm:saetp-specifier saetp)
                     collect `(simple-array ,eltype 1)
                     collect `(array ,eltype 1)))))
    (do-it list)))

(defun specialize-seq-search (function
                              item sequence
                              key test test-not
                              from-end
                              start end)
  (let ((type (upgraded-sequence-type (lvar-type sequence)))
        (key  (lvar-fun-designator-name key  :if-null 'identity))
        (test (lvar-fun-designator-name test :if-null 'eql))
        (test-not (lvar-fun-designator-name test-not :default :maybe))
        (from-end (cond ((null from-end) nil)
                        ((constant-lvar-p from-end)
                         (not (not (lvar-value from-end))))
                        (t :maybe)))
        (startp (and start
                     (not (and (constant-lvar-p start)
                               (member (lvar-value start) '(0 nil))))))
        (endp  (and end
                    (not (and (constant-lvar-p end)
                              (not (lvar-value end)))))))
    (when (and type key test
               (neq test-not :maybe)
               (neq from-end :maybe))
      (values `(,function ,type ,key ,test ,test-not ,from-end
                     ,startp ,endp)
              `(lambda (item sequence
                        ,@(and startp '(start)) ,@(and endp '(end)))
                 (declare (type ,type sequence))
                 (,function item sequence
                            :key ',key
                            ,@(if test-not
                                  `(:test-not ',test-not)
                                  `(:test ',test))
                            :from-end ,from-end
                            ,@(and startp '(:start start))
                            ,@(and endp   '(:end end))))
              `(,item ,sequence
                      ,@(and startp `(,start))
                      ,@(and endp `(,end)))))))

(macrolet ((def (name)
             `(defoptimizer (,name specializer)
                  ((item sequence &key
                         key test test-not from-end
                         start end))
                (specialize-seq-search ',name item sequence
                                       key test test-not
                                       from-end
                                       start end))))
  (def find)
  (def position))

(defun specialize-seq-search-if (function
                                 pred sequence
                                 key from-end
                                 start end)
  (let ((type (upgraded-sequence-type (lvar-type sequence)))
        (predicate (lvar-fun-designator-name pred :default 'any))
        (key  (lvar-fun-designator-name key  :if-null 'identity))
        (from-end (cond ((null from-end) nil)
                        ((constant-lvar-p from-end)
                         (not (not (lvar-value from-end))))
                        (t :maybe)))
        (startp (and start
                     (not (and (constant-lvar-p start)
                               (member (lvar-value start) '(0 nil))))))
        (endp  (and end
                    (not (and (constant-lvar-p end)
                              (not (lvar-value end)))))))
    (when (and type key
               (neq from-end :maybe))
      (values `(,function ,type ,predicate ,key ,from-end
                          ,startp ,endp)
              `(lambda (,@(and (eql predicate 'any) '(predicate)) sequence
                        ,@(and startp '(start)) ,@(and endp '(end)))
                 (declare (type ,type sequence))
                 (,function ,(if (eql predicate 'any)
                                 'predicate
                                 `',predicate)
                            sequence
                            :key ',key
                            :from-end ,from-end
                            ,@(and startp '(:start start))
                            ,@(and endp   '(:end end))))
              `(,@(and (eql predicate 'any) `(,pred))
                ,sequence
                ,@(and startp `(,start))
                ,@(and endp `(,end)))))))

(macrolet ((def (name)
             `(defoptimizer (,name specializer)
                  ((predicate sequence &key
                              key from-end
                              start end))
                (specialize-seq-search-if ',name predicate sequence
                                          key
                                          from-end
                                          start end))))
  (def find-if)
  (def find-if-not)
  (def position-if)
  (def position-if-not))

(defoptimizer (sort specializer) ((sequence pred &key key))
  (let ((type (upgraded-sequence-type (lvar-type sequence)))
        (predicate (lvar-fun-designator-name pred :default 'any))
        (key  (lvar-fun-designator-name key
                                        :if-null 'identity)))
    (when (and type key)
      (values `(sort ,type ,predicate ,key)
              `(lambda (sequence
                        ,@(and (eql predicate 'any) '(predicate)))
                 (declare (type ,type sequence)
                          (inline sort))
                 (sort sequence ,(if (eql predicate 'any)
                                     'predicate `',predicate)
                       :key ',key))
              `(,sequence
                ,@(and (eql predicate 'any) `(,pred)))))))

#+nil
(defoptimizer (%map specializer) ((result-type fun seq &rest seqs))
  (block nil
    (unless (constant-lvar-p result-type)
      (return))
    (let ((result-type (lvar-value result-type))
          (function    (lvar-fun-designator-name fun :default 'any))
          (seq-types   (mapcar (lambda (x)
                                 (upgraded-sequence-type (lvar-type x)))
                               (cons seq seqs)))
          (seq-temps   (mapcar (lambda (x)
                                 (declare (ignore x))
                                 (gensym "SEQ"))
                               (cons seq seqs))))
      (when (position nil seq-types)
        (return))
      (values `(%map ,result-type ,function ,@seq-types)
              `(lambda (,@(and (eql function 'any) '(function))
                        ,@seq-temps)
                 (declare ,@(mapcar (lambda (type temp)
                                      `(type ,type ,temp))
                                    seq-types seq-temps))
                 (%map ',result-type
                       ,(if (eql function 'any) 'function `',function)
                       ,@seq-temps))
              (if (eql function 'any)
                  (list* fun seq seqs)
                  (cons seq seqs))))))

#+nil
(defoptimizer (map-into specializer) ((dest fun &rest seqs))
  (let ((dest-type   (upgraded-sequence-type (lvar-type dest)))
        (function    (lvar-fun-designator-name fun :default 'any))
        (seq-types   (mapcar (lambda (x)
                               (upgraded-sequence-type (lvar-type x)))
                             seqs))
        (seq-temps   (mapcar (lambda (x)
                               (declare (ignore x))
                               (gensym "SEQ"))
                             seqs)))
    (unless (or (not dest-type)
                (position nil seq-types))
      (values `(map-into ,dest-type ,function ,@seq-types)
              `(lambda (dest,@(and (eql function 'any) '(function))
                        ,@seq-temps)
                 (declare (type ,dest-type dest)
                          ,@(mapcar (lambda (type temp)
                                      `(type ,type ,temp))
                                    seq-types seq-temps))
                 (map dest
                      ,(if (eql function 'any) 'function `',function)
                      ,@seq-temps))
              `(,dest ,(and (eql function 'any) `(,fun)) ,@seqs)))))
