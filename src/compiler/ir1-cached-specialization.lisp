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
    (if (ref-p use)
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
              (values default nil)))
        (values default nil))))

(defun fixup-sexp (sexp env)
  (labels ((walk (sexp &aux found)
             (cond ((setf found (assoc sexp env))
                    (cdr found))
                   ((consp sexp)
                    (cons (walk (car sexp))
                          (walk (cdr sexp))))
                   (t sexp))))
    (walk sexp)))

(defun maybe-specialize-call (combination)
  (declare (type combination combination))
  (unless (policy combination (plusp out-of-line-specialized-calls))
    (return-from maybe-specialize-call nil))
  (multiple-value-bind (key source remaining dx wrapper)
      (let ((specializer
              (fun-info-specializer
               (combination-fun-info combination))))
        (and specializer
             (funcall specializer combination)))
    (unless key
      (return-from maybe-specialize-call nil))
    (when (typep source '(cons (eql lambda)))
      (setf source `(named-lambda (specialized-function ,@key)
                        ,@(rest source))))
    (let* ((args (combination-args combination))
           (syms (mapcar (lambda (x)
                           (cons x (gensym "SPECIALIZED-ARG")))
                         args)))
      (transform-call
       combination
       `(lambda ,(mapcar 'cdr syms)
          (declare (ignorable ,@(mapcar 'cdr syms)))
          (,@(or (fixup-sexp wrapper syms)
                 '(progn))
           (funcall (load-time-value
                     (the (values function &optional)
                          (sb!impl::ensure-specialized-function
                           ',key
                           (locally
                               (declare
                                (optimize (out-of-line-specialized-calls 0)
                                          speed (space 0))
                                (muffle-conditions compiler-note))
                             ,source)))
                     t)
                    ,@(fixup-sexp remaining syms))))
       (combination-fun-source-name combination))
      (let* ((use  (lvar-use (combination-fun combination)))
             (leaf (ref-leaf use)))
        (aver (ref-p use))
        (aver (lambda-p leaf))
        (loop for var in (lambda-vars leaf)
              for arg in (combination-args combination)
              when (member arg dx)
                do (dolist (ref (lambda-var-refs var))
                     (setf (lvar-dx-safe-p (ref-lvar ref)) t))))))
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

(defun sequence-type-element-type (type)
  (let ((type (if (ctype-p type)
                  type
                  (specifier-type type))))
    (type-specifier (if (array-type-p type)
                        (array-type-element-type type)
                        (specifier-type t)))))

(defun specialize-seq-search (function
                              item sequence
                              key-var test-var test-not-var
                              from-end
                              start end)
  (let ((type (upgraded-sequence-type (lvar-type sequence)))
        (key  (lvar-fun-designator-name key-var  :if-null 'identity))
        (test (lvar-fun-designator-name test-var :if-null 'eql))
        (test-not (lvar-fun-designator-name test-not-var :default :maybe))
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
                      ,@(and endp `(,end)))
              (list key-var test-var test-not-var)))))

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
                                 key-var from-end
                                 start end)
  (let ((type (upgraded-sequence-type (lvar-type sequence)))
        (predicate (lvar-fun-designator-name pred :default 'any))
        (key  (lvar-fun-designator-name key-var  :if-null 'identity))
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
                ,@(and endp `(,end)))
              (list pred key-var)))))

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

(defun wrap-functions (&rest function-types)
  `(dx-flet ,(loop for entry in function-types
                   when entry
                     collect
                     (destructuring-bind (function . types) entry
                       (let ((gensyms (mapcar (lambda (type) type
                                                (gensym "WRAPPER-ARG"))
                                              types)))
                         `(,function (,@gensyms)
                             (declare ,@(mapcar (lambda (gensym type)
                                                  `(type ,type ,gensym))
                                                gensyms types))
                             (funcall ,function ,@gensyms)))))))

(defoptimizer (sort specializer) ((sequence pred &key key))
  (let* ((type (upgraded-sequence-type (lvar-type sequence)))
         #+nil(eltype (sequence-type-element-type type))
         (predicate (lvar-fun-designator-name pred :default 'any))
         (key-var key)
         (key  (lvar-fun-designator-name key-var
                                         :default 'any
                                         :if-null 'identity)))
    (when type
      (values `(sort ,type ,predicate ,key)
              `(lambda (sequence
                        ,@(and (eql predicate 'any) '(predicate))
                        ,@(and (eql key 'any) '(key)))
                 (declare (type ,type sequence)
                          (inline sort))
                 (sort sequence ,(if (eql predicate 'any)
                                     'predicate `',predicate)
                       :key ,(if (eql key 'any)
                                 'key `',key)))
              `(,sequence
                ,@(and (eql predicate 'any) `(,pred))
                ,@(and (eql key 'any) `(,key-var)))
              (list pred key-var)))))

(defoptimizer (%map specializer) ((result-type fun seq &rest seqs) node)
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
                  (cons seq seqs))
              (list fun)))))

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
              `(lambda (dest ,@(and (eql function 'any) '(function))
                        ,@seq-temps)
                 (declare (type ,dest-type dest)
                          ,@(mapcar (lambda (type temp)
                                      `(type ,type ,temp))
                                    seq-types seq-temps))
                 (map-into dest
                           ,(if (eql function 'any) 'function `',function)
                           ,@seq-temps))
              `(,dest ,@(and (eql function 'any) `(#',fun)) ,@seqs)
              (list fun)
              (wrap-functions (cons fun
                                    (mapcar #'sequence-type-element-type seq-types)))))))
