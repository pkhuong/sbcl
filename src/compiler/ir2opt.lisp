;;;; This file implements some optimisations at the IR2 level.
;;;; Currently, the pass converts branches to conditional moves,
;;;; deletes subsequently dead blocks and then reoptimizes jumps.

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!C")

;;; We track pred/succ info at the IR2-block level, extrapolating
;;; most of the data from IR1 to initialise.
(declaim (type hash-table *2block-pred* *2block-succ* *label-2block*))
(defvar *2block-pred*)
(defvar *2block-succ*)
(defvar *label-2block*)

(defun initialize-ir2-blocks-flow-info (component)
  (labels ((block-last-2block (block)
             (declare (type cblock block))
             (do ((2block (block-info block)
                    (ir2-block-next 2block)))
                 (nil)
               (let ((next (ir2-block-next 2block)))
                 (when (or (null next)
                           (neq block (ir2-block-block next)))
                   (return 2block)))))
           (link-2blocks (pred succ)
             (declare (type ir2-block pred succ))
             (pushnew pred (gethash succ *2block-pred*))
             (pushnew succ (gethash pred *2block-succ*))))
    (do-blocks (block component :both)
      (let ((succ (block-succ block))
            (last (block-last-2block block)))
        (dolist (succ succ)
          (link-2blocks last (block-info succ)))
        (do ((2block (block-info block)
               (ir2-block-next 2block)))
            ((eq 2block last))
          (link-2blocks 2block (ir2-block-next 2block)))))
    (do-ir2-blocks (2block component)
      (awhen (ir2-block-%label 2block)
        (setf (gethash it *label-2block*) 2block)))))

(defun update-block-succ (2block succ)
  (declare (type ir2-block 2block)
           (type list succ))
  (flet ((blockify (x)
           (etypecase x
             (label (or (gethash x *label-2block*)
                        (error "Unknown label: ~S" x)))
             (ir2-block x))))
    (setf succ (mapcar #'blockify succ)))
  (dolist (old (gethash 2block *2block-succ*))
    (setf (gethash old *2block-pred*)
          (remove 2block (gethash old *2block-pred*))))
  (setf (gethash 2block *2block-succ*) succ)
  (dolist (new succ)
    (pushnew 2block (gethash new *2block-pred*))))

;;;; Conditional move insertion support code
#!-sb-fluid (declaim (inline vop-name))
(defun vop-name (vop &optional default)
  (declare (type vop vop))
  (let ((vop-info (vop-info vop)))
    (if vop-info
        (vop-info-name vop-info)
        default)))

(defun move-value-target (2block)
  (declare (type ir2-block 2block))
  (let* ((first  (or (ir2-block-start-vop 2block)
                     (return-from move-value-target)))
         (second (vop-next first)))
    (when (and (eq (vop-name first) 'move)
               (or (not second)
                   (eq (vop-name second) 'branch)))
      (values (tn-ref-tn (vop-args first))
              (tn-ref-tn (vop-results first))))))

;; A conditional jump may be converted to a conditional move if
;; both branches move a value to the same TN and then continue
;; execution in the same successor block.
;;
;; The label argument is used to return possible value TNs in
;; the right order (first TN if the branch would have been taken,
;; second otherwise)
(defun cmovp (label a b)
  (declare (type label label)
           (type cblock a b))
  (cond ((eq label (ir2-block-%label (block-info a))))
        ((eq label (ir2-block-%label (block-info b)))
         (rotatef a b))
        (t (return-from cmovp)))
  (let ((succ-a (block-succ a))
        (succ-b (block-succ b)))
    (unless (and (singleton-p succ-a)
                 (singleton-p succ-b)
                 (eq (car succ-a) (car succ-b)))
      (return-from cmovp))
    (multiple-value-bind (value-a target)
        (move-value-target (block-info a))
      (multiple-value-bind (value-b targetp)
          (move-value-target (block-info b))
        (and value-a value-b (eq target targetp)
             (values (block-label (car succ-a))
                     target value-a value-b))))))

;; To convert a branch to a conditional move:
;; 1. Convert both possible values to the chosen common representation
;; 2. Execute the conditional VOP
;; 3. Execute the chosen conditional move VOP
;; 4. Convert the result from the common representation
;; 5. Jump to the successor
#!-sb-fluid (declaim (inline convert-one-cmov))
(defun convert-one-cmov (cmove-vop
                         value-if arg-if
                         value-else arg-else
                         target res
                         flags info
                         label
                         vop node 2block)
  (delete-vop vop)
  (flet ((load-and-coerce (dst src)
           (when (and dst (neq dst src))
             (let ((end  (ir2-block-last-vop 2block))
                   (move (template-or-lose 'move)))
               (multiple-value-bind (first last)
                   (funcall (template-emit-function move) node 2block
                            move (reference-tn src nil)
                            (reference-tn dst t))
                 (insert-vop-sequence first last 2block end))))))
    (load-and-coerce arg-if   value-if)
    (load-and-coerce arg-else value-else))
  (emit-template node 2block (template-or-lose cmove-vop)
                 (reference-tn-list (remove nil (list arg-if arg-else))
                                    nil)
                 (reference-tn res t)
                 (list* flags info))
  (emit-move node 2block res target)
  (vop branch node 2block label)
  (update-block-succ 2block (list label)))

;; Since conditional branches are always at the end of blocks,
;; it suffices to look at the last VOP in each block.
(defun maybe-convert-one-cmov (2block)
  (let* ((block (ir2-block-block 2block))
         (succ (block-succ block))
         (a    (first succ))
         (b    (second succ))
         (vop  (or (ir2-block-last-vop 2block)
                   (return-from maybe-convert-one-cmov)))
         (node (vop-node vop)))
    (unless (eq (vop-name vop) 'branch-if)
      (return-from maybe-convert-one-cmov))
    (destructuring-bind (jump-target flags not-p) (vop-codegen-info vop)
      (multiple-value-bind (label target value-a value-b)
          (cmovp jump-target a b)
        (unless label
          (return-from maybe-convert-one-cmov))
        (multiple-value-bind (cmove-vop arg-a arg-b res info)
            (convert-conditional-move-p node target value-a value-b)
          (unless cmove-vop
            (return-from maybe-convert-one-cmov))
          (when not-p
            (rotatef value-a value-b)
            (rotatef arg-a arg-b))
          (convert-one-cmov cmove-vop value-a arg-a
                                      value-b arg-b
                                      target  res
                                      flags info
                            label vop node 2block))))))

(defun convert-cmovs (component)
  (do-ir2-blocks (2block component (values))
    (maybe-convert-one-cmov 2block)))

(defun delete-unused-ir2-blocks (component)
  (declare (type component component))
  (let ((live-2blocks (make-hash-table)))
    (labels ((mark-2block (2block)
               (declare (type ir2-block 2block))
               (when (gethash 2block live-2blocks)
                 (return-from mark-2block))
               (setf (gethash 2block live-2blocks) t)
               (map nil #'mark-2block (gethash 2block *2block-succ*))))
      (mark-2block (block-info (component-head component))))

    (flet ((delete-2block (2block)
             (declare (type ir2-block 2block))
             (do ((vop (ir2-block-start-vop 2block)
                    (vop-next vop)))
                 ((null vop))
               (delete-vop vop))))
      (do-ir2-blocks (2block component (values))
        (unless (gethash 2block live-2blocks)
          (delete-2block 2block))))))

(defun delete-fall-through-jumps (component)
  (flet ((jump-falls-through-p (2block)
           (let* ((last   (or (ir2-block-last-vop 2block)
                              (return-from jump-falls-through-p nil)))
                  (target (first (vop-codegen-info last))))
             (unless (eq (vop-name last) 'branch)
               (return-from jump-falls-through-p nil))
             (do ((2block (ir2-block-next 2block)
                    (ir2-block-next 2block)))
                 ((null 2block) nil)
               (cond ((eq target (ir2-block-%label 2block))
                      (return t))
                     ((ir2-block-start-vop 2block)
                      (return nil)))))))
    ;; Walk the blocks in reverse emission order to catch jumps
    ;; that fall-through only once another jump is deleted
    (let ((last-2block
           (do-ir2-blocks (2block component (aver nil))
             (when (null (ir2-block-next 2block))
               (return 2block)))))
      (do ((2block last-2block
             (ir2-block-prev 2block)))
          ((null 2block)
             (values))
        (when (jump-falls-through-p 2block)
          (delete-vop (ir2-block-last-vop 2block)))))))

(defvar *2block-kill*)
(defvar *2block-livein*)
(defvar *2block-liveout*)

(defun compute-2block-liveness (component)
  (declare (type component component))
  (labels ((walk (2block)
             (declare (type ir2-block 2block))
             (let ((use (gethash 2block *2block-livein*)))
               (when use (return-from walk use)))
             (let ((use  (make-hash-table))
                   (kill (make-hash-table)))
               (setf (gethash 2block *2block-livein*) use
                     (gethash 2block *2block-kill*) kill)
               (do ((vop (ir2-block-last-vop 2block) (vop-prev vop)))
                   ((null vop))
                 (do ((ref (vop-results vop) (tn-ref-across ref)))
                     ((null ref))
                   (let ((tn (tn-ref-tn ref)))
                     (setf (gethash tn use) nil)
                     (setf (gethash tn kill) t)))
                 (do ((ref (vop-args vop) (tn-ref-across ref)))
                     ((null ref))
                   (let ((tn (tn-ref-tn ref)))
                     (setf (gethash tn use) t))))
               (let ((liveout (make-hash-table)))
                 (setf (gethash 2block *2block-liveout*) liveout)
                 (dolist (succ (gethash 2block *2block-succ*) use)
                   (let ((use2 (walk succ)))
                     (maphash (lambda (tn live)
                                (when live
                                  (unless (gethash tn kill)
                                    (setf (gethash tn use) t))
                                  (setf (gethash tn liveout) t)))
                              use2)))))))
    (walk (block-info (component-head component)))
    (values)))

(defstruct ir2-node
  receivers
  globalp ; actually a property of TNs, but never mind
  name
  args
  results
  position
  vop)

(defun ir2-block-expression-graph (2block)
  (declare (type ir2-block 2block))
  (let ((values (make-hash-table))
        (nodes  (make-array 8 :adjustable t :fill-pointer 0)))
    (do ((vop (ir2-block-start-vop 2block)
           (vop-next vop)))
        ((null vop))
      (let* ((name (vop-name vop))
             (node (make-ir2-node :name name
                                  :vop vop)))
        (vector-push-extend node nodes)
        (do ((ref (vop-args vop) (tn-ref-across ref)))
            ((null ref)
               (setf (ir2-node-args node)
                     (nreverse (ir2-node-args node))))
          (let* ((tn (tn-ref-tn ref))
                 (arg-node (gethash tn values tn)))
            (unless (tn-p arg-node)
              (destructuring-bind (node2 . index) arg-node
                (push (cons node index) (ir2-node-receivers node2))))
            (push arg-node (ir2-node-args node))))
        (if #+nil (memq name '(move)) nil
            (setf (gethash (tn-ref-tn (vop-results vop)) values)
                  (first (ir2-node-args node)))
            (do ((ref (vop-results vop) (tn-ref-across ref))
                 (index 0 (1+ index)))
                ((null ref)
                   (setf (ir2-node-results node)
                         (nreverse (ir2-node-results node))))
              (let ((tn (tn-ref-tn ref)))
                (setf (gethash tn values) (cons node index))
                (push tn (ir2-node-results node)))))))
    (maphash (lambda (tn value)
               (when (gethash tn (gethash 2block *2block-liveout*))
                 (setf (ir2-node-globalp (car value)) t)))
             values)
    (values (let ((nodes (nreverse (coerce nodes 'simple-vector)))
                  (idx   0))
              (map nil (lambda (node)
                         (shiftf (ir2-node-position node) idx (1+ idx)))
                        nodes)
              nodes)
            values)))

(defun expression-graph-to-dot (graph)
  (declare (type simple-vector graph))
  (let ((names (make-hash-table)))
    (flet ((get-name (x)
             (or (gethash x names)
                 (setf (gethash x names)
                       (let ((*print-case* :downcase))
                         (let* ((node-p (ir2-node-p x))
                                (name (if node-p
                                          (ir2-node-name x)
                                          (primitive-type-name (tn-primitive-type x))))
                                (info (and node-p
                                           (vop-codegen-info (ir2-node-vop x))))
                                (stem (if info
                                           (format nil "[~A~{ ~A~}]" name info)
                                          (format nil "~A" name)))
                                (name (format nil "~A ~A"
                                              name
                                              (hash-table-count names))))
                           (if node-p
                               (format *compiler-trace-output* "~8T\"~A\" [label=\"~A~C\"];~%"
                                       name stem (if (ir2-node-globalp x)
                                                     #\! #\Space))
                               (format *compiler-trace-output* "~8T\"~A\" [label=\"~A\", shape=box];~%"
                                       name stem))
                           name))))))
      (format *compiler-trace-output* "digraph G {~%")
      (map nil #'get-name graph)
      (loop for node across graph
            for self = (get-name node)
            for args = (ir2-node-args node)
            do
         (dolist (arg args)
           (let ((number nil))
             (when (consp arg)
               (setf number (list (cdr arg))
                     arg (car arg)))
             (when (eql (car number) 0)
               (setf number nil))
             (format *compiler-trace-output* "~8T\"~A\" -> \"~A\" [~{label = ~A, ~}dir=back];~%"
                     self (get-name arg) number))))
      (format *compiler-trace-output* "}~%~%"))))

(defvar *ir2-optimize* nil)
(defun arg-name (arg)
  (and (consp arg)
       (ir2-node-name (car arg))))
(defun arg-results (arg)
  (if (consp arg)
      (ir2-node-results (car arg))
      arg))
(defun get-result (arg)
  (if (consp arg)
      (elt (ir2-node-results (car arg)) (cdr arg))
      arg))
(defun get-args (node)
  (mapcar #'get-result (ir2-node-args node)))
(defun single-use-p (x)
  (and (consp x)
       (null (cdr (ir2-node-receivers (cdr x))))))

(defun replace-vop (2block vop name args results info)
  (let ((template (template-or-lose name)))
    (multiple-value-bind (first last)
        (funcall (template-emit-function template)
                 (vop-node vop) 2block template
                 (reference-tn-list args
                                    nil)
                 (reference-tn-list results t)
                 info)
      (insert-vop-sequence first last 2block vop)
      (delete-vop vop)
      first)))

(defun %optimize-sum/simple-array-double-float (2block node)
  (let ((vop (ir2-node-vop node)))
    (when (eql (ir2-node-name node) 'sb-vm::+/double-float)
      (destructuring-bind (x y) (ir2-node-args node)
        (when (eql (arg-name y)
                   'sb-vm::data-vector-ref-with-offset/simple-array-double-float)
          (rotatef x y))
        (when (and (eql (arg-name x)
                        'sb-vm::data-vector-ref-with-offset/simple-array-double-float)
                   (single-use-p x))
          (replace-vop 2block vop
                       'sb-vm::data-vector-add-with-offset/simple-array-double-float
                       (cons (get-result y) (get-args (car x)))
                       (ir2-node-results node)
                       (vop-codegen-info (ir2-node-vop (car x))))
          (delete-vop (ir2-node-vop (car x)))
          t)))))

(defun %optimize-zerop/and (2block node)
  (let ((vop (ir2-node-vop node)))
    (when (and (eql (ir2-node-name node) 'sb-vm::fast-eql-c/fixnum)
               (equal '(0) (vop-codegen-info (ir2-node-vop node)))
               (eql (arg-name (first (ir2-node-args node)))
                    'sb-vm::fast-logand-c/fixnum=>fixnum)
               (single-use-p (first (ir2-node-args node))))
      (replace-vop 2block vop
                   'sb-vm::fast-test-c/fixnum
                   (get-args (car (first (ir2-node-args node))))
                   nil
                   (vop-codegen-info (ir2-node-vop (car (first (ir2-node-args node))))))
      (delete-vop (ir2-node-vop (car (first (ir2-node-args node)))))
      t)))

(defun only-move-between (graph from to)
  (when (> from to)
    (rotatef from to))
  (loop for i from (1+ from) below to
        always (eql (ir2-node-name (aref graph i))
                    'move)))

(defun principal-arg (node index)
  (let ((arg (elt (ir2-node-args node) index)))
    (loop
      (cond ((tn-p arg) (return arg))
            ((eql 'move (ir2-node-name (car arg)))
             (setf arg (first (ir2-node-args (car arg)))))
            (t (return (car arg)))))))

(defun %optimize-cmp/sub (2block graph node)
  (declare (ignore 2block))
  (let ((vop (ir2-node-vop node))
        arg)
    (when (and (memq (ir2-node-name node) '(sb-vm::fast-if->-c/fixnum
                                            sb-vm::fast-if-<-c/fixnum 
                                            sb-vm::fast-eql-c/fixnum))
               (equal '(0) (vop-codegen-info (ir2-node-vop node)))
               (ir2-node-p (setf arg (principal-arg node 0)))
               (eql (ir2-node-name arg)
                    'sb-vm::fast---c/fixnum=>fixnum)
               (only-move-between graph
                                  (ir2-node-position node)
                                  (ir2-node-position arg)))
      (delete-vop vop)
      t)))

(defun ir2-optimize-block (2block)
  (declare (type ir2-block 2block))
  (unless *ir2-optimize*
    (return-from ir2-optimize-block))
  (let ((graph (ir2-block-expression-graph 2block)))
    (unless (zerop (length graph))
      (when *compiler-trace-output*
        (format *compiler-trace-output* "~%~%graph: ~%~%")
        (expression-graph-to-dot graph)
        (force-output *compiler-trace-output*))
      (map nil (lambda (node)
                 (or (%optimize-sum/simple-array-double-float 2block node)
                     (%optimize-zerop/and 2block node)
                     (%optimize-cmp/sub 2block graph node)))
           graph))))

(defmacro with-ir2-blocks-flow-info ((component) &body body)
  `(let ((*2block-pred*  (make-hash-table))
         (*2block-succ*  (make-hash-table))
         (*label-2block* (make-hash-table)))
     (initialize-ir2-blocks-flow-info ,component)
     ,@body))

(defun ir2-optimize (component)
  (with-ir2-blocks-flow-info (component)
    (convert-cmovs component)
    (delete-unused-ir2-blocks component)
    (delete-fall-through-jumps component)
    (values)))

(defun ir2-reoptimize (component)
  (with-ir2-blocks-flow-info (component)
    (let ((*2block-kill* (make-hash-table))
          (*2block-livein*  (make-hash-table))
          (*2block-liveout*  (make-hash-table)))
      (compute-2block-liveness component)
      (do-ir2-blocks (2block component)
        (ir2-optimize-block 2block))))
  (values))
