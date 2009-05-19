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
(def!struct peephole-pattern
  ;; Name of the transform
  (name    (missing-arg) :type symbol)
  ;; If non-NIL, printed as an optimisation note
  ;; when the emitter function returns NIL.
  (note    nil           :type (or null string))
  ;; Receives the pattern, 2block and the first VOP
  ;; in the pattern, returns NIL or the first & last
  ;; VOPs in the sequence to replace the pattern.
  (emitter (missing-arg) :type function)
  ;; Vector of VOP names
  (pattern (missing-arg) :type vector)
  ;; Higher weights fire first
  (weight  0             :type fixnum))

(defvar *max-pattern-length* 0)
;; Table: Vector of VOP names -> vector of patterns
;; least weight first (fired back to front)
(defvar *patterns* (make-hash-table :test 'equalp))

(defun insert-pattern (pattern)
  (let* ((vops (peephole-pattern-pattern pattern))
         (hits (gethash vops *patterns*))
         (length (length vops)))
    (when (> length *max-pattern-length*)
      (setf *max-pattern-length* length))
    (unless hits
      (setf hits
            (setf (gethash vops *patterns*)
                  (make-array 2 :adjustable t :fill-pointer 0))))
    (let ((name (peephole-pattern-name pattern)))
      (dotimes (i (length hits) (vector-push-extend pattern hits))
        (when (eq name (peephole-pattern-name (aref hits i)))
          (setf (aref hits i) pattern)
          (return))))
    (stable-sort hits #'< :key #'peephole-pattern-weight)))

(def!macro define-peephole-pattern (name ((vop &rest vops) &key note (weight 0))
                                         &body body)
  `(insert-pattern (make-peephole-pattern
                    :name ',name
                    :note ',note
                    :emitter (lambda (pattern 2block vop)
                               (declare (ignorable pattern 2block vop))
                               (block ,name
                                 (locally
                                     ,@body)))
                    :pattern ',(coerce (cons vop vops) 'vector)
                    :weight  ',weight)))

(define-peephole-pattern box-around-add ((sb-vm::move-from-word/fixnum
                                          sb-vm::fast-+-c/fixnum=>fixnum
                                          sb-vm::move-to-word/fixnum))
  (let* ((from-word vop)
         (fast-+    (vop-next from-word))
         (to-word   (vop-next fast-+)))
    (let ((arg (tn-ref-tn (vop-args from-word)))
          (res (tn-ref-tn (vop-results to-word)))
          (inc (vop-codegen-info fast-+))
          (signed-inc (template-or-lose 'sb-vm::fast-+-c/signed=>signed)))
      (unless (and (eq (tn-ref-tn (vop-args fast-+))
                       (tn-ref-tn (vop-results from-word)))
                   (eq (tn-ref-tn (vop-results fast-+))
                       (tn-ref-tn (vop-args to-word)))
                   (null (tn-ref-next (tn-reads (tn-ref-tn (vop-results from-word)))))
                   (null (tn-ref-next (tn-reads (tn-ref-tn (vop-results fast-+))))))
        (return-from box-around-add))
      (funcall (template-emit-function signed-inc)
               (vop-node fast-+) 2block signed-inc
               (reference-tn arg nil) (reference-tn res t) inc))))

(define-peephole-pattern box-after-add ((sb-vm::fast-+-c/fixnum=>fixnum
                                         sb-vm::move-to-word/fixnum))
  (let* ((from-word (vop-prev vop))
         (fast-+    vop)
         (to-word   (vop-next fast-+)))
    (unless (eq 'sb-vm::move-from-word/fixnum (vop-name from-word))
      (return-from box-after-add))
    (let ((arg (tn-ref-tn (vop-args from-word)))
          (res (tn-ref-tn (vop-results to-word)))
          (inc (vop-codegen-info fast-+))
          (signed-inc (template-or-lose 'sb-vm::fast-+-c/signed=>signed)))
      (unless (and (eq (tn-ref-tn (vop-args fast-+))
                       (tn-ref-tn (vop-results from-word)))
                   (eq (tn-ref-tn (vop-results fast-+))
                       (tn-ref-tn (vop-args to-word)))
                   (null (tn-ref-next (tn-reads (tn-ref-tn (vop-results fast-+))))))
        (return-from box-after-add nil))
      (funcall (template-emit-function signed-inc)
               (vop-node fast-+) 2block signed-inc
               (reference-tn arg nil) (reference-tn res t) inc))))

(defvar *peephole-p* nil)

;; FIXME: how to handle successor info? How about single-
;; successor/predecessor 2blocks?
(defun peephole-2block (2block)
  (declare (type ir2-block 2block))
  (let* ((max-length *max-pattern-length*)
         (patterns   *patterns*)
         (needle     (make-array max-length :fill-pointer 0)))
    (flet ((subsearch (vop length)
             (declare (type vop vop)
                      (type (and unsigned-byte fixnum) length))
             (setf (fill-pointer needle) 0)
             (do ((vop vop (vop-next vop))
                  (i   0   (1+ i)))
                 ((>= i length))
               (unless vop
                 (return-from subsearch (values nil nil)))
               (vector-push-extend (vop-name vop) needle))
             (let* ((hits  (or (gethash needle patterns)
                               (return-from subsearch (values nil nil))))
                    (nhits (length hits)))
               (declare (type (vector t) hits))
               (loop for i from (1- nhits) downto 0
                     for pattern = (aref hits i)
                     do (multiple-value-bind (first last)
                            (funcall (peephole-pattern-emitter pattern)
                                     pattern 2block vop)
                          (when (and first last)
                            (return (values first last))))
                     finally (return (values t nil)))))
           (replace-vop (vop length new-first new-last)
             (do ((vop vop (vop-next vop))
                  (i   0   (1+ i)))
                 ((>= i length)
                    (insert-vop-sequence new-first new-last 2block vop)
                    new-first)
                 (delete-vop vop)))
           (prev-n (vop n)
             (do ((vop vop (vop-prev vop))
                  (i 0 (1+ i)))
                 ((or (>= i n)
                      (null (vop-prev vop)))
                    vop))))
      (do ((vop (ir2-block-start-vop 2block)))
          ((null vop))
        (loop for i from max-length downto 1
              do (multiple-value-bind (first last)
                     (subsearch vop i)
                   (when (and first last)
                     (setf vop (prev-n (replace-vop vop i first last)
                                       (1- max-length)))
                     (return)))
              finally (setf vop (vop-next vop)))))))

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

(defun ir2-optimize (component &key peephole-only)
  (let ((*2block-pred*  (make-hash-table))
        (*2block-succ*  (make-hash-table))
        (*label-2block* (make-hash-table)))
    (initialize-ir2-blocks-flow-info component)

    (unless peephole-only
      (convert-cmovs component))

    (when *peephole-p*
      (do-ir2-blocks (2block component)
        (peephole-2block 2block)))
    
    (delete-unused-ir2-blocks component)
    (delete-fall-through-jumps component))
  (values))
