;;;; This file contains code for the iterative spilling/coloring
;;;; register allocator

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!REGALLOC")

;;; Interference graph data structure

;; vertex in an interference graph
(def!struct (vertex
             (:constructor make-vertex (tn pack-type)))
  ;; PLACE IN THE GRAPH STRUCTURE
  ;; incidence list
  ;; vertices (node numbers) that are adjacent to the node
  ;; index vector
  ;; FIXME
  (incidence nil :type list)
  ;; POINTER Back to TN
  (tn nil :type tn)
  ;; type of packing necessary
  (pack-type nil :type (member :normal :wired :restricted))
  ;; PROPERTIES
  ;; color = (cons offset sc)
  (color nil :type (or cons null))
  ;; STATUS
  ;; is at the same time  marked for deletion
  (spill-candidate nil :type t)
  ;; current status invisible  or not  (on stack or not)
  (invisible nil :type t))

(defun vertex-sc (vertex)
  (tn-sc (vertex-tn vertex)))

;; interference graph
(def!struct (interference-graph
             (:constructor %make-interference-graph)
             (:conc-name #:ig-))
  (vertices nil :type list))

;; all TNs types are included in the graph, both with offset and without
(defun make-interference-graph (vertices)
  (let ((interference (%make-interference-graph :vertices vertices)))
    (dolist (vertex vertices)
      (let* ((tn (vertex-tn vertex))
             (offset (tn-offset tn))
             (sc (tn-sc tn)))
        (setf (vertex-incidence vertex) '()
              (vertex-invisible vertex) nil
              (vertex-color vertex) (and offset
                                         (cons offset sc)))))
    (loop for (a . rest) on vertices
          for tn = (vertex-tn a)
          for sb = (sc-sb (tn-sc tn))
          do (loop for b in rest
                   do (when (and (eql sb (sc-sb (tn-sc (vertex-tn b))))
                                 (tns-conflict tn (vertex-tn b)))
                        (aver (not (member a (vertex-incidence b))))
                        (aver (not (member b (vertex-incidence a))))
                        (push a (vertex-incidence b))
                        (push b (vertex-incidence a)))))
    interference))

;; &key reset: whether coloring/invisibility information should be
;; removed from all the remaining vertices
(defun remove-vertex-from-interference-graph (vertex graph &key reset)
  (declare (type vertex vertex) (type interference-graph graph))
  (let ((vertices (if reset
                      (loop for v in (ig-vertices graph)
                            unless (eql v vertex)
                              do (let* ((tn (vertex-tn v))
                                        (offset (tn-offset tn))
                                        (sc (tn-sc tn)))
                                   (setf (vertex-invisible v) nil
                                         (vertex-color v)
                                         (and offset
                                              (cons offset sc))))
                              and collect v)
                      (remove vertex (ig-vertices graph)))))
    (dolist (neighbour (vertex-incidence vertex)
                       (%make-interference-graph :vertices vertices))
      (setf (vertex-incidence neighbour)
            (remove vertex (vertex-incidence neighbour))))))

;; Give an interference graph, return a function that maps TNs to
;; vertices, and then to the vertex's assigned offset, if any.
(defun make-tn-offset-mapping (graph)
  (let ((table (make-hash-table)))
    (dolist (vertex (ig-vertices graph))
      (setf (gethash (vertex-tn vertex) table) vertex))
    (flet ((tn->vertex (tn)
             (let ((vertex (gethash tn table)))
               (when vertex
                 (values (car (vertex-color vertex))
                         vertex)))))
      #'tn->vertex)))

;;; Support code
(defvar *loop-depth-weight* 1)
(defun tn-spill-cost (tn &optional (loop-weight *loop-depth-weight*))
  (* (+ (max loop-weight 1) (tn-loop-depth tn)) (tn-cost tn)))

;; Return non-nil if COLOR conflicts with any of NEIGHBOR-COLORS.
;; Take into account element sizes of the respective SCs.
(defun color-conflict-p (color neighbor-colors)
  (declare (type (cons integer sc) color))
  (flet ((intervals-intersect-p (x x-width y y-width)
           (when (< y x)
             (rotatef x y)
             (rotatef x-width y-width))
           ;; x <= y. [x, x+x-width] and [y, y+y-width) intersect iff
           ;; y \in [x, x+x-width).
            (< y (+ x x-width))))
    (destructuring-bind (offset . sc) color
      (let ((element-size (sc-element-size sc)))
        (loop for (neighbor-offset . neighbor-sc) in neighbor-colors
              thereis (intervals-intersect-p
                       offset element-size
                       neighbor-offset (sc-element-size neighbor-sc)))))))

;; Assumes that VERTEX  pack-type is :WIRED.
(defun vertex-color-possible-p (vertex color)
  (declare (type integer color) (type vertex vertex))
  (and (or (and (neq (vertex-pack-type vertex) :wired)
                (not (tn-offset (vertex-tn vertex))))
           (= color (car (vertex-color vertex))))
       (not (color-conflict-p (cons color (vertex-sc vertex))
                              (mapcan (lambda (neighbour)
                                        (and (not (vertex-invisible neighbour))
                                             (list (vertex-color neighbour))))
                                      (vertex-incidence vertex))))))

;; Sorted list of all possible locations for vertex in its preferred
;; SC: more heavily loaded (i.e that should be tried first) locations
;; first.
(defun vertex-domain (vertex)
  (declare (type vertex vertex))
  (flet ((color-always-live-conflict (color)
           ;; Counts, for all the offsets in the SB, the max # of
           ;; basic blocks in which that location is used by an
           ;; :always-live TN.  This measure is an approxmation of the
           ;; pressure on that specific location.
           (loop with sb = (sc-sb (vertex-sc vertex))
                 for offset from color
                 repeat (sc-element-size (vertex-sc vertex))
                 maximize (aref (finite-sb-always-live-count sb) offset))))
    (declare (dynamic-extent #'color-always-live-conflict))
    (let* ((sc (vertex-sc vertex))
           (reserved (sc-reserve-locations sc))
           (allowed (remove-if-not (lambda (color)
                                     (and (vertex-color-possible-p vertex color)
                                          ;; common case is there are
                                          ;; no reserve locs
                                          (not (and reserved
                                                    (memq color reserved)))))
                                   (sc-locations sc))))
      (schwartzian-stable-sort-list allowed #'>
                                    :key #'color-always-live-conflict))))

(defun vertex-target-vertices (vertex tn-offset)
  (declare (type vertex vertex) (type function tn-offset))
  (let ((sb (sc-sb (vertex-sc vertex)))
        (neighbors (vertex-incidence vertex))
        vertices)
    (do-target-tns (current (vertex-tn vertex) :limit 20)
      (multiple-value-bind (offset target)
          (funcall tn-offset current)
        (when (and offset
                   (eq sb (sc-sb (tn-sc current)))
                   (not (member target neighbors)))
          (pushnew target vertices))))
    (nreverse vertices)))

;; Choose the "best" color for these vertices: a color is good if as
;;  many of these vertices simultaneously take that color, and those
;;  that can't have a low spill cost.
(defun vertices-best-color (vertices colors)
  (let ((best-color      nil)
        (best-compatible '())
        (best-cost       nil))
    ;; TODO: sort vertices by spill cost, so that high-spill cost ones
    ;; are more likely to be compatible?  We're trying to find a
    ;; maximal 1-colorable subgraph here, ie. a maximum independent
    ;; set :\ Still, a heuristic like first attempting to pack in
    ;; max-cost vertices may be useful
    (dolist (color colors)
      (let ((compatible '())
            (cost 0))
        (dolist (vertex vertices)
          (when (and (notany (lambda (existing)
                               (member vertex (vertex-incidence existing)))
                             compatible)
                     (vertex-color-possible-p vertex color))
            (incf cost (max 1 (tn-spill-cost (vertex-tn vertex))))
            (push vertex compatible)))
        (when (or (null best-cost)
                  (> cost best-cost))
          (setf best-color      color
                best-compatible compatible
                best-cost       cost))))
    (values best-color best-compatible)))

(defun find-vertex-color (vertex tn-vertex-mapping)
  (awhen (vertex-domain vertex)
    (let ((targets (vertex-target-vertices vertex tn-vertex-mapping))
          (sc (vertex-sc vertex)))
      (multiple-value-bind (color recolor-vertices)
          (if targets
              (vertices-best-color targets it)
              (values (first it) nil))
        ;; FIXME: can this happen during normal code, or is that a
        ;; BUG?
        (unless color
          (let ((*print-level* 3))
            (print :failed-to-align-with-targets)
            (dolist (target (vertex-target-vertices vertex tn-vertex-mapping))
              (print (list :target target))
              (print (vertex-domain target)))
            (print (list :colors-for-me
                         vertex
                         (vertex-domain vertex)))))
        (when color
          ;; FIXME: must the targets be recolored here?
          (dolist (target recolor-vertices)
            (aver (car (vertex-color target)))
            (unless (eql color (car (vertex-color target)))
              (aver (eq (sc-sb sc)
                        (sc-sb (vertex-sc target))))
              (aver (not (tn-offset (vertex-tn target))))
              ;; this check seems slow. Is it necessary?
              (aver (vertex-color-possible-p target color))
              (setf (car (vertex-color target)) color)))
          (return-from find-vertex-color (cons color sc)))))))

(defun partition-and-order-vertices (interference-graph)
  (flet ((domain-size (vertex)
           (let ((sc (vertex-sc vertex-sc)))
             (- (length (sc-locations sc))
                (length (sc-reserve-locations sc)))))
         (degree (vertex)
           (count-if-not #'vertex-invisible (vertex-incidence vertex)))
         (mark-as-spill-candidate (vertex)
           (setf (vertex-spill-candidate vertex) t))
         (eliminate-vertex (vertex)
           (setf (vertex-invisible vertex) t)))
    (let* ((precoloring-stack '())
           (prespilling-stack '())
           (vertices (remove-if #'vertex-color (ig-vertices interference-graph)))
           (sorted-vertices (schwartzian-stable-sort-list
                             vertices '<
                             :key (lambda (vertex)
                                    (tn-spill-cost (vertex-tn vertex))))))
      ;; walk the vertices from least important to most important TN wrt
      ;; spill cost.  That way the TNs we really don't want to spill are
      ;; at the head of the colouring lists.
      (loop for vertex in sorted-vertices do
        (aver (not (vertex-color vertex))) ; we already took those out above
        (eliminate-vertex vertex)
        ;; FIXME: some interference will be with vertices that don't
        ;;  take the same number of slots. Find a smarter heuristic.
        (cond ((< (degree vertex) (domain-size vertex))
               (push vertex precoloring-stack))
              (t
               (mark-as-spill-candidate vertex)
               (push vertex prespilling-stack))))
      (values precoloring-stack prespilling-stack))))

(defun color-interference-graph (interference-graph)
  (let ((tn-vertex (make-tn-offset-mapping interference-graph)))
    (flet ((color-vertices (vertices probably-colored-p)
             (dolist (vertex vertices)
               (let ((color (find-vertex-color vertex tn-vertex)))
                 (unless (or color (not probably-colored-p))
                   ;; FIXME: is that just debugging output?
                   (flet ((colors-in (incidence)
                            (delete-duplicates
                             (mapcar (lambda (vertex)
                                       (car (vertex-color vertex)))
                                     incidence))))
                     (let ((visible-neighbours (remove-if #'vertex-invisible
                                                          (vertex-incidence vertex))))
                       (print  (list "vertex inc " (length (vertex-incidence vertex))
                                     "visibles " (length visible-neighbours)
                                     "colors" (colors-in (vertex-incidence vertex))
                                     "length colo " (length (colors-in visible-neighbours))
                                     "sc-length" (length (sc-locations (vertex-sc vertex))))))))
                 (when color
                   (setf (vertex-color vertex) color
                         (vertex-invisible vertex) nil))))))
      (multiple-value-bind (probably-colored probably-spilled)
          (partition-and-order-vertices interference-graph)
        ;; If this were done correctly (see FIXME above), all probably
        ;; colored would find a color.
        (color-vertices probably-colored t)
        ;; These might benefit from further ordering... LexBFS?
        (color-vertices probably-spilled nil))))
  interference-graph)

(defvar *iterations* 500)

;;; Find the least-spill-cost neighbour in each color.
(defun collect-min-spill-candidates (vertex)
  (let ((colors '()))
    (loop for neighbor in (vertex-incidence vertex)
          when (eql :normal (vertex-pack-type neighbor))
            do (let* ((color (car (vertex-color neighbor)))
                      (cell (assoc color colors))
                      (cost-neighbor (tn-spill-cost (vertex-tn neighbor))))
                 (cond (cell
                        (when (< cost-neighbor (tn-spill-cost
                                                (vertex-tn (cdr cell))))
                          (setf (cdr cell) neighbor)))
                       (t (push (cons color neighbor) colors)))))
    (remove nil (mapcar #'cdr colors))))

;; If true, try to be clever, but the rest of the spill selection
;; logic is too simplistic to exploit it.
(defvar *candidate-color-flag* nil)

(defun iterate-color (vertices &optional (iterations *iterations*))
  (let* ((spill-list '())
         (nvertices (length vertices))
         (number-iterations (min iterations nvertices))
         (sorted-vertices (stable-sort ;; FIXME: why the sort?
                           (copy-list vertices) #'tn-loop-depth-cost->
                           :key #'vertex-tn))
         (graph (make-interference-graph sorted-vertices))
         to-spill)
    (labels ((spill-candidates (vertices)
               (remove-if-not (lambda (vertex)
                                (and (eql :normal (vertex-pack-type vertex))
                                     (not (vertex-color vertex))))
                              vertices))
             (iter (to-spill)
               (when to-spill
                 (setf graph (remove-vertex-from-interference-graph
                              to-spill graph :reset t)))
               (color-interference-graph graph)
               (let ((spill-candidates (spill-candidates
                                        (ig-vertices graph)))
                     (color-flag *candidate-color-flag*)
                     best-cost
                     best-spill)
                 (declare (ignorable color-flag))
                 (when spill-candidates
                   (flet ((candidate (vertex)
                            (let ((cost (tn-spill-cost (vertex-tn vertex))))
                              (when (or (null best-cost)
                                        (< cost best-cost))
                                (setf best-cost cost
                                      best-spill vertex)))))
                     (mapc #'candidate spill-candidates)
                     ;; Compile times become much too long if this is enabled...
                     #+nil
                     (dolist (candidate spill-candidates)
                       (candidate candidate)
                       (if color-flag
                           (mapc #'candidate (collect-min-spill-candidates candidate))
                           (dolist (neighbour (vertex-incidence candidate))
                             (when (eql (vertex-pack-type neighbour) :normal)
                               (candidate neighbour))))))
                   (aver best-spill)
                   (setf (vertex-color best-spill) nil)
                   (push best-spill spill-list)
                   best-spill))))
      (loop repeat number-iterations
            while (setf to-spill (iter to-spill))))
    (let ((rest-vertices (ig-vertices graph)))
      (when to-spill
        (setf rest-vertices (remove to-spill rest-vertices)))
      (aver (= nvertices (+ (length spill-list) (length rest-vertices))))
      (append spill-list rest-vertices))))

(defun pack-colored (colored-vertices)
  (dolist (vertex colored-vertices)
    (let* ((color (vertex-color vertex))
           (offset (car color))
           (tn (vertex-tn vertex))
           (tn-offset (tn-offset tn)))
      (when (and offset (not tn-offset))
        (aver (not (conflicts-in-sc tn (tn-sc tn) offset)))
        (setf (tn-offset tn) offset)
        (pack-wired-tn (vertex-tn vertex) nil))))
  colored-vertices)

(defun pack-iterative (component 2comp optimize)
  (declare (type component component) (type ir2-component 2comp))
  (collect ((vertices))
    ;; Pack TNs that *must* be in a certain location or SC first,
    ;; but still register them in the interference graph.
    (do ((tn (ir2-component-wired-tns 2comp) (tn-next tn)))
        ((null tn))
      (pack-wired-tn tn optimize)
      (vertices (make-vertex tn :wired)))
    ;; Pack restricted component TNs first: they have the longest live
    ;; ranges, might as well avoid fragmentation when trivial.
    (do ((tn (ir2-component-restricted-tns 2comp) (tn-next tn)))
        ((null tn))
      (when (eq (tn-kind tn) :component)
        (pack-tn tn t optimize)
        (vertices (make-vertex tn :restricted))))
    (do ((tn (ir2-component-restricted-tns 2comp) (tn-next tn)))
        ((null tn))
      (unless (tn-offset tn)
        (pack-tn tn t optimize))
      (vertices (make-vertex tn :restricted)))

    ;; Now that all pre-packed TNs are registered as vertices,
    ;; work on normal ones.  Walk through all normal TNs, and
    ;; determine whether we should try to allocate them
    ;; registers or stick them straight to the stack.
    (do ((tn (ir2-component-normal-tns 2comp) (tn-next tn)))
        ((null tn))
      ;; Only consider TNs that aren't forced on the stack and
      ;; for which the spill cost is non-negative (i.e. not
      ;; live across so many calls that it's simpler to just
      ;; leave them on the stack)
      (when (and (not (tn-offset tn))
                 (neq (tn-kind tn) :more)
                 (neq (sb-kind (sc-sb (tn-sc tn))) :unbounded)
                 (>= (tn-cost tn) 0))
        ;; otherwise, we'll let the final pass handle them.
        (vertices (make-vertex tn :normal))))
    ;; Sum loop depths to guide the spilling logic
    (assign-tn-depths component :reducer #'+)
    ;; Iteratively find a coloring/spill partition, and
    ;; allocate those for which we have a location
    (pack-colored (iterate-color (vertices))))
  nil)
