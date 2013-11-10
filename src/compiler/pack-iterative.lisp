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
(defstruct (ordered-set
            (:include sset)
            (:conc-name #:oset-))
  (members nil :type list))

(defun oset-adjoin (oset element)
  (when (sset-adjoin element oset)
    (push element (oset-members oset))
    t))

(defun oset-delete (oset element)
  (when (sset-delete element oset)
    (setf (oset-members oset)
          (delete element (oset-members oset)))
    t))

(defun oset-member (oset element)
  (sset-member element oset))

(defmacro do-oset-elements ((variable oset &optional return) &body body)
  `(dolist (,variable (oset-members ,oset) ,return)
     ,@body))

;; vertex in an interference graph
(def!struct (vertex
             (:include sset-element)
             (:constructor make-vertex (tn pack-type)))
  ;; PLACE IN THE GRAPH STRUCTURE
  ;; incidence list
  ;; vertices (node numbers) that are adjacent to the node
  ;; index vector
  ;; FIXME
  (incidence (make-ordered-set) :type ordered-set)
  ;; list of potential locations in the TN's preferred SB for the
  ;; vertex, taking into account reserve locations and preallocated
  ;; TNs.
  (initial-domain nil :type list)
  (initial-domain-size 0 :type index)
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

(declaim (inline vertex-sc))
(defun vertex-sc (vertex)
  (tn-sc (vertex-tn vertex)))

;; interference graph
(def!struct (interference-graph
             (:constructor %make-interference-graph)
             (:conc-name #:ig-))
  ;; sorted set of yet-uncolored (and not necessarily spilled)
  ;; vertices: vertices with lower spill cost come first.
  (vertices nil :type list)
  ;; unsorted set of precolored vertices.
  (precolored-vertices nil :type list)
  (tn-vertex (bug "missing arg") :type hash-table)
  ;; A function that maps TNs to vertices, and then to the vertex's
  ;; assigned offset, if any.  The offset (or NIL) is returned first,
  ;; then the vertex as a second value.
  (tn-vertex-mapping (bug "missing arg") :type function))

;;; Interference graph construction

;; Supposing that TN is restricted to its preferred SC, what locations
;; are available?
(defun restricted-tn-locations (tn)
  (declare (type tn tn))
  (let* ((sc (tn-sc tn))
         (size (sc-element-size sc))
         (locations (sc-locations sc))
         (reserve (sc-reserve-locations sc))
         (sb (sc-sb sc))
         (always-live (finite-sb-always-live-count sb))
         (possible '()))
    (flet ((color-always-live-conflict (color)
             ;; Counts, for all the offsets in the SB, the max # of
             ;; basic blocks in which that location is used by an
             ;; :always-live TN.  This measure is an approximation of
             ;; the pressure on that specific location.
             (loop for offset from color
                   repeat size
                   maximize (aref always-live offset))))
      (declare (dynamic-extent #'color-always-live-conflict))
      ;; try to pack in low-numbered locations in case of ties: their
      ;; register encoding may be smaller.
      (dolist (loc locations (schwartzian-stable-sort-list
                              (nreverse possible) #'>
                              :key #'color-always-live-conflict))
        (unless (or (and reserve (memq loc reserve)) ; common case: no reserve
                    (conflicts-in-sc tn sc loc))
          (push loc possible))))))

;; walk over vertices, precomputing as much information as possible,
;; and partitioning according to their kind.
;; Return the partition, and a hash table to map tns to vertices.
(defun prepare-vertices (vertices)
  (let (component-vertices
        global-vertices
        local-vertices
        (tn-vertex (make-hash-table)))
    (loop for i upfrom 0
          for vertex in vertices
          do (let* ((tn (vertex-tn vertex))
                    (offset (tn-offset tn))
                    (sc (tn-sc tn))
                    (locs (if offset
                              (list offset)
                              (restricted-tn-locations tn))))
               (setf (vertex-number vertex) i
                     (vertex-incidence vertex) (make-ordered-set)
                     (vertex-initial-domain vertex) locs
                     (vertex-initial-domain-size vertex) (length locs)
                     (vertex-invisible vertex) nil
                     (vertex-color vertex) (and offset
                                                (cons offset sc))
                     (gethash tn tn-vertex) vertex)
               (cond (offset) ; precolored -> no need to track conflict
                     ((eql :component (tn-kind tn))
                      (push vertex component-vertices))
                     ((tn-global-conflicts tn)
                      (push vertex global-vertices))
                     (t
                      (aver (tn-local tn))
                      (push vertex local-vertices)))))
    (values component-vertices global-vertices local-vertices
            tn-vertex)))

;; Compute conflict edges between vertices that aren't precolored:
;; precolored vertices have already been handled via domain
;; initialisation.
(defun insert-conflict-edges (component
                              component-vertices global-vertices
                              local-vertices tn-vertex)
  (declare (type list component-vertices global-vertices local-vertices)
           (type hash-table tn-vertex))
  (flet ((edge (a b)
           (declare (type vertex a b))
           (unless (or (tn-offset (vertex-tn a))  ; precolored -> conflict
                       (tn-offset (vertex-tn b))) ; implicit via domain
             (aver (oset-adjoin (vertex-incidence a) b))
             (aver (oset-adjoin (vertex-incidence b) a)))))
    ;; COMPONENT vertices conflict with everything
    (loop for (a . rest) on component-vertices
          do (dolist (b rest)
               (edge a b))
             (dolist (b global-vertices)
               (edge a b))
             (dolist (b local-vertices)
               (edge a b)))
    ;; GLOBAL vertices have more complex conflict testing
    (loop for (a . rest) on global-vertices
          for tn-a = (vertex-tn a)
          do (dolist (b rest)
               (when (tns-conflict-global-global (vertex-tn b) tn-a)
                 (edge a b)))
             (dolist (b local-vertices)
               (when (tns-conflict-local-global (vertex-tn b) tn-a)
                 (edge a b))))
    ;; LOCAL-LOCAL conflict is easy: just enumerate by IR2 block.
    (do-ir2-blocks (block component)
      (let ((local-tns (ir2-block-local-tns block))
            (n (ir2-block-local-tn-count block)))
        (dotimes (i n)
          (binding* ((a (aref local-tns i))
                     (vertex (gethash a tn-vertex) :exit-if-null)
                     (tn-local (tn-local a) :exit-if-null)
                     (conflicts (tn-local-conflicts a)))
            (unless (tn-offset a)
              (loop for j from (1+ i) below n do
                (when (plusp (sbit conflicts j))
                  (let ((b (aref local-tns j)))
                    (awhen (and (tn-local b)
                                (gethash b tn-vertex))
                      (aver (eq tn-local (tn-local b)))
                      (edge vertex it))))))))))))

;; Construct the interference graph for these vertices in the component.
;; All TNs types are included in the graph, both with offset and without,
;; but only those requiring coloring appear in the VERTICES slot.
(defun make-interference-graph (vertices component)
  (multiple-value-bind (component-vertices global-vertices local-vertices
                        tn-vertex)
      (prepare-vertices vertices)
    (insert-conflict-edges component
                           component-vertices global-vertices local-vertices
                           tn-vertex)
    ;; Normalize adjacency list ordering, and collect all uncolored
    ;; vertices in the graph.
    (collect ((colored)
              (uncolored))
      (dolist (v vertices)
        (let ((incidence (vertex-incidence v)))
          (setf (oset-members incidence)
                (sort (oset-members incidence) #'< :key #'vertex-number)))
        (cond ((vertex-color v)
               (aver (tn-offset (vertex-tn v)))
               (colored v))
              (t
               (aver (not (tn-offset (vertex-tn v))))
               (uncolored v))))
      (%make-interference-graph
       :vertices (schwartzian-stable-sort-list
                  (uncolored) #'<
                  :key (lambda (vertex)
                         (tn-spill-cost (vertex-tn vertex))))
       :precolored-vertices (colored)
       :tn-vertex tn-vertex
       :tn-vertex-mapping (lambda (tn)
                            (awhen (gethash tn tn-vertex)
                              (values (car (vertex-color it))
                                      it)))))))

;; &key reset: whether coloring/invisibility information should be
;; removed from all the remaining vertices
(defun remove-vertex-from-interference-graph (vertex graph &key reset)
  (declare (type vertex vertex) (type interference-graph graph))
  (let ((vertices (if reset
                      (loop for v in (ig-vertices graph)
                            unless (eql v vertex)
                              do (aver (not (tn-offset (vertex-tn v))))
                                 (setf (vertex-invisible v) nil
                                       (vertex-color v) nil)
                              and collect v)
                      (remove vertex (ig-vertices graph)))))
    (setf (ig-vertices graph) vertices)
    (do-oset-elements (neighbor (vertex-incidence vertex) graph)
      (oset-delete (vertex-incidence neighbor) vertex))))

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

;; Assumes that VERTEX pack-type is :WIRED.
(defun vertex-color-possible-p (vertex color)
  (declare (type integer color) (type vertex vertex))
  (and (or (and (neq (vertex-pack-type vertex) :wired)
                (not (tn-offset (vertex-tn vertex))))
           (= color (car (vertex-color vertex))))
       (memq color (vertex-initial-domain vertex))
       (not (color-conflict-p
             (cons color (vertex-sc vertex))
             (collect ((colors))
               (do-oset-elements (neighbor (vertex-incidence vertex)
                                           (colors))
                 (unless (vertex-invisible neighbor)
                   (colors (vertex-color neighbor)))))))))

;; Sorted list of all possible locations for vertex in its preferred
;; SC: more heavily loaded (i.e that should be tried first) locations
;; first.  vertex-initial-domain is already sorted, only have to
;; remove offsets that aren't currently available.
(defun vertex-domain (vertex)
  (declare (type vertex vertex))
  (remove-if-not (lambda (color)
                   (vertex-color-possible-p vertex color))
                 (vertex-initial-domain vertex)))

;; Return a list of vertices that we might want VERTEX to share its
;; location with.
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
                   (not (oset-member neighbors target)))
          (pushnew target vertices))))
    (nreverse vertices)))

;; Choose the "best" color for these vertices: a color is good if as
;; many of these vertices simultaneously take that color, and those
;; that can't have a low spill cost.
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
                               (oset-member (vertex-incidence existing)
                                            vertex))
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

;; Greedily choose the color for this vertex, also moving around any
;; :target vertex to the same color if possible.
(defun find-vertex-color (vertex tn-vertex-mapping)
  (awhen (vertex-domain vertex)
    (let* ((targets (vertex-target-vertices vertex tn-vertex-mapping))
           (sc (vertex-sc vertex))
           (sb (sc-sb sc)))
      (multiple-value-bind (color recolor-vertices)
          (if targets
              (vertices-best-color targets it)
              (values (first it) nil))
        (aver color)
        (dolist (target recolor-vertices)
          (aver (car (vertex-color target)))
          (unless (eql color (car (vertex-color target)))
            (aver (eq sb (sc-sb (vertex-sc target))))
            (aver (not (tn-offset (vertex-tn target))))
            #+nil ; this check is slow
            (aver (vertex-color-possible-p target color))
            (setf (car (vertex-color target)) color)))
        (cons color sc)))))

;; Partition vertices into those that are likely to be colored and
;; those that are likely to be spilled.  Assumes that the interference
;; graph's vertices are sorted with the least spill cost first, so
;; that the stacks end up with the greatest spill cost vertices first.
(defun partition-and-order-vertices (interference-graph)
  (flet ((domain-size (vertex)
           (vertex-initial-domain-size vertex))
         (degree (vertex)
           (count-if-not #'vertex-invisible
                         (oset-members (vertex-incidence vertex))))
         (mark-as-spill-candidate (vertex)
           (setf (vertex-spill-candidate vertex) t))
         (eliminate-vertex (vertex)
           (setf (vertex-invisible vertex) t)))
    (let* ((precoloring-stack '())
           (prespilling-stack '())
           (vertices (ig-vertices interference-graph)))
      ;; walk the vertices from least important to most important TN wrt
      ;; spill cost.  That way the TNs we really don't want to spill are
      ;; at the head of the colouring lists.
      (loop for vertex in vertices do
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

;; Try and color the interference graph once.
(defun color-interference-graph (interference-graph)
  (let ((tn-vertex (ig-tn-vertex-mapping interference-graph)))
    (flet ((color-vertices (vertices)
             (dolist (vertex vertices)
               (awhen (find-vertex-color vertex tn-vertex)
                 (setf (vertex-color vertex) it
                       (vertex-invisible vertex) nil)))))
      (multiple-value-bind (probably-colored probably-spilled)
          (partition-and-order-vertices interference-graph)
        (color-vertices probably-colored)
        ;; These might benefit from further ordering... LexBFS?
        (color-vertices probably-spilled))))
  interference-graph)

;;; Iterative spilling logic.

;; maximum number of spill iterations
(defvar *pack-iterations* 500)

;; Find the least-spill-cost neighbor in each color.

;; FIXME: this is too slow and isn't the right interface anymore.
;; The code might be fast enough if there were a simple way to detect
;; whether a given vertex is a min-candidate for another uncolored
;; vertex.
#+nil
(defun collect-min-spill-candidates (vertex)
  (let ((colors '()))
    (do-oset-elements (neighbor (vertex-incidence vertex))
      (when (eql :normal (vertex-pack-type neighbor))
        (let* ((color (car (vertex-color neighbor)))
               (cell (assoc color colors))
               (cost-neighbor (tn-spill-cost (vertex-tn neighbor))))
          (cond (cell
                 (when (< cost-neighbor (tn-spill-cost
                                         (vertex-tn (cdr cell))))
                   (setf (cdr cell) neighbor)))
                (t (push (cons color neighbor) colors))))))
    (remove nil (mapcar #'cdr colors))))

;; Try to color the graph. If some TNs are left uncolored, find a
;; spill candidate, force it on the stack, and try again.
(defun iterate-color (vertices component
                      &optional (iterations *pack-iterations*))
  (let* ((spill-list '())
         (nvertices (length vertices))
         (number-iterations (min iterations nvertices))
         (graph (make-interference-graph vertices component))
         to-spill)
    (labels ((spill-candidates-p (vertex)
               (unless (vertex-color vertex)
                 (aver (eql :normal (vertex-pack-type vertex)))
                 t))
             (iter (to-spill)
               (when to-spill
                 (setf (vertex-invisible to-spill) t
                       (vertex-color to-spill) nil)
                 (push to-spill spill-list)
                 (setf graph (remove-vertex-from-interference-graph
                              to-spill graph :reset t)))
               (color-interference-graph graph)
               (find-if #'spill-candidates-p (ig-vertices graph))))
      (loop repeat number-iterations
            while (setf to-spill (iter to-spill))))
    (let ((colored (ig-vertices graph)))
      (aver (= nvertices (+ (length spill-list) (length colored)
                            (length (ig-precolored-vertices graph)))))
      colored)))


;;; Nice interface

;; Just pack vertices that have been assigned a color.
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

;; Pack pre-allocated TNs, collect vertices, and color.
(defun pack-iterative (component 2comp optimize)
  (declare (type component component) (type ir2-component 2comp))
  (collect ((vertices))
    ;; Pack TNs that *must* be in a certain location or SC first,
    ;; but still register them in the interference graph
    (do ((tn (ir2-component-wired-tns 2comp) (tn-next tn)))
        ((null tn))
      (pack-wired-tn tn optimize)
      (vertices (make-vertex tn :wired)))
    ;; Pack restricted component TNs first: they have the longest live
    ;; ranges, might as well avoid fragmentation when trivial.
    (do ((tn (ir2-component-restricted-tns 2comp) (tn-next tn)))
        ((null tn))
      (vertices (make-vertex tn :restricted))
      (when (eq (tn-kind tn) :component)
        (pack-tn tn t optimize)))
    (do ((tn (ir2-component-restricted-tns 2comp) (tn-next tn)))
        ((null tn))
      (unless (tn-offset tn)
        (pack-tn tn t optimize)))

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
    (pack-colored (iterate-color (vertices) component)))
  nil)
