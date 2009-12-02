#!/bin/sh
set -e

# Build cross-compiler diagnostics for when changes to the backend
# cause make-target-2 to not work.

# This software is part of the SBCL system. See the README file for
# more information.

HOST_TYPE="${1:-sbcl}"

echo //HOST_TYPE=\"$HOST_TYPE\"

. ./find-after-xc-host.sh

build_test_cores() {
  # Instead of doing a full make-host-2, we use the after-xc.core to
  # avoid having to deal with the compiler-loading logic again.  This
  # also means that things like the list of object files is available.
  $LISP $CORE output/after-xc.core $INIT <<'EOF'
(in-package :sb-cold)
(host-load-stem "src/compiler/generic/genesis" nil)
(defparameter *xc-test-objects*
  (remove-if-not (lambda (name)
                   (string-equal (pathname-type name) "assem-obj"))
                 *target-object-file-names*))
(defun make-xc-test-core (stem)
  (let ((core-file (format nil "output/~A.core" stem))
        (map-file (format nil "output/~A.map" stem))
        (obj-file (target-compile-stem stem '(:trace-file :ignore-failure-p))))
    (sb!vm:genesis :object-file-names (append *xc-test-objects*
                                              (list obj-file))
                   :symbol-table-file-name "src/runtime/sbcl.nm"
                   :core-file-name core-file
                   :map-file-name map-file)))
;; This makes a test core for each lisp file in xc-tests/.
(let* ((test-files (directory "xc-tests/*.lisp"))
       (test-bases (mapcar (lambda (file)
                             (format nil "xc-tests/~A"
                                     (pathname-name file)))
                           test-files)))
  (dolist (base test-bases)
    (make-xc-test-core base)))
EOF
}

test_core() {
  output=`basename $1 .core`.output
  echo -n "running $1..."
  # We strip the line "fatal error encountered in SBCL pid" because it
  # actually does contain a pid, which varies by run and thus breaks
  # our output comparison.
  ./src/runtime/sbcl --noinform --disable-ldb --core $1 2>&1 | grep -v "fatal error encountered in SBCL pid" > output/xc-tests/$output || true
  if [ ! -e xc-tests/$output ]; then
    echo "no master output"
    touch output/xc-tests/$output.no-master
  elif diff xc-tests/$output output/xc-tests/$output > /dev/null; then
    echo "passed"
    touch output/xc-tests/$output.passed
  else
    echo "FAILED"
    touch output/xc-tests/$output.failed
  fi
}

# Clean up our test directory, so we don't have stale output lying
# around to trip us up.
rm -f output/xc-tests/*

build_test_cores

echo

for file in output/xc-tests/*.core; do
  test_core $file;
done

NTESTS=`find output/xc-tests/ -name \*.core | wc -l`
NPASSED=`find output/xc-tests/ -name \*.passed | wc -l`
NFAILED=`find output/xc-tests/ -name \*.failed | wc -l`
NNOMASTER=`find output/xc-tests/ -name \*.no-master | wc -l`
echo
echo "The cross-compiler tests appear to have completed."
echo
echo " Tests passed: $NPASSED"
echo " Tests failed: $NFAILED"
echo " Tests with no master output: $NNOMASTER"
echo " Total number of tests: $NTESTS"
echo
echo //ordinary termination of run-xc-tests.sh
