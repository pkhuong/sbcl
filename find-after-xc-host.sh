#!/bin/false
# Not a shell script, but something intended to be sourced from shell scripts

# We don't try to be general about this in this script the way we are
# in make.sh, since the idiosyncrasies of SBCL command line argument
# order dependence, the meaninglessness of duplicate --core arguments,
# and the SBCL-vs-CMUCL dependence of --core/-core argument syntax
# make it too messy to try deal with arbitrary SBCL_XC_HOST variants.
# So you have no choice:
case "$HOST_TYPE" in
    cmucl) LISP="lisp -batch"
           INIT="-noinit"
           CORE="-core"
           ;;
    sbcl)  LISP="sbcl"
           INIT="--sysinit /dev/null --userinit /dev/null"
           CORE="--core"
           ;;
    clisp) LISP="clisp"
           INIT="-norc"
           CORE="-M"
           ;;
    openmcl)
           LISP="openmcl"
           INIT="-b"
           CORE="-I"
           ;;
    *)     echo unknown host type: "$HOST_TYPE"
           echo should be one of "sbcl", "cmucl", or "clisp"
           exit 1
esac
