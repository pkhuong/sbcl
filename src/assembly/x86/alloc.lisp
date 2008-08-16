;;;; allocating simple objects

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!VM")

;;;; Signed and unsigned bignums from word-sized integers. Argument
;;;; and return in the same register. No VOPs, as these are only used
;;;; as out-of-line versions: MOVE-FROM-[UN]SIGNED VOPs handle the
;;;; fixnum cases inline.

;;; #+SB-ASSEMBLING as we don't need VOPS, just the asm routines:
;;; these are out-of-line versions called by VOPs.

#+sb-assembling
(macrolet ((def (reg)
             (let ((tn (symbolicate reg "-TN")))
               `(define-assembly-routine (,(symbolicate "ALLOC-SIGNED-BIGNUM-IN-" reg)) ()
                  (inst push ,tn)
                  (with-fixed-allocation (,tn bignum-widetag (+ bignum-digits-offset 1))
                    (popw ,tn bignum-digits-offset other-pointer-lowtag))
                  (inst ret)))))
  (def eax)
  (def ebx)
  (def ecx)
  (def edx)
  (def edi)
  (def esi))

#+sb-assembling
(macrolet ((def (reg)
             (let ((tn (symbolicate reg "-TN")))
               `(define-assembly-routine (,(symbolicate "ALLOC-UNSIGNED-BIGNUM-IN-" reg)) ()
                  (inst push ,tn)
                  ;; Sign flag is set by the caller! Note: The inline
                  ;; version always allocates space for two words, but
                  ;; here we minimize garbage.
                  (inst jmp :ns one-word-bignum)
                  ;; Two word bignum
                  (with-fixed-allocation (,tn bignum-widetag (+ bignum-digits-offset 2))
                    (popw ,tn bignum-digits-offset other-pointer-lowtag))
                  (inst ret)
                  ONE-WORD-BIGNUM
                  (with-fixed-allocation (,tn bignum-widetag (+ bignum-digits-offset 1))
                    (popw ,tn bignum-digits-offset other-pointer-lowtag))
                  (inst ret)))))
  (def eax)
  (def ebx)
  (def ecx)
  (def edx)
  (def edi)
  (def esi))

;;; FIXME: This is dead, right? Can it go?
#+sb-assembling
(defun frob-allocation-assembly-routine (obj lowtag arg-tn)
  `(define-assembly-routine (,(intern (format nil "ALLOCATE-~A-TO-~A" obj arg-tn)))
     ((:temp ,arg-tn descriptor-reg ,(intern (format nil "~A-OFFSET" arg-tn))))
     (pseudo-atomic
      (allocation ,arg-tn (pad-data-block ,(intern (format nil "~A-SIZE" obj))))
      (inst lea ,arg-tn (make-ea :byte :base ,arg-tn :disp ,lowtag)))
     (inst ret)))

#+sb-assembling
(macrolet ((frob-cons-routines ()
             (let ((routines nil))
               (dolist (tn-offset *dword-regs*
                        `(progn ,@routines))
                 (push (frob-allocation-assembly-routine 'cons
                                                         list-pointer-lowtag
                                                         (intern (aref *dword-register-names* tn-offset)))
                       routines)))))
  (frob-cons-routines))

#+sb-assembling
(macrolet
    ((def (reg)
       (declare (ignorable reg))
       #!+sb-thread
       (let* ((name (intern (format nil "ALLOC-TLS-INDEX-IN-~A" reg)))
              (target-offset (intern (format nil "~A-OFFSET" reg)))
              (other-offset (if (eql 'eax reg)
                                'ecx-offset
                                'eax-offset)))
         ;; Symbol starts in TARGET, where the TLS-INDEX ends up in.
         `(define-assembly-routine ,name
              ((:temp other descriptor-reg ,other-offset)
               (:temp target descriptor-reg ,target-offset))
            (let ((get-tls-index-lock (gen-label))
                  (release-tls-index-lock (gen-label))
                  (alloc-new-tls-index (gen-label))
                  (store-tls-index (gen-label)))
              (pseudo-atomic
               ;; Save OTHER & push the symbol. EAX is either one of the two.
               (inst push other)
               (inst push target)
               (emit-label get-tls-index-lock)
               (inst mov target 1)
               (inst xor eax-tn eax-tn)
               (inst lock)
               (inst cmpxchg (make-ea-for-symbol-value *tls-index-lock*) target)
               (inst jmp :ne get-tls-index-lock)
               ;; The symbol is now in OTHER.
               (inst mov other (make-ea :dword :base esp-tn))
               ;; Now with the lock held, see if the symbol's tls index has been
               ;; set in the meantime.
               (loadw target other symbol-tls-index-slot other-pointer-lowtag)
               (inst or target target)
               (inst jmp :ne release-tls-index-lock)
               ;; try and get a tls-index from the free list
               (load-symbol-value target *tls-index-free-list*)
               (inst cmp target nil-value)
               (inst jmp :e alloc-new-tls-index)
               ;; pop the index in TARGET
               (loadw other target cons-cdr-slot list-pointer-lowtag)
               (loadw target target cons-car-slot list-pointer-lowtag)
               (store-symbol-value other *tls-index-free-list*)
               ;; and restore OTHER to the symbol
               (inst mov other (make-ea :dword :base esp-tn))
               (inst jmp store-tls-index)

               ;; Allocate a new tls-index.
               (emit-label alloc-new-tls-index)
               (load-symbol-value target *free-tls-index*)
               (let ((error (generate-error-code nil 'tls-exhausted-error)))
                 (inst cmp target (fixnumize tls-size))
                 (inst jmp :ge error))
               (inst add (make-ea-for-symbol-value *free-tls-index*)
                     (fixnumize 1))

               ;; finally store the tls index in the symbol
               ;; and in the table
               (emit-label store-tls-index)
               (storew target other symbol-tls-index-slot other-pointer-lowtag)
               (let ((table-allocated (gen-label)))
                 (load-symbol-value other *tls-index-symbol-table*)
                 (inst test other other)
                 (inst jmp :nz table-allocated)
                 (allocation other (* n-word-bytes (+ 2 tls-size)) nil nil other-pointer-lowtag)
                 (storew simple-array-unsigned-byte-32-widetag other 0 other-pointer-lowtag)
                 (storew (fixnumize tls-size) other vector-length-slot other-pointer-lowtag)
                 (store-symbol-value other *tls-index-symbol-table*)
                 (emit-label table-allocated))

               (emit-label release-tls-index-lock)
               (load-symbol-value other *tls-index-symbol-table*)
               (inst add other (- (* n-word-bytes vector-data-offset) other-pointer-lowtag))
               (inst add other target)
               (inst pop (make-ea :dword :base other))
               (store-symbol-value 0 *tls-index-lock*)
               ;; Restore OTHER.
               (inst pop other))
              (inst ret))))))
  (def eax)
  (def ebx)
  (def ecx)
  (def edx)
  (def edi)
  (def esi))
