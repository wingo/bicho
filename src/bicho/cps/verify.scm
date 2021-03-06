;;; Diagnostic checker for CPS
;;; Copyright (C) 2014, 2015 Free Software Foundation, Inc.
;;;
;;; This library is free software: you can redistribute it and/or modify
;;; it under the terms of the GNU Lesser General Public License as
;;; published by the Free Software Foundation, either version 3 of the
;;; License, or (at your option) any later version.
;;; 
;;; This library is distributed in the hope that it will be useful, but
;;; WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;; Lesser General Public License for more details.
;;; 
;;; You should have received a copy of the GNU Lesser General Public
;;; License along with this program.  If not, see
;;; <http://www.gnu.org/licenses/>.

;;; Commentary:
;;;
;;; A routine to detect invalid CPS.
;;;
;;; Code:

(define-module (bicho cps verify)
  #:use-module (ice-9 match)
  #:use-module (bicho cps)
  #:use-module (bicho cps utils)
  #:use-module (bicho cps intmap)
  #:use-module (bicho cps intset)
  #:use-module (bicho cps primitives)
  #:use-module (srfi srfi-11)
  #:export (verify))

(define (intset-pop set)
  (match (intset-next set)
    (#f (values set #f))
    (i (values (intset-remove set i) i))))

(define-syntax-rule (make-worklist-folder* seed ...)
  (lambda (f worklist seed ...)
    (let lp ((worklist worklist) (seed seed) ...)
      (call-with-values (lambda () (intset-pop worklist))
        (lambda (worklist i)
          (if i
              (call-with-values (lambda () (f i seed ...))
                (lambda (i* seed ...)
                  (let add ((i* i*) (worklist worklist))
                    (match i*
                      (() (lp worklist seed ...))
                      ((i . i*) (add i* (intset-add worklist i)))))))
              (values seed ...)))))))

(define worklist-fold*
  (case-lambda
    ((f worklist seed)
     ((make-worklist-folder* seed) f worklist seed))))

(define (check-distinct-vars conts)
  (define (adjoin-def var seen)
    (when (intset-ref seen var)
      (error "duplicate var name" seen var))
    (intset-add seen var))
  (intmap-fold
   (lambda (label cont seen)
     (match (intmap-ref conts label)
       (($ $kargs names vars ($ $continue k src exp))
        (fold1 adjoin-def vars seen))
       (($ $kfun src meta self tail clause)
        (adjoin-def self seen))
       (_ seen))
     )
   conts
   empty-intset))

(define (compute-available-definitions conts kfun)
  "Compute and return a map of LABEL->VAR..., where VAR... are the
definitions that are available at LABEL."
  (define (adjoin-def var defs)
    (when (intset-ref defs var)
      (error "var already present in defs" defs var))
    (intset-add defs var))

  (define (propagate defs succ out)
    (let* ((in (intmap-ref defs succ (lambda (_) #f)))
           (in* (if in (intset-intersect in out) out)))
      (if (eq? in in*)
          (values '() defs)
          (values (list succ)
                  (intmap-add defs succ in* (lambda (old new) new))))))

  (define (visit-cont label defs)
    (let ((in (intmap-ref defs label)))
      (define (propagate0 out)
        (values '() defs))
      (define (propagate1 succ out)
        (propagate defs succ out))
      (define (propagate2 succ0 succ1 out)
        (let*-values (((changed0 defs) (propagate defs succ0 out))
                      ((changed1 defs) (propagate defs succ1 out)))
          (values (append changed0 changed1) defs)))

      (match (intmap-ref conts label)
        (($ $kargs names vars ($ $continue k src exp))
         (let ((out (fold1 adjoin-def vars in)))
           (match exp
             (($ $branch kt) (propagate2 k kt out))
             (($ $prompt escape? tag handler) (propagate2 k handler out))
             (_ (propagate1 k out)))))
        (($ $kreceive arity k)
         (propagate1 k in))
        (($ $kfun src meta self tail clause)
         (let ((out (adjoin-def self in)))
           (if clause
               (propagate1 clause out)
               (propagate0 out))))
        (($ $kclause arity kbody kalt)
         (if kalt
             (propagate2 kbody kalt in)
             (propagate1 kbody in)))
        (($ $ktail) (propagate0 in)))))

  (worklist-fold* visit-cont
                  (intset kfun)
                  (intmap-add empty-intmap kfun empty-intset)))

(define (intmap-for-each f map)
  (intmap-fold (lambda (k v seed) (f k v) seed) map *unspecified*))

(define (check-valid-var-uses conts kfun)
  (define (adjoin-def var defs) (intset-add defs var))
  (let visit-fun ((kfun kfun) (free empty-intset))
    (define (visit-exp exp bound)
      (define (check-use var)
        (unless (intset-ref bound var)
          (error "unbound var" var)))
      (match exp
        ((or ($ $const) ($ $prim)) #t)
        ;; todo: $closure
        (($ $fun kfun)
         (visit-fun kfun bound))
        (($ $rec names vars (($ $fun kfuns) ...))
         (let ((bound (fold1 adjoin-def vars bound)))
           (for-each (lambda (kfun) (visit-fun kfun bound)) kfuns)))
        (($ $values args)
         (for-each check-use args))
        (($ $call proc args)
         (check-use proc)
         (for-each check-use args))
        (($ $callk k proc args)
         (check-use proc)
         (for-each check-use args))
        (($ $branch kt ($ $values (arg)))
         (check-use arg))
        (($ $branch kt ($ $primcall name args))
         (for-each check-use args))
        (($ $primcall name args)
         (for-each check-use args))
        (($ $prompt escape? tag handler)
         (check-use tag))))
    (intmap-for-each
     (lambda (label bound)
       (let ((bound (intset-union free bound)))
         (match (intmap-ref conts label)
           (($ $kargs names vars ($ $continue k src exp))
            (visit-exp exp (fold1 adjoin-def vars bound)))
           (_ #t))))
     (compute-available-definitions conts kfun))))

(define (fold-nested-funs f conts kfun seed)
  (intset-fold
   (lambda (label seed)
     (match (intmap-ref conts label)
       (($ $kargs _ _ ($ $continue _ _ ($ $fun label)))
        (f label seed))
       (($ $kargs _ _ ($ $continue _ _ ($ $rec _ _ (($ $fun label) ...))))
        (fold1 f label seed))
       (_ seed)))
   (compute-function-body conts kfun)
   seed))

(define (check-label-partition conts kfun)
  ;; A continuation can only belong to one function.
  (let visit-fun ((kfun kfun) (seen empty-intmap))
    (fold-nested-funs
     visit-fun
     conts
     kfun
     (intset-fold
      (lambda (label seen)
        (intmap-add seen label kfun
                    (lambda (old new)
                      (error "label used by two functions" label old new))))
      (compute-function-body conts kfun)
      seen))))

(define (compute-reachable-labels conts kfun)
  (let visit-fun ((kfun kfun) (seen empty-intset))
    (fold-nested-funs visit-fun conts kfun
                      (intset-union seen (compute-function-body conts kfun)))))

(define (check-arities conts kfun)
  (define (check-arity exp cont)
    (define (assert-unary)
      (match cont
        (($ $kargs (_) (_)) #t)
        (_ (error "expected unary continuation" cont))))
    (define (assert-nullary)
      (match cont
        (($ $kargs () ()) #t)
        (_ (error "expected unary continuation" cont))))
    (define (assert-n-ary n)
      (match cont
        (($ $kargs names vars)
         (unless (= (length vars) n)
           (error "expected n-ary continuation" n cont)))
        (_ (error "expected $kargs continuation" cont))))
    (define (assert-kreceive-or-ktail)
      (match cont
        ((or ($ $kreceive) ($ $ktail)) #t)
        (_ (error "expected $kreceive or $ktail continuation" cont))))
    (match exp
      ((or ($ $const) ($ $prim) ($ $closure) ($ $fun))
       (assert-unary))
      (($ $rec names vars funs)
       (unless (= (length names) (length vars) (length funs))
         (error "invalid $rec" exp))
       (assert-n-ary (length names))
       (match cont
         (($ $kargs names vars*)
          (unless (equal? vars* vars)
            (error "bound variable mismatch" vars vars*)))))
      (($ $values args)
       (match cont
         (($ $ktail) #t)
         (_ (assert-n-ary (length args)))))
      (($ $call proc args)
       (assert-kreceive-or-ktail))
      (($ $callk k proc args)
       (assert-kreceive-or-ktail))
      (($ $branch kt exp)
       (assert-nullary)
       (match (intmap-ref conts kt)
         (($ $kargs () ()) #t)
         (cont (error "bad kt" cont))))
      (($ $primcall name args)
       (match cont
         (($ $kargs names)
          (match (prim-arity name)
            ((out . in)
             (unless (= in (length args))
               (error "bad arity to primcall" name args in))
             (unless (= out (length names))
               (error "bad return arity from primcall" name names out)))))
         (($ $kreceive)
          (when (false-if-exception (prim-arity name))
            (error "primitive should continue to $kargs, not $kreceive" name)))
         (($ $ktail)
          (unless (eq? name 'return)
            (when (false-if-exception (prim-arity name))
              (error "primitive should continue to $kargs, not $ktail" name))))))
      (($ $prompt escape? tag handler)
       (assert-nullary)
       (match (intmap-ref conts handler)
         (($ $kreceive) #t)
         (cont (error "bad handler" cont))))))
  (let ((reachable (compute-reachable-labels conts kfun)))
    (intmap-for-each
     (lambda (label cont)
       (when (intset-ref reachable label)
         (match cont
           (($ $kargs names vars ($ $continue k src exp))
            (unless (= (length names) (length vars))
              (error "broken $kargs" label names vars))
            (check-arity exp (intmap-ref conts k)))
           (_ #t))))
     conts)))

(define (check-functions-bound-once conts kfun)
  (let ((reachable (compute-reachable-labels conts kfun)))
    (define (add-fun fun functions)
      (when (intset-ref functions fun)
        (error "function already bound" fun))
      (intset-add functions fun))
    (intmap-fold
     (lambda (label cont functions)
       (if (intset-ref reachable label)
           (match cont
             (($ $kargs _ _ ($ $continue _ _ ($ $fun kfun)))
              (add-fun kfun functions))
             (($ $kargs _ _ ($ $continue _ _ ($ $rec _ _ (($ $fun kfuns) ...))))
              (fold1 add-fun kfuns functions))
             (_ functions))
           functions))
     conts
     empty-intset)))

(define (verify conts)
  (check-distinct-vars conts)
  (check-label-partition conts 0)
  (check-valid-var-uses conts 0)
  (check-arities conts 0)
  (check-functions-bound-once conts 0)
  conts)
