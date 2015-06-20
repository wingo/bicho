;;; Continuation-passing style (CPS) intermediate language (IL)

;; Copyright (C) 2013, 2014, 2015 Free Software Foundation, Inc.

;;;; This library is free software; you can redistribute it and/or
;;;; modify it under the terms of the GNU Lesser General Public
;;;; License as published by the Free Software Foundation; either
;;;; version 3 of the License, or (at your option) any later version.
;;;;
;;;; This library is distributed in the hope that it will be useful,
;;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;;; Lesser General Public License for more details.
;;;;
;;;; You should have received a copy of the GNU Lesser General Public
;;;; License along with this library; if not, write to the Free Software
;;;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

;;; Commentary:
;;;
;;; This pass converts a CPS term in such a way that no function has any
;;; free variables.  Instead, closures are built explicitly with
;;; make-closure primcalls, and free variables are referenced through
;;; the closure.
;;;
;;; Closure conversion also removes any $rec expressions that
;;; contification did not handle.  See (bicho cps) for a further
;;; discussion of $rec.
;;;
;;; Code:

(define-module (bicho cps closure-conversion)
  #:use-module (ice-9 match)
  #:use-module ((srfi srfi-1) #:select (fold
                                        filter-map
                                        ))
  #:use-module (bicho cps utils)
  #:use-module (bicho cps with-cps)
  #:use-module (bicho cps intmap)
  #:use-module (bicho cps intset)
  #:export (convert-closures))

;; free := var ...

(define-record-type <closure>
  (make-closure body bound-vars free-vars well-known? rec-conts)
  closure?
  (body closure-body)
  (bound-vars closure-bound-vars)
  (free-vars closure-free-vars)
  (well-known? closure-well-known? set-closure-well-known!)
  (rec-conts closure-rec-conts))

(define (compute-function-bodies conts kfun)
  "Compute a map from FUN-LABEL->BODY-LABEL... for all $fun instances in
conts."
  (let visit-fun ((kfun kfun) (out empty-intmap))
    (let ((body (compute-function-body conts kfun)))
      (intset-fold
       (lambda (label out)
         (match (intmap-ref conts label)
           (($ $kargs _ _ ($ $continue _ _ ($ $fun kfun)))
            (visit-fun kfun out))
           (($ $kargs _ _ ($ $continue _ _ ($ $rec _ _ (($ $fun kfun) ...))))
            (fold visit-fun out kfun))
           (_ out)))
       body
       (intmap-add out kfun body)))))

(define (compute-program-body functions)
  (intmap-fold (lambda (label body out) (intset-union body out))
               functions
               empty-intset))

(define (filter-reachable conts functions)
  (let ((reachable (compute-program-body functions)))
    (persistent-intmap
     (intmap-fold
      (lambda (label cont out)
        (if (intset-ref reachable label)
            out
            (intmap-remove! out label)))
      conts conts))))

(define (compute-non-operator-uses conts)
  (persistent-intset
   (intmap-fold
    (lambda (label cont uses)
      (define (add-use var uses) (intset-add! uses var))
      (define (add-uses vars uses)
        (match vars
          (() uses)
          ((var . vars) (add-uses vars (add-use var uses)))))
      (match cont
        (($ $kargs _ _ ($ $continue _ _ exp))
         (match exp
           ((or ($ $const) ($ $prim) ($ $fun) ($ $rec)) uses)
           (($ $values args)
            (add-uses args uses))
           (($ $call proc args)
            (add-uses args uses))
           (($ $branch kt ($ $values (arg)))
            (add-use arg uses))
           (($ $branch kt ($ $primcall name args))
            (add-uses args uses))
           (($ $primcall name args)
            (add-uses args uses))
           (($ $prompt escape? tag handler)
            (add-use tag uses))))
        (_ uses)))
    conts
    empty-intset)))

(define (compute-function-names conts functions)
  "Compute a map of FUN-LABEL->BOUND-VAR... for each labelled function
whose bound vars we know."
  (define (add-named-fun var kfun out)
    (let ((self (match (intmap-ref conts kfun)
                  (($ $kfun src meta self) self))))
      (intmap-add out kfun (intset var self))))
  (intmap-fold
   (lambda (label body out)
     (let ((single (compute-singly-referenced-labels conts label)))
       (intset-fold
        (lambda (label out)
          (match (intmap-ref conts label)
            (($ $kargs _ _ ($ $continue k _ ($ $fun kfun)))
             (if (intset-ref single k)
                 (match (intmap-ref conts k)
                   (($ $kargs (_) (var)) (add-named-fun var kfun out))
                   (_ out))
                 out))
            (($ $kargs _ _ ($ $continue k _ ($ $rec _ vars (($ $fun kfun) ...))))
             (unless (intset-ref single k)
               (error "$rec continuation has multiple predecessors??"))
             (fold add-named-fun out vars kfun))
            (_ out)))
        body
        out)))
   functions
   empty-intmap))

(define (compute-well-known-functions conts functions bound->label)
  "Compute a set of labels indicating the well-known functions in
@var{conts}.  A well-known function is a function whose bound names we
know and which is never used in a non-operator position."
  (persistent-intset
   (intset-fold (lambda (bound out)
                  (intset-add! out (intmap-ref bound->label boung)))
                (intset-subtract (intmap-keys bound->label)
                                 (compute-non-operator-uses conts))
                empty-intset)))

(define (compute-shared-closures conts well-known)
  "Compute a map LABEL->VAR indicating the sets of functions that will
share a closure.  If a functions's label is in the map, it is shared.
The entries indicate the var of the shared closure, which will be one of
the bound vars of the closure."
  (intmap-fold
   (lambda (label cont out)
     (($ $kargs _ _ ($ $continue _ _ ($ $rec names vars (($ $fun kfuns) ...))))
      ;; The split-rec pass should have ensured that this $rec forms a
      ;; strongly-connected component, so the free variables from all of
      ;; the functions will be alive as long as one of the closures is
      ;; alive.  For that reason we can consider storing all free
      ;; variables in one closure and sharing it.
      (let* ((kfuns-set (fold intset-cons empty-intset kfuns))
             (unknown-kfuns (intset-subtract kfuns-set well-known)))
        (cond
         ((or (eq? empty-intset kfuns-set) (trivial-intset kfuns-set))
          ;; There is only zero or one function bound here.  Trivially
          ;; shared already.
          out)
         ((eq? empty-intset unknown-kfuns)
          ;; All functions are well-known; we can share a closure.  Use
          ;; the first bound variable.
          (let ((closure (car vars)))
            (intset-fold (lambda (kfun out)
                           (intmap-add out kfun closure))
                         kfuns out)))
         ((trivial-intset unknown-kfuns)
          => (lambda (closure)
               ;; Only one function is not-well-known.  Use that
               ;; function's closure as the shared closure.
               (intset-fold (lambda (kfun out)
                              (intmap-add out kfun closure))
                            kfuns out)))
         (else
          ;; More than one not-well-known function means we need more
          ;; than one proper closure, so we can't share.
          out)))))
   conts
   empty-intmap))

(define* (rewrite-shared-closure-calls cps functions label->bound shared kfun)
  "Rewrite CPS such that every call to a function with a shared closure
instead is a $callk to that label, but passing the shared closure as the
proc argument.  For recursive calls, use the appropriate 'self'
variable, if possible.  Also rewrite uses of the non-well-known but
shared closures to use the appropriate 'self' variable, if possible."
  ;; env := var -> (var . label)
  (define (rewrite-fun kfun cps env)
    (define (subst var)
      (match (intmap-ref env var (lambda (_) #f))
        (#f var)
        ((var . label) var)))

    (define (rename-exp label cps names vars k src exp)
      (let ((exp (rewrite-exp exp
                   ((or ($ $const) ($ $prim)) ,exp)
                   (($ $call proc args)
                    ,(let ((args (map subst args)))
                       (rewrite-exp (intmap-ref env var (lambda (_) #f))
                         (#f ($call proc ,args))
                         ((closure . label) ($callk label closure ,args)))))
                   (($ $callk k proc args)
                    ($callk k (subst proc) ,(map subst args)))
                   (($ $primcall name args)
                    ($primcall name ,(map subst args)))
                   (($ $branch k ($ $values (arg)))
                    ($branch k ($values ((subst arg)))))
                   (($ $branch k ($ $primcall name args))
                    ($branch k ($primcall name ,(map subst args))))
                   (($ $values args)
                    ($values ,(map subst args)))
                   (($ $prompt escape? tag handler)
                    ($prompt escape? (subst tag) handler)))))
        (intmap-replace! cps label
                         (build-cont
                           ($kargs names vars ($continue k src ,exp))))))

    (define (visit-exp label cps names vars k src exp)
      (define (compute-env label self rec-labels env)
        (define (add-bound-vars label env)
          (intset-fold (lambda (var env)
                         (if (eqv? var self)
                             env
                             (intmap-add env var (cons self label)
                                         (lambda (old new) new))))
                       (intmap-ref label->bound label)
                       env))
        (if (intmap-ref shared label (lambda (_) #f))
            ;; Within a function with a shared closure, rewrite
            ;; references to bound vars to use the "self" var.
            (fold add-bound-vars env rec-labels)
            ;; Otherwise be sure to use "self" references in any
            ;; closure.
            (add-bound-vars label env)))
      (match exp
        (($ $fun label)
         (rewrite-fun label cps env))
        (($ $rec names vars (($ $fun labels) ...))
         (fold (lambda (label cps)
                 (match (intmap-ref cps label)
                   (($ $kfun src meta self)
                    (rewrite-fun label cps
                                 (compute-env label self labels env)))))
               cps labels))
        (_ (rename-exp label cps names vars k src exp))))
    
    (define (rewrite-cont label cps)
      (match (intmap-ref cps label)
        (($ $kargs names vars ($ $continue k src exp))
         (visit-exp label cps names vars k src exp))
        (_ cps)))

    (intset-fold rewrite-cont (intmap-ref functions kfun) cps env))

  ;; Initial environment is bound-var -> (shared-var . label) map for
  ;; functions with shared closures.
  (let ((env (intmap-fold (lambda (label shared env)
                            (intset-fold (lambda (bound env)
                                           (intmap-add env bound
                                                       (cons shared label)))
                                         (intmap-ref function-names label)
                                         env))
                          shared
                          empty-intmap)))
    (persistent-intmap (rewrite-fun kfun cps env))))

(define (compute-free-vars conts kfun shared)
  "Compute a FUN-LABEL->FREE-VAR... map describing all free variable
references."
  (define (add-def var defs) (intset-add! defs var))
  (define (add-defs vars defs)
    (match vars
      (() defs)
      ((var . vars) (add-defs vars (add-def var defs)))))
  (define (add-use var uses) (intset-add! uses var))
  (define (add-uses vars uses)
    (match vars
      (() uses)
      ((var . vars) (add-uses vars (add-use var uses)))))
  (define (visit-nested-funs body)
    (intset-fold
     (lambda (label out)
       (match (intmap-ref conts label)
         (($ $kargs _ _ ($ $continue _ _
                           ($ $fun kfun)))
          (intmap-union out (visit-fun kfun)))
         (($ $kargs _ _ ($ $continue _ _
                           ($ $rec _ _ (($ $fun labels) ...))))
          (let* ((out (fold (lambda (kfun out)
                              (intmap-union out (visit-fun kfun)))
                            out labels))
                 (free (fold (lambda (kfun free)
                               (intmap-union free (intmap-ref out kfun)))
                             empty-intset labels)))
            (fold (lambda (kfun out)
                    ;; For functions that share a closure, the free
                    ;; variables for one will be the union of the free
                    ;; variables for all.
                    (if (intmap-ref shared kfun (lambda (_) #f))
                        (intmap-replace out kfun free)
                        out))
                  labels)))
         (_ out)))
     body
     empty-intmap))
  (define (visit-fun kfun)
    (let* ((body (compute-function-body conts kfun))
           (free (visit-nested-funs body)))
      (call-with-values
          (lambda ()
            (intset-fold
             (lambda (label defs uses)
               (match (intmap-ref conts label)
                 (($ $kargs names vars ($ $continue k src exp))
                  (values
                   (add-defs vars defs)
                   (match exp
                     ((or ($ $const) ($ $prim)) uses)
                     (($ $fun kfun)
                      (intset-union (persistent-intset uses)
                                    (intmap-ref free kfun)))
                     (($ $rec names vars (($ $fun kfun) ...))
                      (fold (lambda (kfun uses)
                              (intset-union (persistent-intset uses)
                                            (intmap-ref free kfun)))
                            uses kfun))
                     (($ $values args)
                      (add-uses args uses))
                     (($ $call proc args)
                      (add-use proc (add-uses args uses)))
                     (($ $callk label proc args)
                      (add-use proc (add-uses args uses)))
                     (($ $branch kt ($ $values (arg)))
                      (add-use arg uses))
                     (($ $branch kt ($ $primcall name args))
                      (add-uses args uses))
                     (($ $primcall name args)
                      (add-uses args uses))
                     (($ $prompt escape? tag handler)
                      (add-use tag uses)))))
                 (($ $kfun src meta self)
                  (values (add-def self defs) uses))
                 (_ (values defs uses))))
             body empty-intset empty-intset))
        (lambda (defs uses)
          (intmap-add free kfun (intset-subtract
                                 (persistent-intset uses)
                                 (persistent-intset defs)))))))
  (visit-fun kfun))

(define (eliminate-closure? label free-vars)
  (eq? (intmap-ref free-vars label) empty-intset))

(define (closure-alias label well-known free-vars)
  (and (intset-ref well-known label)
       (trivial-intset (intmap-ref free-vars label))))

(define (prune-free-vars free-vars bound->label well-known)
  "Given the label->bound-var map @var{free-vars}, remove free variables
that are well-known functions with zero free variables, and replace
references to well-known functions with one free variable with that free
variable, until we reach a fixed point on the free-vars map."
  (define (prune-free free free-vars)
    (intset-fold (lambda (var free)
                   (match (intmap-ref bound->label var (lambda (_) #f))
                     (#f free)
                     (label
                      (cond
                       ((eliminate-closure? label free-vars)
                        (intset-remove var free))
                       ((closure-alias label well-known free-vars)
                        => (lambda (alias)
                             ;; If VAR is free in LABEL, then ALIAS must
                             ;; also be free because its definition must
                             ;; precede VAR's definition.
                             (intset-add (intset-remove free var) alias)))
                       (else free)))))
                 free free))
  (fixpoint (lambda (free-vars)
              (intmap-fold (lambda (label free free-vars)
                             (intmap-replace free-vars label
                                             (prune-free free free-vars)))
                           free-vars
                           free-vars))
            free-vars))

(define (intset-find set i)
  (let lp ((idx 0) (start #f))
    (let ((start (intset-next set start)))
      (cond
       ((not start) (error "not found" set i))
       ((= start i) idx)
       (else (lp (1+ idx) (1+ start)))))))

(define (intmap-select map set)
  (persistent-intmap
   (intmap-fold
    (lambda (k v out)
      (if (intset-ref set k)
          (intmap-add! out k v)
          out))
    map
    empty-intmap)))

(define (intset-count set)
  (intset-fold (lambda (_ count) (1+ count)) set 0))

(define (convert-one cps label body free-vars bound->label well-known shared)
  (define (well-known? label)
    (intset-ref well-known label))

  (let* ((free (intmap-ref free-vars label))
         (nfree (intset-count free))
         (self-known? (well-known? label))
         (self (match fun (($ $kfun _ _ self) self)))
         #;
         (bound (trivial-intset
                 (intset-remove (intmap-ref fun-names label) self)))
         )
    (define (convert-arg cps var k)
      "Convert one possibly free variable reference to a bound reference.

If @var{var} is free, it is replaced by a closure reference via a
@code{free-ref} primcall, and @var{k} is called with the new var.
Otherwise @var{var} is bound, so @var{k} is called with @var{var}."
      ;; We know that var is not the name of a well-known function.
      (cond
       ((intset-ref free var)
        (match (vector self-known? nfree)
          (#(#t 1)
           ;; A reference to the one free var of a well-known function.
           (with-cps cps
             ($ (k self))))
          (#(#t 2)
           ;; A reference to one of the two free vars in a well-known
           ;; function.
           (let ((op (if (= var (intset-next free)) 'car 'cdr)))
             (with-cps cps
               (letv var*)
               (let$ body (k var))
               (letk k* ($kargs (#f) (var*) ,body))
               (build-term ($continue k* #f ($primcall op (self)))))))
          (_
           (let* ((idx (intset-find free var))
                  (op (cond
                       ((not self-known?) 'free-ref)
                       ((<= idx #xff) 'vector-ref/immediate)
                       (else 'vector-ref))))
             (with-cps cps
               (letv var*)
               (let$ body (k var))
               (letk k* ($kargs (#f) (var*) ,body))
               ($ (with-cps-constants ((idx idx))
                    (build-term
                      ($continue k* #f ($primcall op (self idx)))))))))))
       (else
        (with-cps cps
          ($ (k var))))))
  
    (define (convert-args cps vars k)
      "Convert a number of possibly free references to bound references.
@var{k} is called with the bound references, and should return the
term."
      (match vars
        (()
         (with-cps cps
           ($ (k '()))))
        ((var . vars)
         (convert-arg cps var
           (lambda (cps var)
             (convert-args cps vars
               (lambda (cps vars)
                 (with-cps cps
                   ($ (k (cons var vars)))))))))))
  
    (define (allocate-closure cps k src label known? nfree)
      "Allocate a new closure, and pass it to $var{k}."
      (match (vector known? nfree)
        (#(#f nfree)
         ;; The call sites cannot be enumerated; allocate a closure.
         (with-cps cps
           (build-term ($continue k src ($closure label nfree)))))
        (#(#t 2)
         ;; Well-known closure with two free variables; the closure is a
         ;; pair.
         (with-cps cps
           (let$ body (make-body))
           (letk kinit ($kargs (name) (var) ,body))
           ($ (with-cps-constants ((false #f))
                (build-term
                  ($continue kinit src ($primcall 'cons (false false))))))))
        ;; Well-known callee with more than two free variables; the closure
        ;; is a vector.
        (#(#t nfree)
         (unless (> nfree 2)
           (error "unexpeced well-known nullary, unary, or binary closure"))
         (let ((op (if (<= nfree #xff) 'make-vector/immediate 'make-vector)))
           (with-cps cps
             (let$ body (make-body))
             (letk kinit ($kargs (name) (var) ,body))
             ($ (with-cps-constants ((nfree nfree)
                                     (false #f))
                  (build-term
                    ($continue kinit src ($primcall op (nfree false)))))))))))

    (define (init-closure cps k src var known? nfree free)
      "Initialize the free variables @var{closure-free} in a closure
bound to @var{var}, and continue to @var{k}."
      (match (cons known? closure-free)
        ;; Well-known callee with no free variables; no initialization
        ;; necessary.
        ((#t) body)
        ;; Well-known callee with one free variable; no initialization
        ;; necessary.
        ((#t _) body)
        ;; Well-known callee with two free variables; do a set-car! and
        ;; set-cdr!.
        ((#t v0 v1)
         (let-fresh (kcar kcdr) ()
           (convert-arg
               v0
               (lambda (v0)
                 (build-cps-term
                   ($letk ((kcar ($kargs () ()
                                   ,(convert-arg
                                        v1
                                        (lambda (v1)
                                          (build-cps-term
                                            ($letk ((kcdr ($kargs () () ,body)))
                                              ($continue kcdr src
                                                ($primcall 'set-cdr! (var v1))))))))))
                     ($continue kcar src
                       ($primcall 'set-car! (var v0)))))))))
        ;; Otherwise residualize a sequence of vector-set! or free-set!,
        ;; depending on whether the callee is well-known or not.
        (_
         (fold (lambda (free idx body)
                 (let-fresh (k) (idxvar)
                   (build-cps-term
                     ($letk ((k ($kargs () () ,body)))
                       ,(convert-arg
                            free
                            (lambda (free)
                              (build-cps-term
                                ($letconst (('idx idxvar idx))
                                  ($continue k src
                                    ($primcall (cond
                                                ((not known?) 'free-set!)
                                                ((<= idx #xff) 'vector-set!/immediate)
                                                (else 'vector-set!))
                                               (var idxvar free)))))))))))
               body
               closure-free
               (iota (length closure-free))))))

    ;; Load the closure for a known call.  The callee may or may not be
    ;; known at all call sites.
    (define (convert-known-proc-call var label self self-known? free k)
      ;; Well-known closures with one free variable are replaced at their
      ;; use sites by uses of the one free variable.  The use sites of a
      ;; well-known closures are only in well-known proc calls, and in
      ;; free lists of other closures.  Here we handle the call case; the
      ;; free list case is handled by prune-free-vars.
      (define (rename var)
        (let ((var* (vector-ref aliases var)))
          (if var*
              (rename var*)
              var)))
      (match (cons (well-known? label)
                   (hashq-ref free-vars label))
        ((#t)
         ;; Calling a well-known procedure with no free variables; pass #f
         ;; as the closure.
         (let-fresh (k*) (v*)
           (build-cps-term
             ($letk ((k* ($kargs (v*) (v*) ,(k v*))))
               ($continue k* #f ($const #f))))))
        ((#t _)
         ;; Calling a well-known procedure with one free variable; pass
         ;; the free variable as the closure.
         (convert-arg (rename var) k))
        (_
         (convert-arg var k))))

    (define (make-single-closure cps k src kfun)
      (let ((free (intmap-ref free-vars kfun)))
        ;; We allow kfun to be #f for well-known closures; in particular
        ;; for functions that share a closure there's no kfun value that
        ;; it makes sense to pass in.
        (match (vector (if kfun (well-known? kfun) #t) (intset-count free))
          (#(#f 0)
           (with-cps cps
             (build-term ($continue k src ($closure kfun 0)))))
          (#(#t 0)
           (with-cps cps
             (build-term ($continue k src ($const #f)))))
          (#(#t 1)
           ;; A well-known closure of one free variable is replaced
           ;; at each use with the free variable itself, so we don't
           ;; need a binding at all; and yet, the continuation
           ;; expects one value, so give it something.  DCE should
           ;; clean up later.
           (with-cps cps
             (build-term ($continue k src ($const #f)))))
          (#(well-known? nfree)
           ;; A bit of a mess, but beta conversion should remove the
           ;; final $values if possible.
           (with-cps cps
             (letv closure)
             (letk k* ($kargs () () ($continue k src ($values (closure)))))
             (let$ init (init-closure k* src closure well-known? nfree free))
             (letk knew ($kargs (#f) (closure) ,init))
             ($ (allocate-closure knew src kfun well-known? nfree)))))))

    (define (visit-term cps term)
      (match term
        (($ $continue k src (or ($ $const) ($ $prim)))
         (with-cps cps
           term))

        (($ $continue k src ($ $fun kfun))
         (with-cps cps
           ($ (make-single-closure k src kfun))))

        ;; Remove letrec.
        (($ $continue k src ($ $rec names vars (($ $fun kfuns) ...)))
         (match (vector names vars kfuns)
           (#(() () ())
            ;; Trivial empty case.
            (with-cps cps
              (build-term ($continue k src ($values ())))))
           (#((name) (var) (kfun))
            ;; Trivial single case.  We have already proven that K has
            ;; only LABEL as its predecessor, so we have been able
            ;; already to rewrite free references to the bound name with
            ;; the self name.
            (with-cps cps
              ($ (make-single-closure k src kfun))))
           (#(_ _ (kfun0 . _))
            ;; A non-trivial strongly-connected component.  Does it have
            ;; a shared closure?
            (match (intmap-ref shared kfun0 (lambda (_) #f))
              (#f
               ;; Nope.  Allocate closures for each function.
               (let lp ((in (map list names vars funs))
                        (bindings (lambda (body) body))
                        (body (match (hashq-ref letrec-conts k)
                                ;; Remove these letrec bindings, as we're
                                ;; going to inline the body after building
                                ;; each closure separately.
                                (($ $kargs names syms body)
                                 (visit-term body)))))
                 (match in
                   (() (bindings body))
                   (((name var ($ $fun
                                  (and fun-body
                                       ($ $cont kfun ($ $kfun src))))) . in)
                    (let ((fun-free (hashq-ref free-vars kfun)))
                      (lp in
                          (lambda (body)
                            (allocate-closure
                             src name var kfun (well-known? kfun) fun-free
                             (bindings body)))
                          (init-closure
                           src var (well-known? kfun) fun-free
                           body)))))))
              (shared
               ;; If shared is in the bound->var map, that means one of
               ;; the functions is not well-known.
               (let ((kfun (intmap-ref bound->label shared (lambda (_) #f))))
                 (with-cps cps
                   (letv closure)
                   (letk k* ($kargs (#f) (closure)
                              ($continue k src
                                ($values ,(map (lambda (_) closure) names)))))
                   ($ (make-single-closure k* src kfun)))))))))

        (($ $continue k src ($ $call proc args))
         (match (hashq-ref named-funs proc)
           (($ $cont kfun)
            (convert-known-proc-call
             proc kfun self self-known? free
             (lambda (proc)
               (convert-args args
                   (lambda (args)
                     (build-cps-term
                       ($continue k src
                         ($callk kfun proc args))))))))
           (#f
            (convert-args (cons proc args)
                (match-lambda
                  ((proc . args)
                   (build-cps-term
                     ($continue k src
                       ($call proc args)))))))))

        (($ $continue k src ($ $primcall name args))
         (convert-args args
             (lambda (args)
               (build-cps-term
                 ($continue k src ($primcall name args))))))

        (($ $continue k src ($ $branch kt ($ $primcall name args)))
         (convert-args args
             (lambda (args)
               (build-cps-term
                 ($continue k src
                   ($branch kt ($primcall name args)))))))

        (($ $continue k src ($ $branch kt ($ $values (arg))))
         (convert-arg arg
             (lambda (arg)
               (build-cps-term
                 ($continue k src
                   ($branch kt ($values (arg))))))))

        (($ $continue k src ($ $values args))
         (convert-args args
             (lambda (args)
               (build-cps-term
                 ($continue k src ($values args))))))

        (($ $continue k src ($ $prompt escape? tag handler))
         (convert-arg tag
             (lambda (tag)
               (build-cps-term
                 ($continue k src
                   ($prompt escape? tag handler))))))))

    (intset-fold (lambda (label cps)
                   (match (intmap-ref cps label)
                     (($ $kargs names vars term)
                      (with-cps cps
                        (let$ term (visit-term term))
                        (setk label ($kargs names vars ,term))))
                     (_ cps)))
                 body
                 cps)))

(define (convert-closures cps)
  "Convert free reference in @var{cps} to primcalls to @code{free-ref},
and allocate and initialize flat closures."
  (let* ((kfun 0) ;; Ass-u-me.
         ;; label -> body-label...
         (functions (compute-function-bodies cps kfun))
         (cps (filter-reachable cps functions))
         ;; label -> bound-var...
         (label->bound (compute-function-names cps functions))
         ;; bound-var -> label
         (bound->label (invert-partition label->bound))
         ;; label...
         (well-known (compute-well-known-functions cps functions label->bound))
         ;; bound-var -> closure-var
         (shared (compute-shared-closures cps well-known))
         (cps (rewrite-shared-closure-calls cps functions label->bound shared
                                            kfun))
         ;; label -> free-var...
         (free-vars (compute-free-vars cps kfun shared))
         (free-vars (prune-free-vars free-vars bound->label well-known)))
    (let ((free-in-program (intmap-ref free-vars kfun)))
      (unless (eq? intset-empty free-in-program)
        (error "Expected no free vars in program" free-in-program)))
    (intmap-map
     (lambda (label body)
       (convert-one cps label body free-vars bound->label well-known shared))
     functions)))

;;; Local Variables:
;;; eval: (put 'convert-arg 'scheme-indent-function 2)
;;; eval: (put 'convert-args 'scheme-indent-function 2)
;;; End:
