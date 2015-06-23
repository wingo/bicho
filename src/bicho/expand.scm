;;;; -*-scheme-*-
;;;;
;;;; Copyright (C) 2001, 2003, 2006, 2009, 2010, 2011,
;;;;   2012, 2013, 2015 Free Software Foundation, Inc.
;;;;
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
;;;; 


(define-module (bicho expand)
  #:use-module (ice-9 match)
  #:use-module (bicho tree-il)
  #:use-module (bicho eval)
  #:export ((macroexpand . expand)))

;;; Portable implementation of syntax-case
;;; Originally extracted from Chez Scheme Version 5.9f
;;; Authors: R. Kent Dybvig, Oscar Waddell, Bob Hieb, Carl Bruggeman

;;; Copyright (c) 1992-1997 Cadence Research Systems
;;; Permission to copy this software, in whole or in part, to use this
;;; software for any lawful purpose, and to redistribute this software
;;; is granted subject to the restriction that all copies made of this
;;; software must include this copyright notice in full.  This software
;;; is provided AS IS, with NO WARRANTY, EITHER EXPRESS OR IMPLIED,
;;; INCLUDING BUT NOT LIMITED TO IMPLIED WARRANTIES OF MERCHANTABILITY
;;; OR FITNESS FOR ANY PARTICULAR PURPOSE.  IN NO EVENT SHALL THE
;;; AUTHORS BE LIABLE FOR CONSEQUENTIAL OR INCIDENTAL DAMAGES OF ANY
;;; NATURE WHATSOEVER.

;;; Modified by Mikael Djurfeldt <djurfeldt@nada.kth.se> according
;;; to the ChangeLog distributed in the same directory as this file:
;;; 1997-08-19, 1997-09-03, 1997-09-10, 2000-08-13, 2000-08-24,
;;; 2000-09-12, 2001-03-08

;;; Modified by Andy Wingo <wingo@pobox.com> according to the Git
;;; revision control logs corresponding to this file: 2009, 2010.

;;; Modified by Mark H Weaver <mhw@netris.org> according to the Git
;;; revision control logs corresponding to this file: 2012, 2013.


;;; This code is based on "Syntax Abstraction in Scheme"
;;; by R. Kent Dybvig, Robert Hieb, and Carl Bruggeman.
;;; Lisp and Symbolic Computation 5:4, 295-326, 1992.
;;; <http://www.cs.indiana.edu/~dyb/pubs/LaSC-5-4-pp295-326.pdf>


;;; This file defines the syntax-case expander, macroexpand, and a set
;;; of associated syntactic forms and procedures.  Of these, the
;;; following are documented in The Scheme Programming Language,
;;; Fourth Edition (R. Kent Dybvig, MIT Press, 2009), and in the 
;;; R6RS:
;;;
;;;   bound-identifier=?
;;;   datum->syntax
;;;   define-syntax
;;;   syntax-parameterize
;;;   free-identifier=?
;;;   generate-temporaries
;;;   identifier?
;;;   identifier-syntax
;;;   let-syntax
;;;   letrec-syntax
;;;   syntax
;;;   syntax-case
;;;   syntax->datum
;;;   syntax-rules
;;;   with-syntax
;;;
;;; Additionally, the expander provides definitions for a number of core
;;; Scheme syntactic bindings, such as `let', `lambda', and the like.

;;; The remaining exports are listed below:
;;;
;;;   (macroexpand datum)
;;;      if datum represents a valid expression, macroexpand returns an
;;;      expanded version of datum in a core language that includes no
;;;      syntactic abstractions.  The core language includes begin,
;;;      define, if, lambda, letrec, quote, and set!.
;;;   (syntax-violation who message form [subform])
;;;      used to report errors found during expansion
;;;   ($$sc-dispatch e p)
;;;      used by expanded code to handle syntax-case matching

;;; This file is shipped along with an expanded version of itself,
;;; psyntax-pp.scm, which is loaded when psyntax.scm has not yet been
;;; compiled.  In this way, psyntax bootstraps off of an expanded
;;; version of itself.

;;; This implementation of the expander sometimes uses syntactic
;;; abstractions when procedural abstractions would suffice.  For
;;; example, we define top-wrap and top-marked? as
;;;
;;;   (define-syntax top-wrap (identifier-syntax '((top))))
;;;   (define-syntax top-marked?
;;;     (syntax-rules ()
;;;       ((_ w) (memq 'top (wrap-marks w)))))
;;;
;;; rather than
;;;
;;;   (define top-wrap '((top)))
;;;   (define top-marked?
;;;     (lambda (w) (memq 'top (wrap-marks w))))
;;;
;;; On the other hand, we don't do this consistently; we define
;;; make-wrap, wrap-marks, and wrap-subst simply as
;;;
;;;   (define make-wrap cons)
;;;   (define wrap-marks car)
;;;   (define wrap-subst cdr)
;;;
;;; In Chez Scheme, the syntactic and procedural forms of these
;;; abstractions are equivalent, since the optimizer consistently
;;; integrates constants and small procedures.  This will be true of
;;; Guile as well, once we implement a proper inliner.


;;; Implementation notes:

;;; Objects with no standard print syntax, including objects containing
;;; cycles and syntax object, are allowed in quoted data as long as they
;;; are contained within a syntax form or produced by datum->syntax.
;;; Such objects are never copied.

;;; All identifiers that don't have macro definitions and are not bound
;;; lexically are assumed to be global variables.

;;; Top-level definitions of macro-introduced identifiers are allowed.
;;; This may not be appropriate for implementations in which the
;;; model is that bindings are created by definitions, as opposed to
;;; one in which initial values are assigned by definitions.

;;; Identifiers and syntax objects are implemented as vectors for
;;; portability.  As a result, it is possible to "forge" syntax objects.

;;; The implementation of generate-temporaries assumes that it is
;;; possible to generate globally unique symbols (gensyms).

;;; The source location associated with incoming expressions is tracked
;;; via the source-properties mechanism, a weak map from expression to
;;; source information. At times the source is separated from the
;;; expression; see the note below about "efficiency and confusion".

(define *compile-environment* (make-hash-table))

(define-syntax define-structure
  (lambda (x)
    (define construct-name
      (lambda (template-identifier . args)
        (datum->syntax
         template-identifier
         (string->symbol
          (apply string-append
                 (map (lambda (x)
                        (if (string? x)
                            x
                            (symbol->string (syntax->datum x))))
                      args))))))
    (syntax-case x ()
      ((_ (name id1 ...))
       (and-map identifier? #'(name id1 ...))
       (with-syntax
           ((constructor (construct-name #'name "make-" #'name))
            (predicate (construct-name #'name #'name "?"))
            ((access ...)
             (map (lambda (x) (construct-name x #'name "-" x))
                  #'(id1 ...)))
            ((assign ...)
             (map (lambda (x)
                    (construct-name x "set-" #'name "-" x "!"))
                  #'(id1 ...)))
            (structure-length
             (+ (length #'(id1 ...)) 1))
            ((index ...)
             (let f ((i 1) (ids #'(id1 ...)))
               (if (null? ids)
                   '()
                   (cons i (f (+ i 1) (cdr ids)))))))
         #'(begin
             (define constructor
               (lambda (id1 ...)
                 (vector 'name id1 ... )))
             (define predicate
               (lambda (x)
                 (and (vector? x)
                      (= (vector-length x) structure-length)
                      (eq? (vector-ref x 0) 'name))))
             (define access
               (lambda (x)
                 (vector-ref x index)))
             ...
             (define assign
               (lambda (x update)
                 (vector-set! x index update)))
             ...))))))

(define-syntax fx+ (identifier-syntax +))
(define-syntax fx- (identifier-syntax -))
(define-syntax fx= (identifier-syntax =))
(define-syntax fx< (identifier-syntax <))

(define (top-level-eval-hook x)
  (eval x))

(define (local-eval-hook x)
  (eval x))

(define (put-global-definition-hook symbol type val)
  (hashq-set! *compile-environment* symbol (cons type val)))

(define (get-global-definition-hook symbol)
  (hashq-ref *compile-environment* symbol))

(define (decorate-source e s)
  (if (and s (supports-source-properties? e))
      (set-source-properties! e s))
  e)

(define (maybe-name-value! name val)
  (when (lambda? val)
    (let ((meta (lambda-meta val)))
      (unless (assq 'name meta)
        (set! (lambda-meta val) (acons 'name name meta))))))

;; output constructors
(define (build-void source)
  (make-void source))

(define (build-call source fun-exp arg-exps)
  (make-call source fun-exp arg-exps))

(define (build-conditional source test-exp then-exp else-exp)
  (make-conditional source test-exp then-exp else-exp))

(define (build-lexical-reference type source name var)
  (make-lexical-ref source name var))

(define (build-lexical-assignment source name var exp)
  (maybe-name-value! name exp)
  (make-lexical-set source name var exp))

(define (build-global-reference source var)
  (make-toplevel-ref source var))

(define (build-simple-lambda src req rest vars meta exp)
  (make-lambda src
               meta
               ;; hah, a case in which kwargs would be nice.
               (make-lambda-case
                ;; src req opt rest kw inits vars body else
                src req #f rest #f '() vars exp #f)))

(define (build-case-lambda src meta body)
  (make-lambda src meta body))

(define (build-lambda-case src req opt rest kw inits vars body else-case)
  ;; req := (name ...)
  ;; opt := (name ...) | #f
  ;; rest := name | #f
  ;; kw := (allow-other-keys? (keyword name var) ...) | #f
  ;; inits: (init ...)
  ;; vars: (sym ...)
  ;; vars map to named arguments in the following order:
  ;;  required, optional (positional), rest, keyword.
  ;; the body of a lambda: anything, already expanded
  ;; else: lambda-case | #f
  (make-lambda-case src req opt rest kw inits vars body else-case))

(define (build-primcall src name args)
  (make-primcall src name args))

(define (build-primref src name)
  (make-primitive-ref src name))

(define (build-data src exp)
  (make-const src exp))

(define (build-sequence src exps)
  (if (null? (cdr exps))
      (car exps)
      (make-seq src (car exps) (build-sequence #f (cdr exps)))))

(define (build-let src ids vars val-exps body-exp)
  (for-each maybe-name-value! ids val-exps)
  (if (null? vars)
      body-exp
      (make-let src ids vars val-exps body-exp)))

(define (build-named-let src ids vars val-exps body-exp)
  (let ((f (car vars))
        (f-name (car ids))
        (vars (cdr vars))
        (ids (cdr ids)))
    (let ((proc (build-simple-lambda src ids #f vars '() body-exp)))
      (maybe-name-value! f-name proc)
      (for-each maybe-name-value! ids val-exps)
      (make-letrec
       src #f
       (list f-name) (list f) (list proc)
       (build-call src (build-lexical-reference 'fun src f-name f)
                   val-exps)))))

(define (build-letrec src in-order? ids vars val-exps body-exp)
  (if (null? vars)
      body-exp
      (begin
        (for-each maybe-name-value! ids val-exps)
        (make-letrec src in-order? ids vars val-exps body-exp))))

;; FIXME: use a faster gensym
(define-syntax-rule (build-lexical-var src id)
  (gensym (string-append (symbol->string id) "-")))

(define-structure (syntax-object expression wrap module))

(define-syntax no-source (identifier-syntax #f))

(define (source-annotation x)
  (let ((props (source-properties
                (if (syntax-object? x)
                    (syntax-object-expression x)
                    x))))
    (and (pair? props) props)))

(define-syntax-rule (arg-check pred? e who)
  (let ((x e))
    (if (not (pred? x)) (syntax-violation who "invalid argument" x))))

;; compile-time environments

;; wrap and environment comprise two level mapping.
;;   wrap : id --> label
;;   env : label --> <element>

;; environments are represented in two parts: a lexical part and a global
;; part.  The lexical part is a simple list of associations from labels
;; to bindings.  The global part is implemented by
;; {put,get}-global-definition-hook and associates symbols with
;; bindings.

;; global (assumed global variable) and displaced-lexical (see below)
;; do not show up in any environment; instead, they are fabricated by
;; resolve-identifier when it finds no other bindings.

;; <environment>              ::= ((<label> . <binding>)*)

;; identifier bindings include a type and a value

;; <binding> ::= (macro . <procedure>)           macros
;;               (syntax-parameter . (<procedure>)) syntax parameters
;;               (core . <procedure>)            core forms
;;               (begin)                         begin
;;               (define)                        define
;;               (define-syntax)                 define-syntax
;;               (define-syntax-parameter)       define-syntax-parameter
;;               (local-syntax . rec?)           let-syntax/letrec-syntax
;;               (syntax . (<var> . <level>))    pattern variables
;;               (global)                        assumed global variable
;;               (lexical . <var>)               lexical variables
;;               (ellipsis . <identifier>)       custom ellipsis
;;               (displaced-lexical)             displaced lexicals
;; <level>   ::= <nonnegative integer>
;; <var>     ::= variable returned by build-lexical-var

;; a macro is a user-defined syntactic-form.  a core is a
;; system-defined syntactic form.  begin, define, define-syntax, and
;; define-syntax-parameter are treated specially since they are
;; sensitive to whether the form is at top-level and can denote valid
;; internal definitions.

;; a pattern variable is a variable introduced by syntax-case and can
;; be referenced only within a syntax form.

;; any identifier for which no top-level syntax definition or local
;; binding of any kind has been seen is assumed to be a global
;; variable.

;; a lexical variable is a lambda- or letrec-bound variable.

;; an ellipsis binding is introduced by the 'with-ellipsis' special
;; form.

;; a displaced-lexical identifier is a lexical identifier removed from
;; it's scope by the return of a syntax object containing the identifier.
;; a displaced lexical can also appear when a letrec-syntax-bound
;; keyword is referenced on the rhs of one of the letrec-syntax clauses.
;; a displaced lexical should never occur with properly written macros.

(define-syntax make-binding
  (syntax-rules (quote)
    ((_ type value) (cons type value))
    ((_ 'type) '(type))
    ((_ type) (cons type '()))))
(define-syntax-rule (binding-type x)
  (car x))
(define-syntax-rule (binding-value x)
  (cdr x))

(define-syntax null-env (identifier-syntax '()))

(define (extend-env labels bindings r)
  (if (null? labels)
      r
      (extend-env (cdr labels) (cdr bindings)
                  (cons (cons (car labels) (car bindings)) r))))

(define (extend-var-env labels vars r)
  ;; variant of extend-env that forms "lexical" binding
  (if (null? labels)
      r
      (extend-var-env (cdr labels) (cdr vars)
                      (cons (cons (car labels) (make-binding 'lexical (car vars))) r))))

;; we use a "macros only" environment in expansion of local macro
;; definitions so that their definitions can use local macros without
;; attempting to use other lexical identifiers.
(define (macros-only-env r)
  (if (null? r)
      '()
      (let ((a (car r)))
        (if (memq (cadr a) '(macro syntax-parameter ellipsis))
            (cons a (macros-only-env (cdr r)))
            (macros-only-env (cdr r))))))

(define (global-extend type sym val)
  (put-global-definition-hook sym type val))

;; Conceptually, identifiers are always syntax objects.  Internally,
;; however, the wrap is sometimes maintained separately (a source of
;; efficiency and confusion), so that symbols are also considered
;; identifiers by id?.  Externally, they are always wrapped.

(define (nonsymbol-id? x)
  (and (syntax-object? x)
       (symbol? (syntax-object-expression x))))

(define (id? x)
  (cond
   ((symbol? x) #t)
   ((syntax-object? x) (symbol? (syntax-object-expression x)))
   (else #f)))

(define-syntax-rule (id-sym-name e)
  (let ((x e))
    (if (syntax-object? x)
        (syntax-object-expression x)
        x)))

(define (id-sym-name&marks x w)
  (if (syntax-object? x)
      (values
       (syntax-object-expression x)
       (join-marks (wrap-marks w) (wrap-marks (syntax-object-wrap x))))
      (values x (wrap-marks w))))

;; syntax object wraps

;;      <wrap> ::= ((<mark> ...) . (<subst> ...))
;;     <subst> ::= shift | <subs>
;;      <subs> ::= #(ribcage #(<sym> ...) #(<mark> ...) #(<label> ...))
;;                 | #(ribcage (<sym> ...) (<mark> ...) (<label> ...))

(define (make-wrap marks subst) (cons marks subst))
(define (wrap-marks wrap) (car wrap))
(define (wrap-subst wrap) (cdr wrap))

;; labels must be comparable with "eq?", have read-write invariance,
;; and distinct from symbols.
(define (gen-label)
  (symbol->string (gensym "-")))

(define (gen-labels ls)
  (if (null? ls)
      '()
      (cons (gen-label) (gen-labels (cdr ls)))))

(define-structure (ribcage symnames marks labels))

(define-syntax empty-wrap (identifier-syntax '(())))

(define-syntax top-wrap (identifier-syntax '((top))))

(define (top-marked? w)
  (memq 'top (wrap-marks w)))

;; Marks must be comparable with "eq?" and distinct from pairs and
;; the symbol top.  We do not use integers so that marks will remain
;; unique even across file compiles.

(define-syntax the-anti-mark (identifier-syntax #f))

(define (anti-mark w)
  (make-wrap (cons the-anti-mark (wrap-marks w))
             (cons 'shift (wrap-subst w))))

(define-syntax-rule (new-mark)
  (gensym "m-"))

;; make-empty-ribcage and extend-ribcage maintain list-based ribcages for
;; internal definitions, in which the ribcages are built incrementally
(define-syntax-rule (make-empty-ribcage)
  (make-ribcage '() '() '()))

(define (extend-ribcage! ribcage id label)
  ;; must receive ids with complete wraps
  (set-ribcage-symnames! ribcage
                         (cons (syntax-object-expression id)
                               (ribcage-symnames ribcage)))
  (set-ribcage-marks! ribcage
                      (cons (wrap-marks (syntax-object-wrap id))
                            (ribcage-marks ribcage)))
  (set-ribcage-labels! ribcage
                       (cons label (ribcage-labels ribcage))))

;; make-binding-wrap creates vector-based ribcages
(define (make-binding-wrap ids labels w)
  (if (null? ids)
      w
      (make-wrap
       (wrap-marks w)
       (cons
        (let ((labelvec (list->vector labels)))
          (let ((n (vector-length labelvec)))
            (let ((symnamevec (make-vector n)) (marksvec (make-vector n)))
              (let f ((ids ids) (i 0))
                (if (not (null? ids))
                    (call-with-values
                        (lambda () (id-sym-name&marks (car ids) w))
                      (lambda (symname marks)
                        (vector-set! symnamevec i symname)
                        (vector-set! marksvec i marks)
                        (f (cdr ids) (fx+ i 1))))))
              (make-ribcage symnamevec marksvec labelvec))))
        (wrap-subst w)))))

(define (smart-append m1 m2)
  (if (null? m2)
      m1
      (append m1 m2)))

(define (join-wraps w1 w2)
  (let ((m1 (wrap-marks w1)) (s1 (wrap-subst w1)))
    (if (null? m1)
        (if (null? s1)
            w2
            (make-wrap
             (wrap-marks w2)
             (smart-append s1 (wrap-subst w2))))
        (make-wrap
         (smart-append m1 (wrap-marks w2))
         (smart-append s1 (wrap-subst w2))))))

(define (join-marks m1 m2)
  (smart-append m1 m2))

(define (same-marks? x y)
  (or (eq? x y)
      (and (not (null? x))
           (not (null? y))
           (eq? (car x) (car y))
           (same-marks? (cdr x) (cdr y)))))

(define (id-var-name id w)
  ;; Syntax objects use wraps to associate names with marked
  ;; identifiers.  This function returns the name corresponding to
  ;; the given identifier and wrap, or the original identifier if no
  ;; corresponding name was found.
  ;;
  ;; The name may be a string created by gen-label, indicating a
  ;; lexical binding, or another syntax object, indicating a
  ;; reference to a top-level definition created during a previous
  ;; macroexpansion.
  ;;
  ;; For lexical variables, finding a label simply amounts to looking
  ;; for an entry with the same symbolic name and the same marks.
  ;; Finding a toplevel definition is the same.
  ;;
  ;; The identifer may be passed in wrapped or unwrapped.  In any
  ;; case, this routine returns either a symbol, a syntax object, or
  ;; a string label.
  ;;
  (define-syntax-rule (first e)
    ;; Rely on Guile's multiple-values truncation.
    e)
  (define (search sym subst marks)
    (if (null? subst)
        (values #f marks)
        (let ((fst (car subst)))
          (if (eq? fst 'shift)
              (search sym (cdr subst) (cdr marks))
              (let ((symnames (ribcage-symnames fst)))
                (if (vector? symnames)
                    (search-vector-rib sym subst marks symnames fst)
                    (search-list-rib sym subst marks symnames fst)))))))
  (define (search-list-rib sym subst marks symnames ribcage)
    (let f ((symnames symnames) (i 0))
      (cond
       ((null? symnames) (search sym (cdr subst) marks))
       ((and (eq? (car symnames) sym)
             (same-marks? marks (list-ref (ribcage-marks ribcage) i)))
        (values (list-ref (ribcage-labels ribcage) i)
                marks))
       (else (f (cdr symnames) (fx+ i 1))))))
  (define (search-vector-rib sym subst marks symnames ribcage)
    (let ((n (vector-length symnames)))
      (let f ((i 0))
        (cond
         ((fx= i n) (search sym (cdr subst) marks))
         ((and (eq? (vector-ref symnames i) sym)
               (same-marks? marks (vector-ref (ribcage-marks ribcage) i)))
          (values (vector-ref (ribcage-labels ribcage) i) marks))
         (else (f (fx+ i 1)))))))
  (cond
   ((symbol? id)
    (or (first (search id (wrap-subst w) (wrap-marks w))) id))
   ((syntax-object? id)
    (let ((id (syntax-object-expression id))
          (w1 (syntax-object-wrap id)))
      (let ((marks (join-marks (wrap-marks w) (wrap-marks w1))))
        (call-with-values (lambda () (search id (wrap-subst w) marks))
          (lambda (new-id marks)
            (or new-id
                (first (search id (wrap-subst w1) marks))
                id))))))
   (else (syntax-violation 'id-var-name "invalid id" id))))

;; A helper procedure for syntax-locally-bound-identifiers, which
;; itself is a helper for transformer procedures.
;; `locally-bound-identifiers' returns a list of all bindings
;; visible to a syntax object with the given wrap.  They are in
;; order from outer to inner.
;;
;; The purpose of this procedure is to give a transformer procedure
;; references on bound identifiers, that the transformer can then
;; introduce some of them in its output.  As such, the identifiers
;; are anti-marked, so that rebuild-macro-output doesn't apply new
;; marks to them.
;;
(define (locally-bound-identifiers w)
  (define (scan subst results)
    (if (null? subst)
        results
        (let ((fst (car subst)))
          (if (eq? fst 'shift)
              (scan (cdr subst) results)
              (let ((symnames (ribcage-symnames fst))
                    (marks (ribcage-marks fst)))
                (if (vector? symnames)
                    (scan-vector-rib subst symnames marks results)
                    (scan-list-rib subst symnames marks results)))))))
  (define (scan-list-rib subst symnames marks results)
    (let f ((symnames symnames) (marks marks) (results results))
      (if (null? symnames)
          (scan (cdr subst) results)
          (f (cdr symnames) (cdr marks)
             (cons (wrap (car symnames)
                         (anti-mark (make-wrap (car marks) subst)))
                   results)))))
  (define (scan-vector-rib subst symnames marks results)
    (let ((n (vector-length symnames)))
      (let f ((i 0) (results results))
        (if (fx= i n)
            (scan (cdr subst) results)
            (f (fx+ i 1)
               (cons (wrap (vector-ref symnames i)
                           (anti-mark (make-wrap (vector-ref marks i) subst)))
                     results))))))
  (scan (wrap-subst w) '()))

;; Returns two values: binding type and binding value.
(define (resolve-identifier id w r resolve-syntax-parameters?)
  (define (resolve-syntax-parameters b)
    (if (and resolve-syntax-parameters?
             (eq? (binding-type b) 'syntax-parameter))
        (or (assq-ref r (binding-value b))
            (make-binding 'macro (car (binding-value b))))
        b))
  (define (resolve-global var)
    (let ((b (resolve-syntax-parameters
              (or (get-global-definition-hook var)
                  (make-binding 'global)))))
      (if (eq? (binding-type b) 'global)
          (values 'global var)
          (values (binding-type b) (binding-value b)))))
  (define (resolve-lexical label)
    (let ((b (resolve-syntax-parameters
              (or (assq-ref r label)
                  (make-binding 'displaced-lexical)))))
      (values (binding-type b) (binding-value b))))
  (let ((n (id-var-name id w)))
    (cond
     ((syntax-object? n)
      (cond
       ((not (eq? n id))
        ;; This identifier aliased another; recurse to allow
        ;; syntax-parameterize to override macro-introduced syntax
        ;; parameters.
        (resolve-identifier n w r resolve-syntax-parameters?))
       (else
        ;; Resolved to a free variable that was introduced by this
        ;; macro; continue to resolve this global by name.
        (resolve-identifier (syntax-object-expression n)
                            (syntax-object-wrap n)
                            r
                            resolve-syntax-parameters?))))
     ((symbol? n)
      (resolve-global n))
     ((string? n)
      (resolve-lexical n))
     (else
      (error "unexpected id-var-name" id w n)))))

(define transformer-environment
  (make-fluid
   (lambda (k)
     (error "called outside the dynamic extent of a syntax transformer"))))

(define (with-transformer-environment k)
  ((fluid-ref transformer-environment) k))

;; free-id=? must be passed fully wrapped ids since (free-id=? x y)
;; may be true even if (free-id=? (wrap x w) (wrap y w)) is not.

(define (free-id=? i j)
  (let* ((ni (id-var-name i empty-wrap))
         (nj (id-var-name j empty-wrap)))
    (cond
     ((syntax-object? ni) (free-id=? ni j))
     ((syntax-object? nj) (free-id=? i nj))
     (else
      ;; If the id-var-name is a symbol, then the variable is free.
      ;; Otherwise it is bound.  In either case, the identifiers are
      ;; the same if they are equal.
      (equal? ni nj)))))

;; bound-id=? may be passed unwrapped (or partially wrapped) ids as
;; long as the missing portion of the wrap is common to both of the ids
;; since (bound-id=? x y) iff (bound-id=? (wrap x w) (wrap y w))

(define (bound-id=? i j)
  (if (and (syntax-object? i) (syntax-object? j))
      (and (eq? (syntax-object-expression i)
                (syntax-object-expression j))
           (same-marks? (wrap-marks (syntax-object-wrap i))
                        (wrap-marks (syntax-object-wrap j))))
      (eq? i j)))

;; "valid-bound-ids?" returns #t if it receives a list of distinct ids.
;; valid-bound-ids? may be passed unwrapped (or partially wrapped) ids
;; as long as the missing portion of the wrap is common to all of the
;; ids.

(define (valid-bound-ids? ids)
  (and (let all-ids? ((ids ids))
         (or (null? ids)
             (and (id? (car ids))
                  (all-ids? (cdr ids)))))
       (distinct-bound-ids? ids)))

;; distinct-bound-ids? expects a list of ids and returns #t if there are
;; no duplicates.  It is quadratic on the length of the id list; long
;; lists could be sorted to make it more efficient.  distinct-bound-ids?
;; may be passed unwrapped (or partially wrapped) ids as long as the
;; missing portion of the wrap is common to all of the ids.

(define (distinct-bound-ids? ids)
  (let distinct? ((ids ids))
    (or (null? ids)
        (and (not (bound-id-member? (car ids) (cdr ids)))
             (distinct? (cdr ids))))))

(define (bound-id-member? x list)
  (and (not (null? list))
       (or (bound-id=? x (car list))
           (bound-id-member? x (cdr list)))))

;; wrapping expressions and identifiers

(define (wrap x w)
  (cond
   ((and (null? (wrap-marks w)) (null? (wrap-subst w))) x)
   ((syntax-object? x)
    (make-syntax-object (syntax-object-expression x)
                        (join-wraps w (syntax-object-wrap x))
                        #f))
   ((null? x) x)
   (else (make-syntax-object x w #f))))

(define (source-wrap x w s)
  (wrap (decorate-source x s) w))

;; expanding

(define (expand-sequence body r w s)
  (build-sequence s
                  (let dobody ((body body) (r r) (w w))
                    (if (null? body)
                        '()
                        (let ((first (expand (car body) r w)))
                          (cons first (dobody (cdr body) r w)))))))

;; At top-level, we allow mixed definitions and expressions.  Like
;; expand-body we expand in two passes.
;;
;; First, from left to right, we expand just enough to know what
;; expressions are definitions, syntax definitions, and splicing
;; statements (`begin').  If we anything needs evaluating at
;; expansion-time, it is expanded directly.
;;
;; Otherwise we collect expressions to expand, in thunks, and then
;; expand them all at the end.  This allows all syntax expanders
;; visible in a toplevel sequence to be visible during the
;; expansions of all normal definitions and expressions in the
;; sequence.
;;
(define (expand-top-sequence body r w s)
  (let* ((r (cons '("placeholder" . (placeholder)) r))
         (ribcage (make-empty-ribcage))
         (w (make-wrap (wrap-marks w) (cons ribcage (wrap-subst w)))))
    (define (record-definition! id var)
      ;; Ribcages map symbol+marks to names, mostly for resolving
      ;; lexicals.
      (extend-ribcage! ribcage id (wrap var top-wrap)))
    (define (macro-introduced-identifier? id)
      (not (equal? (wrap-marks (syntax-object-wrap id)) '(top))))
    (define (fresh-derived-name id orig-form)
      (gensym
       (string-append (symbol->string (syntax-object-expression id)) "-")))
    (define (parse body r w s)
      (let lp ((body body) (exps '()))
        (if (null? body)
            exps
            (lp (cdr body)
                (append (parse1 (car body) r w s)
                        exps)))))
    (define (parse1 x r w s)
      (call-with-values
          (lambda ()
            (syntax-type x r w (source-annotation x) ribcage #f))
        (lambda (type value form e w s)
          (case type
            ((define-form)
             (syntax-violation 'define
                               "toplevel definitions not allowed in bicho" e))
            ((define-syntax-form)
             (let* ((id (wrap value w))
                    (label (gen-label))
                    (var (if (macro-introduced-identifier? id)
                             (fresh-derived-name id x)
                             (syntax-object-expression id))))
               (record-definition! id var)
               (let ((val (top-level-eval-hook (expand e r w))))
                 (put-global-definition-hook var 'macro val))
               '()))
            ((define-syntax-parameter-form)
             (let* ((id (wrap value w))
                    (label (gen-label))
                    (var (if (macro-introduced-identifier? id)
                             (fresh-derived-name id x)
                             (syntax-object-expression id))))
               (record-definition! id var)
               (let ((val (list (top-level-eval-hook (expand e r w)))))
                 (put-global-definition-hook var 'syntax-parameter val))
               '()))
            ((begin-form)
             (syntax-case e ()
               ((_ e1 ...)
                (parse #'(e1 ...) r w s))))
            ((local-syntax-form)
             (expand-local-syntax value e r w s parse))
            (else
             (list
              (lambda ()
                (expand-expr type value form e r w s))))))))
    (let ((exps (map (lambda (x) (x))
                     (reverse (parse body r w s)))))
      (if (null? exps)
          (build-void s)
          (build-sequence s exps)))))

;; syntax-type returns six values: type, value, form, e, w, and s.
;; The first two are described in the table below.
;;
;;    type                   value         explanation
;;    -------------------------------------------------------------------
;;    core                   procedure     core singleton
;;    core-form              procedure     core form
;;    lexical                name          lexical variable reference
;;    global                 name          global variable reference
;;    begin                  none          begin keyword
;;    define                 none          define keyword
;;    define-syntax          none          define-syntax keyword
;;    define-syntax-parameter none         define-syntax-parameter keyword
;;    local-syntax           rec?          letrec-syntax/let-syntax keyword
;;    syntax                 level         pattern variable
;;    displaced-lexical      none          displaced lexical identifier
;;    lexical-call           name          call to lexical variable
;;    global-call            name          call to global variable
;;    primitive-call         name          call to primitive
;;    call                   none          any other call
;;    begin-form             none          begin expression
;;    define-form            id            variable definition
;;    define-syntax-form     id            syntax definition
;;    define-syntax-parameter-form id      syntax parameter definition
;;    local-syntax-form      rec?          syntax definition
;;    constant               none          self-evaluating datum
;;    other                  none          anything else
;;
;; form is the entire form.  For definition forms (define-form,
;; define-syntax-form, and define-syntax-parameter-form), e is the
;; rhs expression.  For all others, e is the entire form.  w is the
;; wrap for both form and e.  s is the source for the entire form.
;;
;; syntax-type expands macros and unwraps as necessary to get to one
;; of the forms above.  It also parses definition forms, although
;; perhaps this should be done by the consumer.

(define (syntax-type e r w s rib for-car?)
  (cond
   ((symbol? e)
    (call-with-values (lambda () (resolve-identifier e w r #t))
      (lambda (type value)
        (case type
          ((macro)
           (if for-car?
               (values type value e e w s)
               (syntax-type (expand-macro value e r w s rib)
                            r empty-wrap s rib #f)))
          ((global)
           ;; Toplevel definitions may resolve to bindings with
           ;; different names.
           (values type value e value w s))
          (else (values type value e e w s))))))
   ((pair? e)
    (let ((first (car e)))
      (call-with-values
          (lambda () (syntax-type first r w s rib #t))
        (lambda (ftype fval fform fe fw fs)
          (case ftype
            ((lexical)
             (values 'lexical-call fval e e w s))
            ((global)
             (values 'global-call (make-syntax-object fval w #f) e e w s))
            ((macro)
             (syntax-type (expand-macro fval e r w s rib)
                          r empty-wrap s rib for-car?))
            ((core)
             (values 'core-form fval e e w s))
            ((local-syntax)
             (values 'local-syntax-form fval e e w s))
            ((begin)
             (values 'begin-form #f e e w s))
            ((define)
             (syntax-case e ()
               ((_ name val)
                (id? #'name)
                (values 'define-form #'name e #'val w s))
               ((_ (name . args) e1 e2 ...)
                (and (id? #'name)
                     (valid-bound-ids? (lambda-var-list #'args)))
                ;; need lambda here...
                (values 'define-form (wrap #'name w)
                        (wrap e w)
                        (decorate-source
                         (cons #'lambda (wrap #'(args e1 e2 ...) w))
                         s)
                        empty-wrap s))
               ((_ name)
                (id? #'name)
                (values 'define-form (wrap #'name w)
                        (wrap e w)
                        #'(if #f #f)
                        empty-wrap s))))
            ((define-syntax)
             (syntax-case e ()
               ((_ name val)
                (id? #'name)
                (values 'define-syntax-form #'name e #'val w s))))
            ((define-syntax-parameter)
             (syntax-case e ()
               ((_ name val)
                (id? #'name)
                (values 'define-syntax-parameter-form #'name e #'val w s))))
            (else
             (values 'call #f e e w s)))))))
   ((syntax-object? e)
    (syntax-type (syntax-object-expression e)
                 r
                 (join-wraps w (syntax-object-wrap e))
                 (or (source-annotation e) s) rib
                 for-car?))
   ((self-evaluating? e) (values 'constant #f e e w s))
   (else (values 'other #f e e w s))))

(define (expand e r w)
  (call-with-values
      (lambda () (syntax-type e r w (source-annotation e) #f #f))
    (lambda (type value form e w s)
      (expand-expr type value form e r w s))))

(define (expand-expr type value form e r w s)
  (case type
    ((lexical)
     (build-lexical-reference 'value s e value))
    ((core core-form)
     ;; apply transformer
     (value e r w s))
    ((lexical-call)
     (expand-call
      (let ((id (car e)))
        (build-lexical-reference 'fun (source-annotation id)
                                 (if (syntax-object? id)
                                     (syntax->datum id)
                                     id)
                                 value))
      e r w s))
    ((global-call)
     (expand-call
      (build-global-reference (source-annotation (car e))
                              (if (syntax-object? value)
                                  (syntax-object-expression value)
                                  value))
      e r w s))
    ((primitive-call)
     (syntax-case e ()
       ((_ e ...)
        (build-primcall s
                        value
                        (map (lambda (e) (expand e r w))
                             #'(e ...))))))
    ((constant) (build-data s (strip (source-wrap e w s) empty-wrap)))
    ((global) (build-global-reference s value))
    ((call) (expand-call (expand (car e) r w) e r w s))
    ((begin-form)
     (syntax-case e ()
       ((_ e1 e2 ...) (expand-sequence #'(e1 e2 ...) r w s))
       ((_)
        (syntax-violation #f "sequence of zero expressions"
                          (source-wrap e w s)))))
    ((local-syntax-form)
     (expand-local-syntax value e r w s expand-sequence))
    ((define-form define-syntax-form define-syntax-parameter-form)
     (syntax-violation #f "definition in expression context, where definitions are not allowed,"
                       (source-wrap form w s)))
    ((syntax)
     (syntax-violation #f "reference to pattern variable outside syntax form"
                       (source-wrap e w s)))
    ((displaced-lexical)
     (syntax-violation #f "reference to identifier outside its scope"
                       (source-wrap e w s)))
    (else (syntax-violation #f "unexpected syntax"
                            (source-wrap e w s)))))

(define (expand-call x e r w s)
  (syntax-case e ()
    ((e0 e1 ...)
     (build-call s x
                 (map (lambda (e) (expand e r w)) #'(e1 ...))))))

;; (What follows is my interpretation of what's going on here -- Andy)
;;
;; A macro takes an expression, a tree, the leaves of which are
;; identifiers and datums. Identifiers are symbols along with a
;; wrap. For efficiency, subtrees that share wraps may be grouped as
;; one syntax object.
;;
;; Going into the expansion, the expression is given an anti-mark, which
;; logically propagates to all leaves. Then, in the new expression returned
;; from the transfomer, if we see an expression with an anti-mark, we know it
;; pertains to the original expression; conversely, expressions without the
;; anti-mark are known to be introduced by the transformer.
;;
;; Part of the macro output will be from the site of the macro use and part
;; from the macro definition. We allow source information from the macro use
;; to pass through, but we annotate the parts coming from the macro with the
;; source location information corresponding to the macro use. It would be
;; really nice if we could also annotate introduced expressions with the
;; locations corresponding to the macro definition, but that is not yet
;; possible.
(define (expand-macro p e r w s rib)
  (define (rebuild-macro-output x m)
    (cond ((pair? x)
           (decorate-source 
            (cons (rebuild-macro-output (car x) m)
                  (rebuild-macro-output (cdr x) m))
            s))
          ((syntax-object? x)
           (let ((w (syntax-object-wrap x)))
             (let ((ms (wrap-marks w)) (ss (wrap-subst w)))
               (if (and (pair? ms) (eq? (car ms) the-anti-mark))
                   ;; output is from original text
                   (make-syntax-object
                    (syntax-object-expression x)
                    (make-wrap (cdr ms) (if rib (cons rib (cdr ss)) (cdr ss)))
                    #f)
                   ;; output introduced by macro
                   (make-syntax-object
                    (decorate-source (syntax-object-expression x) s)
                    (make-wrap (cons m ms)
                               (if rib
                                   (cons rib (cons 'shift ss))
                                   (cons 'shift ss)))
                    #f)))))
          
          ((vector? x)
           (let* ((n (vector-length x))
                  (v (decorate-source (make-vector n) s)))
             (do ((i 0 (fx+ i 1)))
                 ((fx= i n) v)
               (vector-set! v i
                            (rebuild-macro-output (vector-ref x i) m)))))
          ((symbol? x)
           (syntax-violation #f "encountered raw symbol in macro output"
                             (source-wrap e w (wrap-subst w)) x))
          (else (decorate-source x s))))
  (with-fluids ((transformer-environment
                 (lambda (k) (k e r w s rib))))
    (rebuild-macro-output (p (source-wrap e (anti-mark w) s))
                          (new-mark))))

(define (expand-body body outer-form r w)
  ;; In processing the forms of the body, we create a new, empty wrap.
  ;; This wrap is augmented (destructively) each time we discover that
  ;; the next form is a definition.  This is done:
  ;;
  ;;   (1) to allow the first nondefinition form to be a call to
  ;;       one of the defined ids even if the id previously denoted a
  ;;       definition keyword or keyword for a macro expanding into a
  ;;       definition;
  ;;   (2) to prevent subsequent definition forms (but unfortunately
  ;;       not earlier ones) and the first nondefinition form from
  ;;       confusing one of the bound identifiers for an auxiliary
  ;;       keyword; and
  ;;   (3) so that we do not need to restart the expansion of the
  ;;       first nondefinition form, which is problematic anyway
  ;;       since it might be the first element of a begin that we
  ;;       have just spliced into the body (meaning if we restarted,
  ;;       we'd really need to restart with the begin or the macro
  ;;       call that expanded into the begin, and we'd have to give
  ;;       up allowing (begin <defn>+ <expr>+), which is itself
  ;;       problematic since we don't know if a begin contains only
  ;;       definitions until we've expanded it).
  ;;
  ;; Before processing the body, we also create a new environment
  ;; containing a placeholder for the bindings we will add later and
  ;; associate this environment with each form.  In processing a
  ;; let-syntax or letrec-syntax, the associated environment may be
  ;; augmented with local keyword bindings, so the environment may
  ;; be different for different forms in the body.  Once we have
  ;; gathered up all of the definitions, we evaluate the transformer
  ;; expressions and splice into r at the placeholder the new variable
  ;; and keyword bindings.  This allows let-syntax or letrec-syntax
  ;; forms local to a portion or all of the body to shadow the
  ;; definition bindings.
  ;;
  ;; Subforms of a begin, let-syntax, or letrec-syntax are spliced
  ;; into the body.
  ;;
  ;; outer-form is fully wrapped w/source
  (let* ((r (cons '("placeholder" . (placeholder)) r))
         (ribcage (make-empty-ribcage))
         (w (make-wrap (wrap-marks w) (cons ribcage (wrap-subst w)))))
    (let parse ((body (map (lambda (x) (cons r (wrap x w))) body))
                (ids '()) (labels '())
                (var-ids '()) (vars '()) (vals '()) (bindings '()))
      (if (null? body)
          (syntax-violation #f "no expressions in body" outer-form)
          (let ((e (cdar body)) (er (caar body)))
            (call-with-values
                (lambda ()
                  (syntax-type e er empty-wrap (source-annotation e) ribcage #f))
              (lambda (type value form e w s)
                (case type
                  ((define-form)
                   (let ((id (wrap value w)) (label (gen-label)))
                     (let ((var (gen-var id)))
                       (extend-ribcage! ribcage id label)
                       (parse (cdr body)
                              (cons id ids) (cons label labels)
                              (cons id var-ids)
                              (cons var vars) (cons (cons er (wrap e w)) vals)
                              (cons (make-binding 'lexical var) bindings)))))
                  ((define-syntax-form)
                   (let ((id (wrap value w))
                         (label (gen-label))
                         (trans-r (macros-only-env er)))
                     (extend-ribcage! ribcage id label)
                     ;; As required by R6RS, evaluate the right-hand-sides of internal
                     ;; syntax definition forms and add their transformers to the
                     ;; compile-time environment immediately, so that the newly-defined
                     ;; keywords may be used in definition context within the same
                     ;; lexical contour.
                     (set-cdr! r (extend-env
                                  (list label)
                                  (list (make-binding
                                         'macro
                                         (eval-local-transformer
                                          (expand e trans-r w))))
                                  (cdr r)))
                     (parse (cdr body) (cons id ids) labels var-ids vars vals bindings)))
                  ((define-syntax-parameter-form)
                   ;; Same as define-syntax-form, but different format of the binding.
                   (let ((id (wrap value w))
                         (label (gen-label))
                         (trans-r (macros-only-env er)))
                     (extend-ribcage! ribcage id label)
                     (set-cdr! r (extend-env
                                  (list label)
                                  (list (make-binding
                                         'syntax-parameter
                                         (list (eval-local-transformer
                                                (expand e trans-r w)))))
                                  (cdr r)))
                     (parse (cdr body) (cons id ids) labels var-ids vars vals bindings)))
                  ((begin-form)
                   (syntax-case e ()
                     ((_ e1 ...)
                      (parse (let f ((forms #'(e1 ...)))
                               (if (null? forms)
                                   (cdr body)
                                   (cons (cons er (wrap (car forms) w))
                                         (f (cdr forms)))))
                             ids labels var-ids vars vals bindings))))
                  ((local-syntax-form)
                   (expand-local-syntax value e er w s
                                        (lambda (forms er w s)
                                          (parse (let f ((forms forms))
                                                   (if (null? forms)
                                                       (cdr body)
                                                       (cons (cons er (wrap (car forms) w))
                                                             (f (cdr forms)))))
                                                 ids labels var-ids vars vals bindings))))
                  (else           ; found a non-definition
                   (if (null? ids)
                       (build-sequence no-source
                                       (map (lambda (x)
                                              (expand (cdr x) (car x) empty-wrap))
                                            (cons (cons er (source-wrap e w s))
                                                  (cdr body))))
                       (begin
                         (if (not (valid-bound-ids? ids))
                             (syntax-violation
                              #f "invalid or duplicate identifier in definition"
                              outer-form))
                         (set-cdr! r (extend-env labels bindings (cdr r)))
                         (build-letrec no-source #t
                                       (reverse (map syntax->datum var-ids))
                                       (reverse vars)
                                       (map (lambda (x)
                                              (expand (cdr x) (car x) empty-wrap))
                                            (reverse vals))
                                       (build-sequence no-source
                                                       (map (lambda (x)
                                                              (expand (cdr x) (car x) empty-wrap))
                                                            (cons (cons er (source-wrap e w s))
                                                                  (cdr body))))))))))))))))

(define (expand-local-syntax rec? e r w s k)
  (syntax-case e ()
    ((_ ((id val) ...) e1 e2 ...)
     (let ((ids #'(id ...)))
       (if (not (valid-bound-ids? ids))
           (syntax-violation #f "duplicate bound keyword" e)
           (let ((labels (gen-labels ids)))
             (let ((new-w (make-binding-wrap ids labels w)))
               (k #'(e1 e2 ...)
                  (extend-env
                   labels
                   (let ((w (if rec? new-w w))
                         (trans-r (macros-only-env r)))
                     (map (lambda (x)
                            (make-binding 'macro
                                          (eval-local-transformer
                                           (expand x trans-r w))))
                          #'(val ...)))
                   r)
                  new-w
                  s))))))
    (_ (syntax-violation #f "bad local syntax definition"
                         (source-wrap e w s)))))

(define (eval-local-transformer expanded)
  (let ((p (local-eval-hook expanded)))
    (if (procedure? p)
        p
        (syntax-violation #f "nonprocedure transformer" p))))

(define (expand-void )
  (build-void no-source))

(define (ellipsis? e r)
  (and (nonsymbol-id? e)
       ;; If there is a binding for the special identifier
       ;; #{ $sc-ellipsis }# in the lexical environment of E,
       ;; and if the associated binding type is 'ellipsis',
       ;; then the binding's value specifies the custom ellipsis
       ;; identifier within that lexical environment, and the
       ;; comparison is done using 'bound-id=?'.
       (call-with-values
           (lambda () (resolve-identifier
                       (make-syntax-object '#{ $sc-ellipsis }#
                                           (syntax-object-wrap e)
                                           #f)
                       empty-wrap r #f))
         (lambda (type value)
           (if (eq? type 'ellipsis)
               (bound-id=? e value)
               (free-id=? e #'(... ...)))))))

(define (lambda-formals orig-args)
  (define (req args rreq)
    (syntax-case args ()
      (()
       (check (reverse rreq) #f))
      ((a . b) (id? #'a)
       (req #'b (cons #'a rreq)))
      (r (id? #'r)
         (check (reverse rreq) #'r))
      (else
       (syntax-violation 'lambda "invalid argument list" orig-args args))))
  (define (check req rest)
    (cond
     ((distinct-bound-ids? (if rest (cons rest req) req))
      (values req #f rest #f))
     (else
      (syntax-violation 'lambda "duplicate identifier in argument list"
                        orig-args))))
  (req orig-args '()))

(define (expand-simple-lambda e r w s req rest meta body)
  (let* ((ids (if rest (append req (list rest)) req))
         (vars (map gen-var ids))
         (labels (gen-labels ids)))
    (build-simple-lambda
     s
     (map syntax->datum req) (and rest (syntax->datum rest)) vars
     meta
     (expand-body body (source-wrap e w s)
                  (extend-var-env labels vars r)
                  (make-binding-wrap ids labels w)))))

(define (lambda*-formals orig-args)
  (define (req args rreq)
    (syntax-case args ()
      (()
       (check (reverse rreq) '() #f '()))
      ((a . b) (id? #'a)
       (req #'b (cons #'a rreq)))
      ((a . b) (eq? (syntax->datum #'a) #:optional)
       (opt #'b (reverse rreq) '()))
      ((a . b) (eq? (syntax->datum #'a) #:key)
       (key #'b (reverse rreq) '() '()))
      ((a b) (eq? (syntax->datum #'a) #:rest)
       (rest #'b (reverse rreq) '() '()))
      (r (id? #'r)
         (rest #'r (reverse rreq) '() '()))
      (else
       (syntax-violation 'lambda* "invalid argument list" orig-args args))))
  (define (opt args req ropt)
    (syntax-case args ()
      (()
       (check req (reverse ropt) #f '()))
      ((a . b) (id? #'a)
       (opt #'b req (cons #'(a #f) ropt)))
      (((a init) . b) (id? #'a)
       (opt #'b req (cons #'(a init) ropt)))
      ((a . b) (eq? (syntax->datum #'a) #:key)
       (key #'b req (reverse ropt) '()))
      ((a b) (eq? (syntax->datum #'a) #:rest)
       (rest #'b req (reverse ropt) '()))
      (r (id? #'r)
         (rest #'r req (reverse ropt) '()))
      (else
       (syntax-violation 'lambda* "invalid optional argument list"
                         orig-args args))))
  (define (key args req opt rkey)
    (syntax-case args ()
      (()
       (check req opt #f (cons #f (reverse rkey))))
      ((a . b) (id? #'a)
       (with-syntax ((k (symbol->keyword (syntax->datum #'a))))
         (key #'b req opt (cons #'(k a #f) rkey))))
      (((a init) . b) (id? #'a)
       (with-syntax ((k (symbol->keyword (syntax->datum #'a))))
         (key #'b req opt (cons #'(k a init) rkey))))
      (((a init k) . b) (and (id? #'a)
                             (keyword? (syntax->datum #'k)))
       (key #'b req opt (cons #'(k a init) rkey)))
      ((aok) (eq? (syntax->datum #'aok) #:allow-other-keys)
       (check req opt #f (cons #t (reverse rkey))))
      ((aok a b) (and (eq? (syntax->datum #'aok) #:allow-other-keys)
                      (eq? (syntax->datum #'a) #:rest))
       (rest #'b req opt (cons #t (reverse rkey))))
      ((aok . r) (and (eq? (syntax->datum #'aok) #:allow-other-keys)
                      (id? #'r))
       (rest #'r req opt (cons #t (reverse rkey))))
      ((a b) (eq? (syntax->datum #'a) #:rest)
       (rest #'b req opt (cons #f (reverse rkey))))
      (r (id? #'r)
         (rest #'r req opt (cons #f (reverse rkey))))
      (else
       (syntax-violation 'lambda* "invalid keyword argument list"
                         orig-args args))))
  (define (rest args req opt kw)
    (syntax-case args ()
      (r (id? #'r)
         (check req opt #'r kw))
      (else
       (syntax-violation 'lambda* "invalid rest argument"
                         orig-args args))))
  (define (check req opt rest kw)
    (cond
     ((distinct-bound-ids?
       (append req (map car opt) (if rest (list rest) '())
               (if (pair? kw) (map cadr (cdr kw)) '())))
      (values req opt rest kw))
     (else
      (syntax-violation 'lambda* "duplicate identifier in argument list"
                        orig-args))))
  (req orig-args '()))

(define (expand-lambda-case e r w s get-formals clauses)
  (define (parse-req req opt rest kw body)
    (let ((vars (map gen-var req))
          (labels (gen-labels req)))
      (let ((r* (extend-var-env labels vars r))
            (w* (make-binding-wrap req labels w)))
        (parse-opt (map syntax->datum req)
                   opt rest kw body (reverse vars) r* w* '() '()))))
  (define (parse-opt req opt rest kw body vars r* w* out inits)
    (cond
     ((pair? opt)
      (syntax-case (car opt) ()
        ((id i)
         (let* ((v (gen-var #'id))
                (l (gen-labels (list v)))
                (r** (extend-var-env l (list v) r*))
                (w** (make-binding-wrap (list #'id) l w*)))
           (parse-opt req (cdr opt) rest kw body (cons v vars)
                      r** w** (cons (syntax->datum #'id) out)
                      (cons (expand #'i r* w*) inits))))))
     (rest
      (let* ((v (gen-var rest))
             (l (gen-labels (list v)))
             (r* (extend-var-env l (list v) r*))
             (w* (make-binding-wrap (list rest) l w*)))
        (parse-kw req (if (pair? out) (reverse out) #f)
                  (syntax->datum rest)
                  (if (pair? kw) (cdr kw) kw)
                  body (cons v vars) r* w* 
                  (if (pair? kw) (car kw) #f)
                  '() inits)))
     (else
      (parse-kw req (if (pair? out) (reverse out) #f) #f
                (if (pair? kw) (cdr kw) kw)
                body vars r* w*
                (if (pair? kw) (car kw) #f)
                '() inits))))
  (define (parse-kw req opt rest kw body vars r* w* aok out inits)
    (cond
     ((pair? kw)
      (syntax-case (car kw) ()
        ((k id i)
         (let* ((v (gen-var #'id))
                (l (gen-labels (list v)))
                (r** (extend-var-env l (list v) r*))
                (w** (make-binding-wrap (list #'id) l w*)))
           (parse-kw req opt rest (cdr kw) body (cons v vars)
                     r** w** aok
                     (cons (list (syntax->datum #'k)
                                 (syntax->datum #'id)
                                 v)
                           out)
                     (cons (expand #'i r* w*) inits))))))
     (else
      (parse-body req opt rest
                  (if (or aok (pair? out)) (cons aok (reverse out)) #f)
                  body (reverse vars) r* w* (reverse inits) '()))))
  (define (parse-body req opt rest kw body vars r* w* inits meta)
    (syntax-case body ()
      ((docstring e1 e2 ...) (string? (syntax->datum #'docstring))
       (parse-body req opt rest kw #'(e1 e2 ...) vars r* w* inits
                   (append meta 
                           `((documentation
                              . ,(syntax->datum #'docstring))))))
      ((#((k . v) ...) e1 e2 ...) 
       (parse-body req opt rest kw #'(e1 e2 ...) vars r* w* inits
                   (append meta (syntax->datum #'((k . v) ...)))))
      ((e1 e2 ...)
       (values meta req opt rest kw inits vars
               (expand-body #'(e1 e2 ...) (source-wrap e w s)
                            r* w*)))))

  (syntax-case clauses ()
    (() (values '() #f))
    (((args e1 e2 ...) (args* e1* e2* ...) ...)
     (call-with-values (lambda () (get-formals #'args))
       (lambda (req opt rest kw)
         (call-with-values (lambda ()
                             (parse-req req opt rest kw #'(e1 e2 ...)))
           (lambda (meta req opt rest kw inits vars body)
             (call-with-values
                 (lambda ()
                   (expand-lambda-case e r w s get-formals
                                       #'((args* e1* e2* ...) ...)))
               (lambda (meta* else*)
                 (values
                  (append meta meta*)
                  (build-lambda-case s req opt rest kw inits vars
                                     body else*)))))))))))

;; data

;; strips syntax-objects down to top-wrap
;;
;; since only the head of a list is annotated by the reader, not each pair
;; in the spine, we also check for pairs whose cars are annotated in case
;; we've been passed the cdr of an annotated list

(define (strip x w)
  (if (top-marked? w)
      x
      (let f ((x x))
        (cond
         ((syntax-object? x)
          (strip (syntax-object-expression x) (syntax-object-wrap x)))
         ((pair? x)
          (let ((a (f (car x))) (d (f (cdr x))))
            (if (and (eq? a (car x)) (eq? d (cdr x)))
                x
                (cons a d))))
         ((vector? x)
          (let ((old (vector->list x)))
            (let ((new (map f old)))
              ;; inlined and-map with two args
              (let lp ((l1 old) (l2 new))
                (if (null? l1)
                    x
                    (if (eq? (car l1) (car l2))
                        (lp (cdr l1) (cdr l2))
                        (list->vector new)))))))
         (else x)))))

;; lexical variables

(define (gen-var id)
  (let ((id (if (syntax-object? id) (syntax-object-expression id) id)))
    (build-lexical-var no-source id)))

;; appears to return a reversed list
(define (lambda-var-list vars)
  (let lvl ((vars vars) (ls '()) (w empty-wrap))
    (cond
     ((pair? vars) (lvl (cdr vars) (cons (wrap (car vars) w) ls) w))
     ((id? vars) (cons (wrap vars w) ls))
     ((null? vars) ls)
     ((syntax-object? vars)
      (lvl (syntax-object-expression vars)
           ls
           (join-wraps w (syntax-object-wrap vars))))
     ;; include anything else to be caught by subsequent error
     ;; checking
     (else (cons vars ls)))))

;; core transformers

(global-extend 'local-syntax 'letrec-syntax #t)
(global-extend 'local-syntax 'let-syntax #f)

(global-extend
 'core 'syntax-parameterize
 (lambda (e r w s)
   (syntax-case e ()
     ((_ ((var val) ...) e1 e2 ...)
      (valid-bound-ids? #'(var ...))
      (let ((names
             (map (lambda (x)
                    (call-with-values
                        (lambda () (resolve-identifier x w r #f))
                      (lambda (type value)
                        (case type
                          ((displaced-lexical)
                           (syntax-violation 'syntax-parameterize
                                             "identifier out of context"
                                             e
                                             (source-wrap x w s)))
                          ((syntax-parameter)
                           value)
                          (else
                           (syntax-violation 'syntax-parameterize
                                             "invalid syntax parameter"
                                             e
                                             (source-wrap x w s)))))))
                  #'(var ...)))
            (bindings
             (let ((trans-r (macros-only-env r)))
               (map (lambda (x)
                      (make-binding
                       'macro
                       (eval-local-transformer (expand x trans-r w))))
                    #'(val ...)))))
        (expand-body #'(e1 e2 ...)
                     (source-wrap e w s)
                     (extend-env names bindings r)
                     w)))
     (_ (syntax-violation 'syntax-parameterize "bad syntax"
                          (source-wrap e w s))))))

(global-extend 'core 'quote
               (lambda (e r w s)
                 (syntax-case e ()
                   ((_ e) (build-data s (strip #'e w)))
                   (_ (syntax-violation 'quote "bad syntax"
                                        (source-wrap e w s))))))

(global-extend
 'core 'syntax
 (let ()
   (define (gen-syntax src e r maps ellipsis?)
     (if (id? e)
         (call-with-values (lambda ()
                             (resolve-identifier e empty-wrap r #f))
           (lambda (type value)
             (case type
               ((syntax)
                (call-with-values
                    (lambda () (gen-ref src (car value) (cdr value) maps))
                  (lambda (var maps)
                    (values `(ref ,var) maps))))
               (else
                (if (ellipsis? e r)
                    (syntax-violation 'syntax "misplaced ellipsis" src)
                    (values `(quote ,e) maps))))))
         (syntax-case e ()
           ((dots e)
            (ellipsis? #'dots r)
            (gen-syntax src #'e r maps (lambda (e r) #f)))
           ((x dots . y)
            ;; this could be about a dozen lines of code, except that we
            ;; choose to handle #'(x ... ...) forms
            (ellipsis? #'dots r)
            (let f ((y #'y)
                    (k (lambda (maps)
                         (call-with-values
                             (lambda ()
                               (gen-syntax src #'x r
                                           (cons '() maps) ellipsis?))
                           (lambda (x maps)
                             (if (null? (car maps))
                                 (syntax-violation 'syntax "extra ellipsis"
                                                   src)
                                 (values (gen-map x (car maps))
                                         (cdr maps))))))))
              (syntax-case y ()
                ((dots . y)
                 (ellipsis? #'dots r)
                 (f #'y
                    (lambda (maps)
                      (call-with-values
                          (lambda () (k (cons '() maps)))
                        (lambda (x maps)
                          (if (null? (car maps))
                              (syntax-violation 'syntax "extra ellipsis" src)
                              (values (gen-mappend x (car maps))
                                      (cdr maps))))))))
                (_ (call-with-values
                       (lambda () (gen-syntax src y r maps ellipsis?))
                     (lambda (y maps)
                       (call-with-values
                           (lambda () (k maps))
                         (lambda (x maps)
                           (values (gen-append x y) maps)))))))))
           ((x . y)
            (call-with-values
                (lambda () (gen-syntax src #'x r maps ellipsis?))
              (lambda (x maps)
                (call-with-values
                    (lambda () (gen-syntax src #'y r maps ellipsis?))
                  (lambda (y maps) (values (gen-cons x y) maps))))))
           (#(e1 e2 ...)
            (call-with-values
                (lambda ()
                  (gen-syntax src #'(e1 e2 ...) r maps ellipsis?))
              (lambda (e maps) (values (gen-vector e) maps))))
           (_ (values `(quote ,e) maps)))))

   (define (gen-ref src var level maps)
     (if (fx= level 0)
         (values var maps)
         (if (null? maps)
             (syntax-violation 'syntax "missing ellipsis" src)
             (call-with-values
                 (lambda () (gen-ref src var (fx- level 1) (cdr maps)))
               (lambda (outer-var outer-maps)
                 (let ((b (assq outer-var (car maps))))
                   (if b
                       (values (cdr b) maps)
                       (let ((inner-var (gen-var 'tmp)))
                         (values inner-var
                                 (cons (cons (cons outer-var inner-var)
                                             (car maps))
                                       outer-maps))))))))))

   (define (gen-mappend e map-env)
     `(apply (primitive append) ,(gen-map e map-env)))

   (define (gen-map e map-env)
     (let ((formals (map cdr map-env))
           (actuals (map (lambda (x) `(ref ,(car x))) map-env)))
       (cond
        ((eq? (car e) 'ref)
         ;; identity map equivalence:
         ;; (map (lambda (x) x) y) == y
         (car actuals))
        ((and-map
          (lambda (x) (and (eq? (car x) 'ref) (memq (cadr x) formals)))
          (cdr e))
         ;; eta map equivalence:
         ;; (map (lambda (x ...) (f x ...)) y ...) == (map f y ...)
         `(map (primitive ,(car e))
               ,@(map (let ((r (map cons formals actuals)))
                        (lambda (x) (cdr (assq (cadr x) r))))
                      (cdr e))))
        (else `(map (lambda ,formals ,e) ,@actuals)))))

   (define (gen-cons x y)
     (case (car y)
       ((quote)
        (if (eq? (car x) 'quote)
            `(quote (,(cadr x) . ,(cadr y)))
            (if (eq? (cadr y) '())
                `(list ,x)
                `(cons ,x ,y))))
       ((list) `(list ,x ,@(cdr y)))
       (else `(cons ,x ,y))))

   (define (gen-append x y)
     (if (equal? y '(quote ()))
         x
         `(append ,x ,y)))

   (define (gen-vector x)
     (cond
      ((eq? (car x) 'list) `(vector ,@(cdr x)))
      ((eq? (car x) 'quote) `(quote #(,@(cadr x))))
      (else `(list->vector ,x))))


   (define (regen x)
     (case (car x)
       ((ref) (build-lexical-reference 'value no-source (cadr x) (cadr x)))
       ((primitive) (build-primref no-source (cadr x)))
       ((quote) (build-data no-source (cadr x)))
       ((lambda)
        (if (list? (cadr x))
            (build-simple-lambda no-source (cadr x) #f (cadr x) '() (regen (caddr x)))
            (error "how did we get here" x)))
       (else (build-primcall no-source (car x) (map regen (cdr x))))))

   (lambda (e r w s)
     (let ((e (source-wrap e w s)))
       (syntax-case e ()
         ((_ x)
          (call-with-values
              (lambda () (gen-syntax e #'x r '() ellipsis?))
            (lambda (e maps) (regen e))))
         (_ (syntax-violation 'syntax "bad `syntax' form" e)))))))

(global-extend
 'core 'lambda
 (lambda (e r w s)
   (syntax-case e ()
     ((_ args e1 e2 ...)
      (call-with-values (lambda () (lambda-formals #'args))
        (lambda (req opt rest kw)
          (let lp ((body #'(e1 e2 ...)) (meta '()))
            (syntax-case body ()
              ((docstring e1 e2 ...) (string? (syntax->datum #'docstring))
               (lp #'(e1 e2 ...)
                   (append meta
                           `((documentation
                              . ,(syntax->datum #'docstring))))))
              ((#((k . v) ...) e1 e2 ...) 
               (lp #'(e1 e2 ...)
                   (append meta (syntax->datum #'((k . v) ...)))))
              (_ (expand-simple-lambda e r w s req rest meta body)))))))
     (_ (syntax-violation 'lambda "bad lambda" e)))))

(global-extend
 'core 'lambda*
 (lambda (e r w s)
   (syntax-case e ()
     ((_ args e1 e2 ...)
      (call-with-values
          (lambda ()
            (expand-lambda-case e r w s
                                lambda*-formals #'((args e1 e2 ...))))
        (lambda (meta lcase)
          (build-case-lambda s meta lcase))))
     (_ (syntax-violation 'lambda "bad lambda*" e)))))

(global-extend
 'core 'case-lambda
 (lambda (e r w s)
   (define (build-it meta clauses)
     (call-with-values
         (lambda ()
           (expand-lambda-case e r w s
                               lambda-formals
                               clauses))
       (lambda (meta* lcase)
         (build-case-lambda s (append meta meta*) lcase))))
   (syntax-case e ()
     ((_ (args e1 e2 ...) ...)
      (build-it '() #'((args e1 e2 ...) ...)))
     ((_ docstring (args e1 e2 ...) ...)
      (string? (syntax->datum #'docstring))
      (build-it `((documentation
                   . ,(syntax->datum #'docstring)))
                #'((args e1 e2 ...) ...)))
     (_ (syntax-violation 'case-lambda "bad case-lambda" e)))))

(global-extend
 'core 'case-lambda*
 (lambda (e r w s)
   (define (build-it meta clauses)
     (call-with-values
         (lambda ()
           (expand-lambda-case e r w s
                               lambda*-formals
                               clauses))
       (lambda (meta* lcase)
         (build-case-lambda s (append meta meta*) lcase))))
   (syntax-case e ()
     ((_ (args e1 e2 ...) ...)
      (build-it '() #'((args e1 e2 ...) ...)))
     ((_ docstring (args e1 e2 ...) ...)
      (string? (syntax->datum #'docstring))
      (build-it `((documentation
                   . ,(syntax->datum #'docstring)))
                #'((args e1 e2 ...) ...)))
     (_ (syntax-violation 'case-lambda "bad case-lambda*" e)))))

(global-extend
 'core 'with-ellipsis
 (lambda (e r w s)
   (syntax-case e ()
     ((_ dots e1 e2 ...)
      (id? #'dots)
      (let ((id (if (symbol? #'dots)
                    '#{ $sc-ellipsis }#
                    (make-syntax-object '#{ $sc-ellipsis }#
                                        (syntax-object-wrap #'dots)
                                        #f))))
        (let ((ids (list id))
              (labels (list (gen-label)))
              (bindings (list (make-binding 'ellipsis (source-wrap #'dots w s)))))
          (let ((nw (make-binding-wrap ids labels w))
                (nr (extend-env labels bindings r)))
            (expand-body #'(e1 e2 ...) (source-wrap e nw s) nr nw)))))
     (_ (syntax-violation 'with-ellipsis "bad syntax"
                          (source-wrap e w s))))))

(global-extend
 'core 'let
 (let ()
   (define (expand-let e r w s constructor ids vals exps)
     (if (not (valid-bound-ids? ids))
         (syntax-violation 'let "duplicate bound variable" e)
         (let ((labels (gen-labels ids))
               (new-vars (map gen-var ids)))
           (let ((nw (make-binding-wrap ids labels w))
                 (nr (extend-var-env labels new-vars r)))
             (constructor s
                          (map syntax->datum ids)
                          new-vars
                          (map (lambda (x) (expand x r w)) vals)
                          (expand-body exps (source-wrap e nw s)
                                       nr nw))))))
   (lambda (e r w s)
     (syntax-case e ()
       ((_ ((id val) ...) e1 e2 ...)
        (and-map id? #'(id ...))
        (expand-let e r w s
                    build-let
                    #'(id ...)
                    #'(val ...)
                    #'(e1 e2 ...)))
       ((_ f ((id val) ...) e1 e2 ...)
        (and (id? #'f) (and-map id? #'(id ...)))
        (expand-let e r w s
                    build-named-let
                    #'(f id ...)
                    #'(val ...)
                    #'(e1 e2 ...)))
       (_ (syntax-violation 'let "bad let" (source-wrap e w s)))))))


(global-extend
 'core 'letrec
 (lambda (e r w s)
   (syntax-case e ()
     ((_ ((id val) ...) e1 e2 ...)
      (and-map id? #'(id ...))
      (let ((ids #'(id ...)))
        (if (not (valid-bound-ids? ids))
            (syntax-violation 'letrec "duplicate bound variable" e)
            (let ((labels (gen-labels ids))
                  (new-vars (map gen-var ids)))
              (let ((w (make-binding-wrap ids labels w))
                    (r (extend-var-env labels new-vars r)))
                (build-letrec s #f
                              (map syntax->datum ids)
                              new-vars
                              (map (lambda (x) (expand x r w)) #'(val ...))
                              (expand-body #'(e1 e2 ...) 
                                           (source-wrap e w s) r w)))))))
     (_ (syntax-violation 'letrec "bad letrec" (source-wrap e w s))))))


(global-extend
 'core 'letrec*
 (lambda (e r w s)
   (syntax-case e ()
     ((_ ((id val) ...) e1 e2 ...)
      (and-map id? #'(id ...))
      (let ((ids #'(id ...)))
        (if (not (valid-bound-ids? ids))
            (syntax-violation 'letrec* "duplicate bound variable" e)
            (let ((labels (gen-labels ids))
                  (new-vars (map gen-var ids)))
              (let ((w (make-binding-wrap ids labels w))
                    (r (extend-var-env labels new-vars r)))
                (build-letrec s #t
                              (map syntax->datum ids)
                              new-vars
                              (map (lambda (x) (expand x r w)) #'(val ...))
                              (expand-body #'(e1 e2 ...) 
                                           (source-wrap e w s) r w)))))))
     (_ (syntax-violation 'letrec* "bad letrec*" (source-wrap e w s))))))


(global-extend
 'core 'set!
 (lambda (e r w s)
   (syntax-case e ()
     ((_ id val)
      (id? #'id)
      (call-with-values
          (lambda () (resolve-identifier #'id w r #t))
        (lambda (type value)
          (case type
            ((lexical)
             (build-lexical-assignment s (syntax->datum #'id) value
                                       (expand #'val r w)))
            ((global)
             (syntax-violation
              'set!
              "assignment to top-level variable not allowed in bicho"
              (wrap #'id w)))
            ((macro)
             (if (procedure-property value 'variable-transformer)
                 (expand (expand-macro value e r w s #f) r empty-wrap)
                 (syntax-violation 'set! "not a variable transformer"
                                   (wrap e w)
                                   (wrap #'id w))))
            ((displaced-lexical)
             (syntax-violation 'set! "identifier out of context"
                               (wrap #'id w)))
            (else
             (syntax-violation 'set! "bad set!" (source-wrap e w s)))))))
     (_ (syntax-violation 'set! "bad set!" (source-wrap e w s))))))

(global-extend
 'core 'if
 (lambda (e r w s)
   (syntax-case e ()
     ((_ test then)
      (build-conditional
       s
       (expand #'test r w)
       (expand #'then r w)
       (build-void no-source)))
     ((_ test then else)
      (build-conditional
       s
       (expand #'test r w)
       (expand #'then r w)
       (expand #'else r w))))))

(global-extend 'begin 'begin '())

(global-extend 'define 'define '())

(global-extend 'define-syntax 'define-syntax '())
(global-extend 'define-syntax-parameter 'define-syntax-parameter '())

(global-extend
 'core 'syntax-case
 (let ()
   (define (convert-pattern pattern keys ellipsis?)
     ;; accepts pattern & keys
     ;; returns $sc-dispatch pattern & ids
     (define (cvt* p* n ids)
       (syntax-case p* ()
         ((x . y)
          (call-with-values
              (lambda () (cvt* #'y n ids))
            (lambda (y ids)
              (call-with-values
                  (lambda () (cvt #'x n ids))
                (lambda (x ids)
                  (values (cons x y) ids))))))
         (_ (cvt p* n ids))))
                   
     (define (v-reverse x)
       (let loop ((r '()) (x x))
         (if (not (pair? x))
             (values r x)
             (loop (cons (car x) r) (cdr x)))))

     (define (cvt p n ids)
       (if (id? p)
           (cond
            ((bound-id-member? p keys)
             (values (vector 'free-id p) ids))
            ((free-id=? p #'_)
             (values '_ ids))
            (else
             (values 'any (cons (cons p n) ids))))
           (syntax-case p ()
             ((x dots)
              (ellipsis? (syntax dots))
              (call-with-values
                  (lambda () (cvt (syntax x) (fx+ n 1) ids))
                (lambda (p ids)
                  (values (if (eq? p 'any) 'each-any (vector 'each p))
                          ids))))
             ((x dots . ys)
              (ellipsis? (syntax dots))
              (call-with-values
                  (lambda () (cvt* (syntax ys) n ids))
                (lambda (ys ids)
                  (call-with-values
                      (lambda () (cvt (syntax x) (+ n 1) ids))
                    (lambda (x ids)
                      (call-with-values
                          (lambda () (v-reverse ys))
                        (lambda (ys e)
                          (values `#(each+ ,x ,ys ,e) 
                                  ids))))))))
             ((x . y)
              (call-with-values
                  (lambda () (cvt (syntax y) n ids))
                (lambda (y ids)
                  (call-with-values
                      (lambda () (cvt (syntax x) n ids))
                    (lambda (x ids)
                      (values (cons x y) ids))))))
             (() (values '() ids))
             (#(x ...)
              (call-with-values
                  (lambda () (cvt (syntax (x ...)) n ids))
                (lambda (p ids) (values (vector 'vector p) ids))))
             (x (values (vector 'atom (strip p empty-wrap)) ids)))))
     (cvt pattern 0 '()))

   (define (build-dispatch-call pvars exp y r)
     (let ((ids (map car pvars)) (levels (map cdr pvars)))
       (let ((labels (gen-labels ids)) (new-vars (map gen-var ids)))
         (build-primcall
          no-source
          'apply
          (list (build-simple-lambda no-source (map syntax->datum ids) #f new-vars '()
                                     (expand exp
                                             (extend-env
                                              labels
                                              (map (lambda (var level)
                                                     (make-binding 'syntax `(,var . ,level)))
                                                   new-vars
                                                   (map cdr pvars))
                                              r)
                                             (make-binding-wrap ids labels empty-wrap)))
                y)))))

   (define (gen-clause x keys clauses r pat fender exp)
     (call-with-values
         (lambda () (convert-pattern pat keys (lambda (e) (ellipsis? e r))))
       (lambda (p pvars)
         (cond
          ((not (and-map (lambda (x) (not (ellipsis? (car x) r))) pvars))
           (syntax-violation 'syntax-case "misplaced ellipsis" pat))
          ((not (distinct-bound-ids? (map car pvars)))
           (syntax-violation 'syntax-case "duplicate pattern variable" pat))
          (else
           (let ((y (gen-var 'tmp)))
             ;; fat finger binding and references to temp variable y
             (build-call no-source
                         (build-simple-lambda no-source (list 'tmp) #f (list y) '()
                                              (let ((y (build-lexical-reference 'value no-source
                                                                                'tmp y)))
                                                (build-conditional no-source
                                                                   (syntax-case fender ()
                                                                     (#t y)
                                                                     (_ (build-conditional no-source
                                                                                           y
                                                                                           (build-dispatch-call pvars fender y r)
                                                                                           (build-data no-source #f))))
                                                                   (build-dispatch-call pvars exp y r)
                                                                   (gen-syntax-case x keys clauses r))))
                         (list (if (eq? p 'any)
                                   (build-primcall no-source 'list (list x))
                                   (build-call no-source
                                               (build-data no-source $sc-dispatch)
                                               (list x (build-data no-source p))))))))))))

   (define (gen-syntax-case x keys clauses r)
     (if (null? clauses)
         (build-primcall no-source 'syntax-violation
                         (list (build-data no-source #f)
                               (build-data no-source
                                           "source expression failed to match any pattern")
                               x))
         (syntax-case (car clauses) ()
           ((pat exp)
            (if (and (id? #'pat)
                     (and-map (lambda (x) (not (free-id=? #'pat x)))
                              (cons #'(... ...) keys)))
                (if (free-id=? #'pat #'_)
                    (expand #'exp r empty-wrap)
                    (let ((labels (list (gen-label)))
                          (var (gen-var #'pat)))
                      (build-call no-source
                                  (build-simple-lambda
                                   no-source (list (syntax->datum #'pat)) #f (list var)
                                   '()
                                   (expand #'exp
                                           (extend-env labels
                                                       (list (make-binding 'syntax `(,var . 0)))
                                                       r)
                                           (make-binding-wrap #'(pat)
                                                              labels empty-wrap)))
                                  (list x))))
                (gen-clause x keys (cdr clauses) r
                            #'pat #t #'exp)))
           ((pat fender exp)
            (gen-clause x keys (cdr clauses) r
                        #'pat #'fender #'exp))
           (_ (syntax-violation 'syntax-case "invalid clause"
                                (car clauses))))))

   (lambda (e r w s)
     (let ((e (source-wrap e w s)))
       (syntax-case e ()
         ((_ val (key ...) m ...)
          (if (and-map (lambda (x) (and (id? x) (not (ellipsis? x r))))
                       #'(key ...))
              (let ((x (gen-var 'tmp)))
                ;; fat finger binding and references to temp variable x
                (build-call s
                            (build-simple-lambda
                             no-source (list 'tmp) #f (list x) '()
                             (gen-syntax-case
                              (build-lexical-reference 'value no-source
                                                       'tmp x)
                              #'(key ...) #'(m ...) r))
                            (list (expand #'val r empty-wrap))))
              (syntax-violation 'syntax-case "invalid literals list" e))))))))

(define (macroexpand x)
  (expand-top-sequence (list x) null-env top-wrap #f))

(define (identifier? x)
  (nonsymbol-id? x))

(define (datum->syntax id datum)
  (make-syntax-object datum (syntax-object-wrap id) #f))

(define (syntax->datum x)
  ;; accepts any object, since syntax objects may consist partially
  ;; or entirely of unwrapped, nonsymbolic data
  (strip x empty-wrap))

(define (syntax-source x)
  (source-annotation x))

(define (generate-temporaries ls)
  (arg-check list? ls 'generate-temporaries)
  (map (lambda (x) (wrap (gensym "t-") top-wrap)) ls))

(define (free-identifier=? x y)
  (arg-check nonsymbol-id? x 'free-identifier=?)
  (arg-check nonsymbol-id? y 'free-identifier=?)
  (free-id=? x y))

(define (bound-identifier=? x y)
  (arg-check nonsymbol-id? x 'bound-identifier=?)
  (arg-check nonsymbol-id? y 'bound-identifier=?)
  (bound-id=? x y))

(define* (syntax-violation who message form #:optional subform)
  (arg-check (lambda (x) (or (not x) (string? x) (symbol? x)))
             who 'syntax-violation)
  (arg-check string? message 'syntax-violation)
  (throw 'syntax-error who message
         (or (source-annotation subform)
             (source-annotation form))
         (strip form empty-wrap)
         (and subform (strip subform empty-wrap))))

(define* (syntax-local-binding id #:key (resolve-syntax-parameters? #t))
  (arg-check nonsymbol-id? id 'syntax-local-binding)
  (with-transformer-environment
   (lambda (e r w s rib)
     (define (strip-anti-mark w)
       (let ((ms (wrap-marks w)) (s (wrap-subst w)))
         (if (and (pair? ms) (eq? (car ms) the-anti-mark))
             ;; output is from original text
             (make-wrap (cdr ms) (if rib (cons rib (cdr s)) (cdr s)))
             ;; output introduced by macro
             (make-wrap ms (if rib (cons rib s) s)))))
     (call-with-values (lambda ()
                         (resolve-identifier
                          (syntax-object-expression id)
                          (strip-anti-mark (syntax-object-wrap id))
                          r
                          resolve-syntax-parameters?))
       (lambda (type value)
         (case type
           ((lexical) (values 'lexical value))
           ((macro) (values 'macro value))
           ((syntax-parameter) (values 'syntax-parameter (car value)))
           ((syntax) (values 'pattern-variable value))
           ((displaced-lexical) (values 'displaced-lexical #f))
           ((global) (values 'global value))
           ((ellipsis)
            (values 'ellipsis
                    (make-syntax-object (syntax-object-expression value)
                                        (anti-mark (syntax-object-wrap value))
                                        #f)))
           (else (values 'other #f))))))))

(define (syntax-locally-bound-identifiers id)
  (arg-check nonsymbol-id? id 'syntax-locally-bound-identifiers)
  (locally-bound-identifiers (syntax-object-wrap id)))

;; $sc-dispatch expects an expression and a pattern.  If the expression
;; matches the pattern a list of the matching expressions for each
;; "any" is returned.  Otherwise, #f is returned.  (This use of #f will
;; not work on r4rs implementations that violate the ieee requirement
;; that #f and () be distinct.)

;; The expression is matched with the pattern as follows:

;; pattern:                           matches:
;;   ()                                 empty list
;;   any                                anything
;;   (<pattern>1 . <pattern>2)          (<pattern>1 . <pattern>2)
;;   each-any                           (any*)
;;   #(free-id <key>)                   <key> with free-identifier=?
;;   #(each <pattern>)                  (<pattern>*)
;;   #(each+ p1 (p2_1 ... p2_n) p3)      (p1* (p2_n ... p2_1) . p3)
;;   #(vector <pattern>)                (list->vector <pattern>)
;;   #(atom <object>)                   <object> with "equal?"

;; Vector cops out to pair under assumption that vectors are rare.  If
;; not, should convert to:
;;   #(vector <pattern>*)               #(<pattern>*)

(define $sc-dispatch
  (let ()
    (define (match-each e p w)
      (cond
       ((pair? e)
        (let ((first (match (car e) p w '())))
          (and first
               (let ((rest (match-each (cdr e) p w)))
                 (and rest (cons first rest))))))
       ((null? e) '())
       ((syntax-object? e)
        (match-each (syntax-object-expression e)
                    p
                    (join-wraps w (syntax-object-wrap e))))
       (else #f)))

    (define (match-each+ e x-pat y-pat z-pat w r)
      (let f ((e e) (w w))
        (cond
         ((pair? e)
          (call-with-values (lambda () (f (cdr e) w))
            (lambda (xr* y-pat r)
              (if r
                  (if (null? y-pat)
                      (let ((xr (match (car e) x-pat w '())))
                        (if xr
                            (values (cons xr xr*) y-pat r)
                            (values #f #f #f)))
                      (values
                       '()
                       (cdr y-pat)
                       (match (car e) (car y-pat) w r)))
                  (values #f #f #f)))))
         ((syntax-object? e)
          (f (syntax-object-expression e) (join-wraps w e)))
         (else
          (values '() y-pat (match e z-pat w r))))))

    (define (match-each-any e w)
      (cond
       ((pair? e)
        (let ((l (match-each-any (cdr e) w)))
          (and l (cons (wrap (car e) w) l))))
       ((null? e) '())
       ((syntax-object? e)
        (match-each-any (syntax-object-expression e)
                        (join-wraps w (syntax-object-wrap e))))
       (else #f)))

    (define (match-empty p r)
      (cond
       ((null? p) r)
       ((eq? p '_) r)
       ((eq? p 'any) (cons '() r))
       ((pair? p) (match-empty (car p) (match-empty (cdr p) r)))
       ((eq? p 'each-any) (cons '() r))
       (else
        (case (vector-ref p 0)
          ((each) (match-empty (vector-ref p 1) r))
          ((each+) (match-empty (vector-ref p 1)
                                (match-empty
                                 (reverse (vector-ref p 2))
                                 (match-empty (vector-ref p 3) r))))
          ((free-id atom) r)
          ((vector) (match-empty (vector-ref p 1) r))))))

    (define (combine r* r)
      (if (null? (car r*))
          r
          (cons (map car r*) (combine (map cdr r*) r))))

    (define (match* e p w r)
      (cond
       ((null? p) (and (null? e) r))
       ((pair? p)
        (and (pair? e) (match (car e) (car p) w
                         (match (cdr e) (cdr p) w r))))
       ((eq? p 'each-any)
        (let ((l (match-each-any e w))) (and l (cons l r))))
       (else
        (case (vector-ref p 0)
          ((each)
           (if (null? e)
               (match-empty (vector-ref p 1) r)
               (let ((l (match-each e (vector-ref p 1) w)))
                 (and l
                      (let collect ((l l))
                        (if (null? (car l))
                            r
                            (cons (map car l) (collect (map cdr l)))))))))
          ((each+)
           (call-with-values
               (lambda ()
                 (match-each+ e (vector-ref p 1) (vector-ref p 2) (vector-ref p 3) w r))
             (lambda (xr* y-pat r)
               (and r
                    (null? y-pat)
                    (if (null? xr*)
                        (match-empty (vector-ref p 1) r)
                        (combine xr* r))))))
          ((free-id) (and (id? e) (free-id=? (wrap e w) (vector-ref p 1)) r))
          ((atom) (and (equal? (vector-ref p 1) (strip e w)) r))
          ((vector)
           (and (vector? e)
                (match (vector->list e) (vector-ref p 1) w r)))))))

    (define (match e p w r)
      (cond
       ((not r) #f)
       ((eq? p '_) r)
       ((eq? p 'any) (cons (wrap e w) r))
       ((syntax-object? e)
        (match* (syntax-object-expression e)
                p
                (join-wraps w (syntax-object-wrap e))
                r))
       (else
        (match* e p w r))))

    (lambda (e p)
      (cond
       ((eq? p 'any) (list e))
       ((eq? p '_) '())
       ((syntax-object? e)
        (match* (syntax-object-expression e)
                p (syntax-object-wrap e) '()))
       (else (match* e p empty-wrap '()))))))

(define (make-variable-transformer proc)
  (if (procedure? proc)
      (let ((trans (lambda (x)
                     #((macro-type . variable-transformer))
                     (proc x))))
        (set-procedure-property! trans 'variable-transformer #t)
        trans)
      (error "variable transformer not a procedure" proc)))

(define-syntax-rule (export-syntax-helpers! name ...)
  (begin
    (add-compile-time-value! 'name name)
    ...))

(export-syntax-helpers!
 identifier? datum->syntax syntax->datum syntax-source
 generate-temporaries
 free-identifier=? bound-identifier=?
 syntax-violation
 syntax-local-binding syntax-locally-bound-identifiers
 $sc-dispatch
 make-variable-transformer)

(macroexpand
 '(begin
    (define-syntax and
      (lambda (x)
        (syntax-case x ()
          ((_) #'#t)
          ((_ x) #'x)
          ;; Avoid ellipsis, which would lead to quadratic expansion time.
          ((_ x . y) #'(if x (and . y) #f)))))

    (define-syntax or
      (lambda (x)
        (syntax-case x ()
          ((_) #'#f)
          ((_ x) #'x)
          ;; Avoid ellipsis, which would lead to quadratic expansion time.
          ((_ x . y) #'(let ((t x)) (if t t (or . y)))))))

    (define-syntax with-syntax
      (lambda (x)
        (syntax-case x ()
          ((_ () e1 e2 ...)
           #'(let () e1 e2 ...))
          ((_ ((out in)) e1 e2 ...)
           #'(syntax-case in ()
               (out (let () e1 e2 ...))))
          ((_ ((out in) ...) e1 e2 ...)
           #'(syntax-case (list in ...) ()
               ((out ...) (let () e1 e2 ...)))))))

    (define-syntax syntax-error
      (lambda (x)
        (syntax-case x ()
          ;; Extended internal syntax which provides the original form
          ;; as the first operand, for improved error reporting.
          ((_ (keyword . operands) message arg ...)
           (string? (syntax->datum #'message))
           (syntax-violation (syntax->datum #'keyword)
                             (string-join (cons (syntax->datum #'message)
                                                (map (lambda (x)
                                                       (object->string
                                                        (syntax->datum x)))
                                                     #'(arg ...))))
                             (and (syntax->datum #'keyword)
                                  #'(keyword . operands))))
          ;; Standard R7RS syntax
          ((_ message arg ...)
           (string? (syntax->datum #'message))
           #'(syntax-error (#f) message arg ...)))))

    (define-syntax syntax-rules
      (lambda (xx)
        (define (expand-clause clause)
          ;; Convert a 'syntax-rules' clause into a 'syntax-case' clause.
          (syntax-case clause (syntax-error)
            ;; If the template is a 'syntax-error' form, use the extended
            ;; internal syntax, which adds the original form as the first
            ;; operand for improved error reporting.
            (((keyword . pattern) (syntax-error message arg ...))
             (string? (syntax->datum #'message))
             #'((dummy . pattern) #'(syntax-error (dummy . pattern) message arg ...)))
            ;; Normal case
            (((keyword . pattern) template)
             #'((dummy . pattern) #'template))))
        (define (expand-syntax-rules dots keys docstrings clauses)
          (with-syntax
              (((k ...) keys)
               ((docstring ...) docstrings)
               ((((keyword . pattern) template) ...) clauses)
               ((clause ...) (map expand-clause clauses)))
            (with-syntax
                ((form #'(lambda (x)
                           docstring ... ; optional docstring
                           #((macro-type . syntax-rules)
                             (patterns pattern ...)) ; embed patterns as procedure metadata
                           (syntax-case x (k ...)
                             clause ...))))
              (if dots
                  (with-syntax ((dots dots))
                    #'(with-ellipsis dots form))
                  #'form))))
        (syntax-case xx ()
          ((_ (k ...) ((keyword . pattern) template) ...)
           (expand-syntax-rules #f #'(k ...) #'() #'(((keyword . pattern) template) ...)))
          ((_ (k ...) docstring ((keyword . pattern) template) ...)
           (string? (syntax->datum #'docstring))
           (expand-syntax-rules #f #'(k ...) #'(docstring) #'(((keyword . pattern) template) ...)))
          ((_ dots (k ...) ((keyword . pattern) template) ...)
           (identifier? #'dots)
           (expand-syntax-rules #'dots #'(k ...) #'() #'(((keyword . pattern) template) ...)))
          ((_ dots (k ...) docstring ((keyword . pattern) template) ...)
           (and (identifier? #'dots) (string? (syntax->datum #'docstring)))
           (expand-syntax-rules #'dots #'(k ...) #'(docstring) #'(((keyword . pattern) template) ...))))))

    (define-syntax define-syntax-rule
      (lambda (x)
        (syntax-case x ()
          ((_ (name . pattern) template)
           #'(define-syntax name
               (syntax-rules ()
                 ((_ . pattern) template))))
          ((_ (name . pattern) docstring template)
           (string? (syntax->datum #'docstring))
           #'(define-syntax name
               (syntax-rules ()
                 docstring
                 ((_ . pattern) template)))))))

    (define-syntax let*
      (lambda (x)
        (syntax-case x ()
          ((let* ((x v) ...) e1 e2 ...)
           (and-map identifier? #'(x ...))
           (let f ((bindings #'((x v)  ...)))
             (if (null? bindings)
                 #'(let () e1 e2 ...)
                 (with-syntax ((body (f (cdr bindings)))
                               (binding (car bindings)))
                   #'(let (binding) body))))))))

    (define-syntax quasiquote
      (let ()
        (define (quasi p lev)
          (syntax-case p (unquote quasiquote)
            ((unquote p)
             (if (= lev 0)
                 #'("value" p)
                 (quasicons #'("quote" unquote) (quasi #'(p) (- lev 1)))))
            ((quasiquote p) (quasicons #'("quote" quasiquote) (quasi #'(p) (+ lev 1))))
            ((p . q)
             (syntax-case #'p (unquote unquote-splicing)
               ((unquote p ...)
                (if (= lev 0)
                    (quasilist* #'(("value" p) ...) (quasi #'q lev))
                    (quasicons
                     (quasicons #'("quote" unquote) (quasi #'(p ...) (- lev 1)))
                     (quasi #'q lev))))
               ((unquote-splicing p ...)
                (if (= lev 0)
                    (quasiappend #'(("value" p) ...) (quasi #'q lev))
                    (quasicons
                     (quasicons #'("quote" unquote-splicing) (quasi #'(p ...) (- lev 1)))
                     (quasi #'q lev))))
               (_ (quasicons (quasi #'p lev) (quasi #'q lev)))))
            (#(x ...) (quasivector (vquasi #'(x ...) lev)))
            (p #'("quote" p))))
        (define (vquasi p lev)
          (syntax-case p ()
            ((p . q)
             (syntax-case #'p (unquote unquote-splicing)
               ((unquote p ...)
                (if (= lev 0)
                    (quasilist* #'(("value" p) ...) (vquasi #'q lev))
                    (quasicons
                     (quasicons #'("quote" unquote) (quasi #'(p ...) (- lev 1)))
                     (vquasi #'q lev))))
               ((unquote-splicing p ...)
                (if (= lev 0)
                    (quasiappend #'(("value" p) ...) (vquasi #'q lev))
                    (quasicons
                     (quasicons
                      #'("quote" unquote-splicing)
                      (quasi #'(p ...) (- lev 1)))
                     (vquasi #'q lev))))
               (_ (quasicons (quasi #'p lev) (vquasi #'q lev)))))
            (() #'("quote" ()))))
        (define (quasicons x y)
          (with-syntax ((x x) (y y))
            (syntax-case #'y ()
              (("quote" dy)
               (syntax-case #'x ()
                 (("quote" dx) #'("quote" (dx . dy)))
                 (_ (if (null? #'dy) #'("list" x) #'("list*" x y)))))
              (("list" . stuff) #'("list" x . stuff))
              (("list*" . stuff) #'("list*" x . stuff))
              (_ #'("list*" x y)))))
        (define (quasiappend x y)
          (syntax-case y ()
            (("quote" ())
             (if (null? x)
                 #'("quote" ())
                 (if (null? (cdr x))
                     (car x)
                     (with-syntax (((p ...) x)) #'("append" p ...)))))
            (_
             (if (null? x)
                 y
                 (with-syntax (((p ...) x) (y y)) #'("append" p ... y))))))
        (define (quasilist* x y)
          (let f ((x x))
            (if (null? x)
                y
                (quasicons (car x) (f (cdr x))))))
        (define (quasivector x)
          (syntax-case x ()
            (("quote" (x ...)) #'("quote" #(x ...)))
            (_
             (let f ((y x) (k (lambda (ls) #`("vector" #,@ls))))
               (syntax-case y ()
                 (("quote" (y ...)) (k #'(("quote" y) ...)))
                 (("list" y ...) (k #'(y ...)))
                 (("list*" y ... z) (f #'z (lambda (ls) (k (append #'(y ...) ls)))))
                 (else #`("list->vector" #,x)))))))
        (define (emit x)
          (syntax-case x ()
            (("quote" x) #''x)
            (("list" x ...) #`(list #,@(map emit #'(x ...))))
            ;; could emit list* for 3+ arguments if implementation supports
            ;; list*
            (("list*" x ... y)
             (let f ((x* #'(x ...)))
               (if (null? x*)
                   (emit #'y)
                   #`(cons #,(emit (car x*)) #,(f (cdr x*))))))
            (("append" x ...) #`(append #,@(map emit #'(x ...))))
            (("vector" x ...) #`(vector #,@(map emit #'(x ...))))
            (("list->vector" x) #`(list->vector #,(emit #'x)))
            (("value" x) #'x)))
        (lambda (x)
          (syntax-case x ()
            ;; convert to intermediate language, combining introduced (but
            ;; not unquoted source) quote expressions where possible and
            ;; choosing optimal construction code otherwise, then emit
            ;; Scheme code corresponding to the intermediate language forms.
            ((_ e) (emit (quasi #'e 0))))))) 

    (define-syntax include
      (lambda (x)
        (define (read-file fn dir k)
          (call-with-input-file
              (if (absolute-file-name? fn)
                  fn
                  (if dir
                      (in-vicinity dir fn)
                      (syntax-violation
                       'include
                       "relative file name only allowed when the include form is in a file"
                       x)))
            (lambda (p)
              (let ((enc (file-encoding p)))
                ;; Choose the input encoding deterministically.
                (set-port-encoding! p (or enc "UTF-8"))
                (let f ()
                  (let ((x (read p)))
                    (if (eof-object? x)
                        '()
                        (cons (datum->syntax k x) (f)))))))))
        (let* ((src (syntax-source x))
               (file (and src (assq-ref src 'filename)))
               (dir (and (string? file) (dirname file))))
          (syntax-case x ()
            ((k filename)
             (let ((fn (syntax->datum #'filename)))
               (with-syntax (((exp ...) (read-file fn dir #'filename)))
                 #'(begin exp ...))))))))

    (define-syntax include-from-path
      (lambda (x)
        (syntax-case x ()
          ((k filename)
           (let ((fn (syntax->datum #'filename)))
             (with-syntax ((fn (datum->syntax
                                #'filename
                                (or (%search-load-path fn)
                                    (syntax-violation 'include-from-path
                                                      "file not found in path"
                                                      x #'filename)))))
               #'(include fn)))))))

    (define-syntax unquote
      (lambda (x)
        (syntax-violation 'unquote
                          "expression not valid outside of quasiquote"
                          x)))

    (define-syntax unquote-splicing
      (lambda (x)
        (syntax-violation 'unquote-splicing
                          "expression not valid outside of quasiquote"
                          x)))

    (define-syntax identifier-syntax
      (lambda (xx)
        (syntax-case xx (set!)
          ((_ e)
           #'(lambda (x)
               #((macro-type . identifier-syntax))
               (syntax-case x ()
                 (id
                  (identifier? #'id)
                  #'e)
                 ((_ x (... ...))
                  #'(e x (... ...))))))
          ((_ (id exp1) ((set! var val) exp2))
           (and (identifier? #'id) (identifier? #'var))
           #'(make-variable-transformer
              (lambda (x)
                #((macro-type . variable-transformer))
                (syntax-case x (set!)
                  ((set! var val) #'exp2)
                  ((id x (... ...)) #'(exp1 x (... ...)))
                  (id (identifier? #'id) #'exp1))))))))

    (define-syntax define*
      (lambda (x)
        (syntax-case x ()
          ((_ (id . args) b0 b1 ...)
           #'(define id (lambda* args b0 b1 ...)))
          ((_ id val) (identifier? #'id)
           #'(define id val)))))))
