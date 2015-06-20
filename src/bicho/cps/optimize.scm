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
;;; Optimizations on CPS.
;;;
;;; Code:

(define-module (bicho cps optimize)
  #:use-module (ice-9 match)
  #:use-module (bicho cps constructors)
  #:use-module (bicho cps contification)
  #:use-module (bicho cps cse)
  #:use-module (bicho cps dce)
  #:use-module (bicho cps elide-values)
  #:use-module (bicho cps prune-top-level-scopes)
  #:use-module (bicho cps prune-bailouts)
  #:use-module (bicho cps self-references)
  #:use-module (bicho cps simplify)
  #:use-module (bicho cps specialize-primcalls)
  #:use-module (bicho cps split-rec)
  #:use-module (bicho cps type-fold)
  #:use-module (bicho cps verify)
  #:export (optimize))

(define (kw-arg-ref args kw default)
  (match (memq kw args)
    ((_ val . _) val)
    (_ default)))

(define *debug?* #f)

(define (maybe-verify program)
  (if *debug?*
      (verify program)
      program))

(define* (optimize program #:optional (opts '()))
  (define (run-pass! pass kw default)
    (set! program
          (if (kw-arg-ref opts kw default)
              (maybe-verify (pass program))
              program)))

  (maybe-verify program)

  ;; This series of assignments to `program' used to be a series of let*
  ;; bindings of `program', as you would imagine.  In compiled code this
  ;; is fine because the compiler is able to allocate all let*-bound
  ;; variable to the same slot, which also means that the garbage
  ;; collector doesn't have to retain so many copies of the term being
  ;; optimized.  However during bootstrap, the interpreter doesn't do
  ;; this optimization, leading to excessive data retention as the terms
  ;; are rewritten.  To marginally improve bootstrap memory usage, here
  ;; we use set! instead.  The compiler should produce the same code in
  ;; any case, though currently it does not because it doesn't do escape
  ;; analysis on the box created for the set!.

  (run-pass! split-rec #:split-rec? #t)
  (run-pass! eliminate-dead-code #:eliminate-dead-code? #t)
  (run-pass! prune-top-level-scopes #:prune-top-level-scopes? #t)
  (run-pass! simplify #:simplify? #t)
  (run-pass! contify #:contify? #t)
  (run-pass! inline-constructors #:inline-constructors? #t)
  (run-pass! specialize-primcalls #:specialize-primcalls? #t)
  (run-pass! elide-values #:elide-values? #t)
  (run-pass! prune-bailouts #:prune-bailouts? #t)
  (run-pass! eliminate-common-subexpressions #:cse? #t)
  (run-pass! type-fold #:type-fold? #t)
  (run-pass! resolve-self-references #:resolve-self-references? #t)
  (run-pass! eliminate-dead-code #:eliminate-dead-code? #t)
  (run-pass! simplify #:simplify? #t)

  (verify program))
