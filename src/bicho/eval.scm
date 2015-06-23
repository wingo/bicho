;;;; 	Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014 Free Software Foundation, Inc.
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


(define-module (bicho eval)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-26)
  #:use-module (ice-9 match)
  #:use-module (bicho tree-il)
  #:export (add-compile-time-value!)
  #:replace (eval))

(define *compile-time-values* (make-hash-table))

(define (add-compile-time-value! name value)
  (when (hashq-ref *compile-time-values* name)
    (error "name already exists in compile-time environment" name))
  (hashq-set! *compile-time-values* name value))

(define-syntax-rule (import! name ...)
  (begin (add-compile-time-value! 'name name) ...))

(import! * + - / 1+ 1- < <= = > >=)

(import! abs max min sqrt exact-integer-sqrt exp expt log log10)

(import! acos acosh asin asinh atan atanh cos cosh sin sinh tan tanh)

(import! complex? make-rectangular real-part imag-part
         make-polar angle magnitude)

(import! ash bit-extract logand logbit? logcount logior lognot logtest
         logxor round-ash)

(import! ceiling floor round)

(import! quotient remainder modulo
         ceiling-quotient ceiling-remainder ceiling/
         centered-quotient centered-remainder centered/
         euclidean-quotient euclidean-remainder euclidean/
         floor-quotient floor-remainder floor/
         round-quotient round-remainder round/
         truncate-quotient truncate-remainder truncate/)

(import! rational? denominator numerator rationalize)

(import! integer? exact-integer? even? odd?
         gcd lcm integer-expt integer-length modulo-expt)

(import! number? exact->inexact exact? inexact->exact inexact?)

(import! finite? inf inf? nan nan?)

(import! negative? positive? real? zero?)

(import! car cdr set-car! set-cdr!)

(import! caaaar caaadr caaar caadar caaddr caadr caar
         cadaar cadadr cadar caddar cadddr caddr cadr
         cdaaar cdaadr cdaar cdadar cdaddr cdadr cdar
         cddaar cddadr cddar cdddar cddddr cdddr cddr)

(import! cons cons* acons null? pair?)

(import! append length list list-cdr-ref list-cdr-set! list-copy
         list-head list-index list-ref list-set! list-tail list?
         last-pair make-list sort stable-sort merge reverse)

(import! assoc assoc-ref assoc-remove! assoc-set!
         assq assq-ref assq-remove! assq-set!
         assv assv-ref assv-remove! assv-set!
         member memq memv)

(import! and-map and=> apply compose const filter for-each
         identity iota map negate or-map procedure?)

(import! absolute-file-name? basename canonicalize-path dirname
         in-vicinity file-name-separator-string file-name-separator?
         file-exists? file-is-directory?)

(import! current-input-port current-output-port
         current-error-port current-warning-port

         call-with-input-file call-with-input-string
         call-with-output-file call-with-output-string

         with-input-from-file with-input-from-port with-input-from-string
         with-output-to-file with-output-to-port with-output-to-string
         with-error-to-file with-error-to-port with-error-to-string)

(import! port? input-port? output-port?
         file-encoding file-port? file-position file-set-position
         port-filename port-line port-column
         port-conversion-strategy port-encoding port-mode
         set-port-filename! set-port-line! set-port-column!
         set-port-conversion-strategy! set-port-encoding!)

(import! eof-object? display newline peek peek-char pk write
         format simple-format warn
         read read-char unread-char unread-string write-char)

(import! boolean? not)

(import! call-with-values values)

(import! catch throw error print-exception)

(import! char? integer->char char->integer

         char<=? char<? char=? char>=? char>?
         char-ci<=? char-ci<? char-ci=? char-ci>=? char-ci>?
         
         char-alphabetic? char-is-both? char-lower-case?
         char-numeric? char-upper-case? char-whitespace?

         char-downcase char-general-category char-titlecase char-upcase)

(import! char-set char-set? ucs-range->char-set
         char-set->list list->char-set char-set->string string->char-set
         char-set<= char-set= 

         char-set-adjoin char-set-delete
         char-set-complement char-set-diff+intersection
         char-set-difference char-set-intersection
         char-set-union char-set-xor
         
         char-set-every char-set-any char-set-contains? char-set-count

         char-set-ref char-set-size

         char-set-cursor char-set-cursor-next end-of-char-set?

         char-set-filter char-set-fold char-set-for-each
         char-set-hash char-set-map char-set-unfold

         char-set:ascii char-set:blank char-set:designated
         char-set:digit char-set:empty char-set:full char-set:graphic
         char-set:hex-digit char-set:iso-control char-set:letter
         char-set:letter+digit char-set:lower-case char-set:printing
         char-set:punctuation char-set:symbol char-set:title-case
         char-set:upper-case char-set:whitespace)

(import! current-time)

(import! eq? equal? eqv?)
(import! hash hashq hashv)

(import! gensym list->symbol make-symbol string->symbol symbol
         symbol->string symbol-append symbol?)

(import! make-hash-table hash-table? hash-count
         hash-clear! hash-fold hash-for-each
         hash-for-each-handle hash-map->list

         hash-create-handle! hash-get-handle
         hash-ref hash-remove! hash-set!

         hashq-create-handle! hashq-get-handle
         hashq-ref hashq-remove! hashq-set!

         hashv-create-handle! hashv-get-handle
         hashv-ref hashv-remove! hashv-set!)

(import! string make-string string-length string? substring
         list->string string->list number->string string->number

         string-ref string-bytes-per-char

         string-compare string-compare-ci

         string< string<= string<=? string<> string<? string= string=?
         string> string>= string>=? string>?

         string-ci< string-ci<= string-ci<=? string-ci<> string-ci<?
         string-ci= string-ci=? string-ci> string-ci>= string-ci>=?
         string-ci>?

         string-any string-every string-contains string-contains-ci
         string-null? string-prefix-ci? string-prefix?
         string-suffix-ci? string-suffix?
         
         string-index string-index-right string-rindex
         
         string-count

         string-fold string-fold-right string-for-each string-for-each-index
         
         string-join string-split

         string-normalize-nfc string-normalize-nfd
         string-normalize-nfkc string-normalize-nfkd

         string-delete string-filter string-append
         string-capitalize string-concatenate string-concatenate-reverse
         string-downcase string-drop string-drop-right
         string-hash string-hash-ci string-map string-pad string-pad-right
         string-prefix-length string-prefix-length-ci string-replace
         string-reverse string-skip string-skip-right string-suffix-length
         string-suffix-length-ci string-tabulate string-take
         string-take-right string-titlecase string-tokenize string-trim
         string-trim-both string-trim-right string-unfold
         string-unfold-right string-upcase)

(import! make-vector vector vector? list->vector vector->list
         vector-copy vector-fill! vector-length vector-move-left!
         vector-move-right! vector-ref vector-set!)

(import! make-variable variable-ref variable-set! variable?)

(define (compile-time-ref name)
  (match (hashq-ref *compile-time-values* name)
    (#f (error "unbound toplevel" name))
    (val val)))

(define* (eval exp #:optional (env '()))
  (match exp
    (($ <void> src)
     *unspecified*)

    (($ <call> src proc args)
     (apply (eval proc env) (map (cut eval <> env) args)))

    (($ <primcall> src name args)
     (apply (compile-time-ref name) (map (cut eval <> env) args)))

    (($ <conditional> src test consequent alternate)
     (if (eval test env)
	 (eval consequent env)
	 (eval alternate env)))

    (($ <primitive-ref> src name)
     (compile-time-ref name))

    (($ <lexical-ref> src name var)
     (assq-ref env var))

    (($ <lexical-set> src name var exp)
     (assq-set! env var (eval exp env)))

    (($ <toplevel-ref> src name)
     (compile-time-ref name))

    (($ <lambda> src meta body)
     (if body
	 (eval body env)
	 (case-lambda)))

    (($ <lambda-case> src req opt rest kw inits vars body alternate)
     (define (parse-args env args)
       (parse-req env req vars args))
     (define (parse-req env req vars args)
       (match (vector req vars args)
	 (#((_ . req) (var . vars) (arg . args))
	  (parse-req (acons var arg env) req vars args))
	 (#(() vars args)
	  (check-positional env vars args))
	 (_ #f)))
     (define (check-positional env vars args)
       (let ((opt (or opt '())))
	 (define (nopt args)
	   (let lp ((n 0) (args args))
	     (if (or (null? args) (and kw (keyword? (car args))))
		 n
		 (lp (1+ n) (cdr args)))))
	 (and (or rest (<= (nopt args) (length opt)))
	      (parse-opt env opt vars inits args))))
     (define (parse-opt env opt vars inits args)
       (match (vector opt inits vars args)
	 (#((_ . opt) (var . vars) (init . inits) (arg . args))
	  (parse-opt (acons var arg env) opt vars inits args))
	 (#((_ . opt) (var . vars) (init . inits) ())
	  (parse-opt (acons var (eval init env) env) opt vars inits '()))
	 (#(() vars inits args)
	  (parse-rest env vars inits args))))
     (define (parse-rest env vars inits args)
       (if rest
	   (match vars
	     ((var . vars)
	      (parse-kw (acons var rest env) vars inits args)))
	   (parse-kw env vars inits args)))
     (define (parse-kw env vars inits args)
       (when kw (error "whattt"))
       env)
     (lambda args
       (cond
	((parse-args env args)
	 => (lambda (env) (eval body env)))
	(else
	 (if alternate
	     (apply (eval alternate env) args)
	     (error "function failed to apply" req opt rest kw args))))))

    (($ <const> src exp)
     exp)

    (($ <seq> src head tail)
     (eval head env)
     (eval tail env))
    
    (($ <let> src names vars vals body)
     (let lp ((env* env) (vars vars) (vals vals))
       (match (vector vars vals)
	 (#(() ()) (eval body env*))
	 (#((var . vars) (val . vals))
	  (lp (acons var (eval val env) env*) vars vals)))))

    (($ <letrec> src in-order? names vars vals body)
     (let ((env (fold (lambda (var env) (acons var #f env)) env vars)))
       (if in-order?
	   (let lp ((vars vars) (vals vals))
	     (match (vector vars vals)
	       (#(() ()) (eval body env))
	       (#((var . vars) (val . vals))
		(assq-set! env var (eval val env))
		(lp vars vals))))
	   (let lp ((vars vars) (vals (map (cut eval <> env) vals)))
	     (match (vector vars vals)
	       (#(() ()) (eval body env))
	       (#((var . vars) (val . vals))
		(assq-set! env var val)
		(lp vars vals)))))))

    (($ <fix> src names vars vals body)
     (let ((env (fold (lambda (var env) (acons var #f env)) env vars)))
       (let lp ((vars vars) (vals vals))
	 (match (vector vars vals)
	   (#(() ()) (eval body env))
	   (#((var . vars) (val . vals))
	    (assq-set! env var (eval val env))
	    (lp vars vals))))))

    (($ <let-values> src exp body)
     (call-with-values (lambda () (eval exp body))
       (eval body env)))

    (($ <prompt> src escape-only? tag body handler)
     (call-with-prompt (eval tag env) (eval body env) (eval handler env)))

    (($ <abort> src tag args tail)
     (apply abort-to-prompt (eval tag env)
	    (append (map (cut eval <> env) args) (eval tail env))))))
