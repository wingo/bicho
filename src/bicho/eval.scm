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
  #:export (eval))

(define (call-primitive name args)
  (apply (module-ref the-scm-module name) args))

(define (eval exp env)
  (match exp
    (($ <void> src)
     *unspecified*)

    (($ <call> src proc args)
     (apply (eval proc env) (map (cut eval <> env) args)))

    (($ <primcall> src name args)
     (call-primitive name (map (cut eval <> env) args)))

    (($ <conditional> src test consequent alternate)
     (if (eval test env)
	 (eval consequent env)
	 (eval alternate env)))

    (($ <primitive-ref> src name)
     (lambda args (call-primitive name args)))

    (($ <lexical-ref> src name gensym)
     (assq-ref env gensym))

    (($ <lexical-set> src name gensym exp)
     (assq-set! env gensym (eval exp env)))

    (($ <toplevel-ref> src name)
     (variable-ref (module-variable (current-module) name)))

    (($ <toplevel-set> src name exp)
     (variable-set! (module-variable (current-module) name) (eval exp env)))

    (($ <toplevel-define> src name exp)
     (module-define! (current-module) name (eval exp env)) )

    (($ <lambda> src meta body)
     (if body
	 (eval body env)
	 (case-lambda)))

    (($ <lambda-case> src req opt rest kw inits gensyms body alternate)
     (define (parse-args env args)
       (parse-req env req gensyms args))
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
    
    (($ <let> src names gensyms vals body)
     (let lp ((env* env) (gensyms gensyms) (vals vals))
       (match (vector gensyms vals)
	 (#(() ()) (eval body env*))
	 (#((var . vars) (val .vals))
	  (lp (acons var (eval val env) env*) vars vals)))))

    (($ <letrec> src in-order? names gensyms vals body)
     (let ((env (fold (lambda (var env) (acons var #f env)) env gensyms)))
       (if in-order?
	   (let lp ((vars gensyms) (vals vals))
	     (match (vector vars vals)
	       (#(() ()) (eval body env))
	       (#((var . vars) (val . vals))
		(assq-set! env var (eval val env))
		(lp vars vals))))
	   (let lp ((vars gensyms) (vals (map (cut eval <> env) vals)))
	     (match (vector vars vals)
	       (#(() ()) (eval body env))
	       (#((var . vars) (val . vals))
		(assq-set! env var val)
		(lp vars vals)))))))

    (($ <fix> src names gensyms vals body)
     (let ((env (fold (lambda (var env) (acons var #f env)) env gensyms)))
       (let lp ((vars gensyms) (vals vals))
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
