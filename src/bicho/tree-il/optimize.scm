;;; Tree-il optimizer

;; Copyright (C) 2009, 2011, 2012, 2013, 2014 Free Software Foundation, Inc.

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

;;; Code:

(define-module (bicho tree-il optimize)
  #:use-module (bicho tree-il)
  #:use-module (bicho tree-il primitives)
  #:use-module (bicho tree-il peval)
  #:use-module (bicho tree-il fix-letrec)
  #:use-module (bicho tree-il debug)
  #:use-module (ice-9 match)
  #:export (optimize))

(define (optimize x env opts)
  (let ((peval (match (memq #:partial-eval? opts)
                 ((#:partial-eval? #f _ ...)
                  ;; Disable partial evaluation.
                  (lambda (x e) x))
                 (_ peval))))
    (fix-letrec
     (verify-tree-il
      (peval (expand-primitives (resolve-primitives x env))
             env)))))
