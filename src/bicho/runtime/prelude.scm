(include "./quasisyntax.scm")

(define-syntax-rule (when test stmt stmt* ...)
  (if test (begin stmt stmt* ...)))

(define-syntax-rule (unless test stmt stmt* ...)
  (if (not test) (begin stmt stmt* ...)))

(define-syntax cond
  (lambda (whole-expr)
    (define (fold f seed xs)
      (let loop ((xs xs) (seed seed))
        (if (null? xs) seed
            (loop (cdr xs) (f (car xs) seed)))))
    (define (reverse-map f xs)
      (fold (lambda (x seed) (cons (f x) seed))
            '() xs))
    (syntax-case whole-expr ()
      ((_ clause clauses ...)
       #`(begin
           #,@(fold (lambda (clause-builder tail)
                      (clause-builder tail))
                    #'()
                    (reverse-map
                     (lambda (clause)
                       (define* (bad-clause #:optional (msg "invalid clause"))
                         (syntax-violation 'cond msg whole-expr clause))
                       (syntax-case clause (=> else)
                         ((else e e* ...)
                          (lambda (tail)
                            (if (null? tail)
                                #'((begin e e* ...))
                                (bad-clause "else must be the last clause"))))
                         ((else . _) (bad-clause))
                         ((test => receiver)
                          (lambda (tail)
                            #`((let ((t test))
                                 (if t
                                     (receiver t)
                                     #,@tail)))))
                         ((test => receiver ...)
                          (bad-clause "wrong number of receiver expressions"))
                         ((generator guard => receiver)
                          (lambda (tail)
                            #`((call-with-values (lambda () generator)
                                 (lambda vals
                                   (if (apply guard vals)
                                       (apply receiver vals)
                                       #,@tail))))))
                         ((generator guard => receiver ...)
                          (bad-clause "wrong number of receiver expressions"))
                         ((test)
                          (lambda (tail)
                            #`((let ((t test))
                                 (if t t #,@tail)))))
                         ((test e e* ...)
                          (lambda (tail)
                            #`((if test
                                   (begin e e* ...)
                                   #,@tail))))
                         (_ (bad-clause))))
                     #'(clause clauses ...))))))))

(define-syntax case
  (lambda (whole-expr)
    (define (fold f seed xs)
      (let loop ((xs xs) (seed seed))
        (if (null? xs) seed
            (loop (cdr xs) (f (car xs) seed)))))
    (define (fold2 f a b xs)
      (let loop ((xs xs) (a a) (b b))
        (if (null? xs) (values a b)
            (call-with-values
                (lambda () (f (car xs) a b))
              (lambda (a b)
                (loop (cdr xs) a b))))))
    (define (reverse-map-with-seed f seed xs)
      (fold2 (lambda (x ys seed)
               (call-with-values
                   (lambda () (f x seed))
                 (lambda (y seed)
                   (values (cons y ys) seed))))
             '() seed xs))
    (syntax-case whole-expr ()
      ((_ expr clause clauses ...)
       (with-syntax ((key #'key))
         #`(let ((key expr))
             #,@(fold
                 (lambda (clause-builder tail)
                   (clause-builder tail))
                 #'()
                 (reverse-map-with-seed
                  (lambda (clause seen)
                    (define* (bad-clause #:optional (msg "invalid clause"))
                      (syntax-violation 'case msg whole-expr clause))
                    (syntax-case clause ()
                      ((test . rest)
                       (with-syntax
                           ((clause-expr
                             (syntax-case #'rest (=>)
                               ((=> receiver) #'(receiver key))
                               ((=> receiver ...)
                                (bad-clause
                                 "wrong number of receiver expressions"))
                               ((e e* ...) #'(begin e e* ...))
                               (_ (bad-clause)))))
                         (syntax-case #'test (else)
                           ((datums ...)
                            (let ((seen
                                   (fold
                                    (lambda (datum seen)
                                      (define (warn-datum type)
                                        ((@ (system base message)
                                            warning)
                                         type
                                         (append (source-properties datum)
                                                 (source-properties
                                                  (syntax->datum #'test)))
                                         datum
                                         (syntax->datum clause)
                                         (syntax->datum whole-expr)))
                                      (when (memv datum seen)
                                        (warn-datum 'duplicate-case-datum))
                                      (when (or (pair? datum) (array? datum))
                                        (warn-datum 'bad-case-datum))
                                      (cons datum seen))
                                    seen
                                    (map syntax->datum #'(datums ...)))))
                              (values (lambda (tail)
                                        #`((if (memv key '(datums ...))
                                               clause-expr
                                               #,@tail)))
                                      seen)))
                           (else (values (lambda (tail)
                                           (if (null? tail)
                                               #'(clause-expr)
                                               (bad-clause
                                                "else must be the last clause")))
                                         seen))
                           (_ (bad-clause)))))
                      (_ (bad-clause))))
                  '() #'(clause clauses ...)))))))))

(define-syntax do
  (syntax-rules ()
    ((do ((var init step ...) ...)
         (test expr ...)
         command ...)
     (letrec
       ((loop
         (lambda (var ...)
           (if test
               (begin
                 (if #f #f)
                 expr ...)
               (begin
                 command
                 ...
                 (loop (do "step" var step ...)
                       ...))))))
       (loop init ...)))
    ((do "step" x)
     x)
    ((do "step" x y)
     y)))

(define-syntax define-values
  (lambda (orig-form)
    (syntax-case orig-form ()
      ((_ () expr)
       ;; XXX Work around the lack of hygienic top-level identifiers
       (with-syntax (((dummy) (generate-temporaries '(dummy))))
         #`(define dummy
             (call-with-values (lambda () expr)
               (lambda () #f)))))
      ((_ (var) expr)
       (identifier? #'var)
       #`(define var
           (call-with-values (lambda () expr)
             (lambda (v) v))))
      ((_ (var0 ... varn) expr)
       (and-map identifier? #'(var0 ... varn))
       ;; XXX Work around the lack of hygienic toplevel identifiers
       (with-syntax (((dummy) (generate-temporaries '(dummy))))
         #`(begin
             ;; Avoid mutating the user-visible variables
             (define dummy
               (call-with-values (lambda () expr)
                 (lambda (var0 ... varn)
                   (list var0 ... varn))))
             (define var0
               (let ((v (car dummy)))
                 (set! dummy (cdr dummy))
                 v))
             ...
             (define varn
               (let ((v (car dummy)))
                 (set! dummy #f)  ; blackhole dummy
                 v)))))
      ((_ var expr)
       (identifier? #'var)
       #'(define var
           (call-with-values (lambda () expr)
             list)))
      ((_ (var0 ... . varn) expr)
       (and-map identifier? #'(var0 ... varn))
       ;; XXX Work around the lack of hygienic toplevel identifiers
       (with-syntax (((dummy) (generate-temporaries '(dummy))))
         #`(begin
             ;; Avoid mutating the user-visible variables
             (define dummy
               (call-with-values (lambda () expr)
                 (lambda (var0 ... . varn)
                   (list var0 ... varn))))
             (define var0
               (let ((v (car dummy)))
                 (set! dummy (cdr dummy))
                 v))
             ...
             (define varn
               (let ((v (car dummy)))
                 (set! dummy #f)  ; blackhole dummy
                 v))))))))

(define-syntax-rule (delay exp)
  (make-promise (lambda () exp)))

(define-syntax with-fluids
  (lambda (stx)
    (define (emit-with-fluids bindings body)
      (syntax-case bindings ()
        (()
         body)
        (((f v) . bindings)
         #`(with-fluid* f v
             (lambda ()
               #,(emit-with-fluids #'bindings body))))))
    (syntax-case stx ()
      ((_ ((fluid val) ...) exp exp* ...)
       (with-syntax (((fluid-tmp ...) (generate-temporaries #'(fluid ...)))
                     ((val-tmp ...) (generate-temporaries #'(val ...))))
         #`(let ((fluid-tmp fluid) ...)
             (let ((val-tmp val) ...)
               #,(emit-with-fluids #'((fluid-tmp val-tmp) ...)
                                   #'(begin exp exp* ...)))))))))

(define-syntax current-source-location
  (lambda (x)
    (syntax-case x ()
      ((_)
       (with-syntax ((s (datum->syntax x (syntax-source x))))
         #''s)))))

;; We provide this accessor out of convenience.  current-line and
;; current-column aren't so interesting, because they distort what they
;; are measuring; better to use syntax-source from a macro.
;;
(define-syntax current-filename
  (lambda (x)
    "A macro that expands to the current filename: the filename that
the (current-filename) form appears in.  Expands to #f if this
information is unavailable."
    (false-if-exception
     (canonicalize-path (assq-ref (syntax-source x) 'filename)))))

(define-syntax-rule (define-once sym val)
  (define sym
    (if (module-locally-bound? (current-module) 'sym) sym val)))
