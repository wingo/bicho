;; Lambkin, a garbage-collected heap suitable for microcontrollers.
;; Copyright (C) 2015 Andy Wingo <wingo@igalia.com>.
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;; Q: What do ewe call a smallish heap?
;;
;; A: A lamb.
;; *sunglasses*
;; *skates off into sunset*
;;

(define-module (lambkin)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-9 gnu)
  #:use-module (ice-9 match)
  )

;; First, we define a byte-addressable persistent sparse functional
;; heap that we will use to model SRAM state.  The advantage of being
;; sparse is that we can prevent undefined memory access.  Being
;; persistent lets us cheaply snapshot state.  Being functional is
;; kindof a wash -- it's neat but you have to thread around a lot of
;; state in the emulator.  Anyway, an experiment.

(define-syntax-rule (define-inline name val)
  (define-syntax name (identifier-syntax val)))

(define-inline *branch-bits* 4)
(define-inline *branch-size* (ash 1 *branch-bits*))
(define-inline *branch-mask* (1- *branch-size*))

(define-record-type <heap>
  (make-heap min shift root)
  heap?
  (min heap-min)
  (shift heap-shift)
  (root heap-root))

(define *absent* (list 'absent))
(define-inlinable (absent? x)
  (eq? x *absent*))
(define-inlinable (present? x)
  (not (absent? x)))

(define empty-heap (make-heap 0 0 *absent*))

(define (heap-set heap addr byte)
  (define (new-branch)
    (make-vector *branch-size* *absent*))
  (define (clone-branch-and-set branch i elt)
    (let ((new (vector-copy branch)))
      (vector-set! new i elt)
      new))
  (define (round-down min shift)
    (logand min (lognot (1- (ash 1 shift)))))
  (define (set addr shift root)
    (if (zero? shift)
        byte
        (let* ((shift (- shift *branch-bits*))
               (idx (logand (ash addr (- shift)) *branch-mask*)))
          (if (absent? root)
              (let ((root* (new-branch))
                    (node* (set addr shift root)))
                (vector-set! root* idx node*)
                root*)
              (let* ((node (vector-ref root idx))
                     (node* (set addr shift node)))
                (if (eqv? node node*)
                    root
                    (clone-branch-and-set root idx node*)))))))
  (match heap
    (($ <heap> min shift root)
     (cond
      ((< addr 0) (error "Invalid address" addr))
      ((absent? root)
       ;; Add first element.
       (make-heap addr 0 byte))
      (else
       (let lp ((min min) (shift shift) (root* root))
         (if (and (<= min addr) (< addr (+ min (ash 1 shift))))
             (let ((root* (set (- addr min) shift root*)))
               (if (eq? root* root)
                   heap
                   (make-heap min shift root*)))
             (let* ((shift* (+ shift *branch-bits*))
                    (min* (round-down min shift*))
                    (idx (logand (ash (- min min*) (- shift)) *branch-mask*))
                    (root** (new-branch)))
               (vector-set! root** idx root*)
               (lp min* shift* root**)))))))))

(define* (heap-ref heap addr #:optional
                   (not-found (lambda (addr) (error "not found" addr))))
  (define (absent) (not-found addr))
  (define (ref min shift root)
    (if (zero? shift)
        (if (and min (= addr min) (present? root))
            root
            (absent))
        (if (and (<= min addr) (< addr (+ min (ash 1 shift))))
            (let ((addr* (- addr min)))
              (let lp ((node root) (shift shift))
                (if (present? node)
                    (if (= shift *branch-bits*)
                        (let ((node (vector-ref node
                                                (logand addr* *branch-mask*))))
                          (if (present? node)
                              node
                              (absent)))
                        (let* ((shift (- shift *branch-bits*))
                               (idx (logand (ash addr* (- shift))
                                            *branch-mask*)))
                          (lp (vector-ref node idx) shift)))
                    (absent))))
            (absent))))
  (match heap
    (($ <heap> min shift root)
     (ref min shift root))))

(define (heap-addr-ranges heap)
  (define-syntax-rule (make-heap-folder seed ...)
    (lambda (f heap seed ...)
      (define (visit-branch node shift min seed ...)
        (let ((shift (- shift *branch-bits*)))
          (if (zero? shift)
              (let lp ((i 0) (seed seed) ...)
                (if (< i *branch-size*)
                    (let ((elt (vector-ref node i)))
                      (call-with-values (lambda ()
                                          (if (present? elt)
                                              (f (+ i min) elt seed ...)
                                              (values seed ...)))
                        (lambda (seed ...)
                          (lp (1+ i) seed ...))))
                    (values seed ...)))
              (let lp ((i 0) (seed seed) ...)
                (if (< i *branch-size*)
                    (let ((elt (vector-ref node i)))
                      (call-with-values
                          (lambda ()
                            (if (present? elt)
                                (visit-branch elt shift (+ min (ash i shift))
                                              seed ...)
                                (values seed ...)))
                        (lambda (seed ...)
                          (lp (1+ i) seed ...))))
                    (values seed ...))))))
      (let fold ((heap heap))
        (match heap
          (($ <heap> min shift root)
           (cond
            ((absent? root) (values seed ...))
            ((zero? shift) (f min root seed ...))
            (else (visit-branch root shift min seed ...))))))))
  (define (heap-fold f heap seed0 seed1 seed2)
    ((make-heap-folder seed0 seed1 seed2) f heap seed0 seed1 seed2))
  (call-with-values
      (lambda ()
        (heap-fold (lambda (k v start end closed)
                     (cond
                      ((not start) (values k k closed))
                      ((= k (1+ end)) (values start k closed))
                      (else (values k k (acons start end closed)))))
                   heap #f #f '()))
    (lambda (start end closed)
      (reverse (if start (acons start end closed) closed)))))

(define (print-heap heap port)
  (define (range-string ranges)
    (string-join (map (match-lambda
                        ((start . start)
                         (format #f "#x~x" start))
                        ((start . end)
                         (format #f "#x~x-#x~x" start (1+ end))))
                      ranges)
                 ","))
  (if (eq? heap empty-heap)
      (format port "#<heap>")
      (format port "#<heap ~a>" (range-string (heap-addr-ranges heap)))))

(set-record-type-printer! <heap> print-heap)


;; Some convenience methods.

(define heap-ref-u8 heap-ref)
(define heap-set-u8 heap-set)
(define* (heap-ref-s8 heap addr #:optional
                      (unset (lambda (addr) (error "unset" addr))))
  (let ((u8 (heap-ref-u8 heap addr unset)))
    (if (>= u8 128) (- u8 256) u8)))
(define (heap-set-s8 heap addr s8)
  (unless (<= -128 s8 127) (error "bad s8" s8))
  (heap-set-u8 heap addr (if (< s8 0) (+ s8 256) s8)))

(define* (heap-ref-u16 heap addr #:optional
                       (unset (lambda (addr) (error "unset" addr))))
  (+ (heap-ref-u8 heap addr unset)
     (ash (heap-ref-u8 heap (1+ addr) unset) 8)))
(define (heap-set-u16 heap addr u16)
  (unless (<= 0 u16 (1- (ash 1 16))) (error "bad u16" u16))
  (let ((heap (heap-set-u8 heap (1+ addr) (ash u16 -8))))
    (heap-set-u8 heap addr (logand u16 #xff))))
(define* (heap-ref-s16 heap addr #:optional
                       (unset (lambda (addr) (error "unset" addr))))
  (let ((u16 (heap-ref-u16 heap addr unset)))
    (if (>= u16 (ash 1 15)) (- u16 (ash 1 16)) u16)))
(define (heap-set-s16 heap addr s16)
  (heap-set-u16 heap addr (if (< s16 0) (+ s16 (ash 1 16)) s16)))

;; Now we define bits about the arduino's configuration.

(define-inline *prog-bits* 15) ;; 32KB
(define-inline *data-bits* 11) ;; 2KB

(define-inline *prog-size* (ash 1 *prog-bits*))
(define-inline *data-size* (ash 1 *data-bits*))

;; atmega328P-PU chip:
;;  #x0-#x20: registers
;;  #x20-#x60: i/o registers
(define-inline *data-start* #x60)

;; The garbage collector is a mark/compact collector.  The stack grows
;; down and the heap grows up.  Whenever there is no room to grow the
;; stack or heap, GC happens, taking the stack as the root set.  When
;; GC happens there is no stack space available, so we have to reserve
;; a space for a worklist after the mark bits.  Mark bits are stored
;; outside objects, to make relocation easy.  Relocation uses the
;; compaction trick described in
;; http://factor-language.blogspot.fr/2009/11/mark-compact-garbage-collection-for.html.
;; Since the visit worklist is only used during marking and the
;; forwarding table is only used during relocation, they share space.

;; #x60-#xe0 mark bits
(define-inline *mark-table* *data-start*)
(define-inline *mark-table-size* (ash *data-size* -4))
;; #xe0-#x160 visit bits; a worklist for marking.
(define-inline *visit-table* (+ *mark-table* *mark-table-size*))
(define-inline *visit-table-size* *mark-table-size*)
;; #xe0-#x100 forwarding table, sharing space with visit table
(define-inline *forward-table* (+ *mark-table* *mark-table-size*))
(define-inline *forward-table-mark-bits-per-entry* 16)
(define-inline *forward-table-mark-bytes-per-entry*
  (ash *forward-table-mark-bits-per-entry* -3))
(define-inline *forward-table-size*
  (* (/ *mark-table-size* *forward-table-mark-bytes-per-entry*) 2))

(define-inlinable (max a b)
  (if (< a b) b a))

(define-inline *hp-start*
  (max (+ *forward-table* *forward-table-size*)
       (+ *visit-table* *visit-table-size*)))
(define-inline *sp-start*
  *data-size*)

;; Object representation.  This heap differentiates between references
;; to data in ROM ("prog objects") and RAM ("data objects").  There
;; are immediate signed 13-bit fixnums, immediate chars and other
;; miscellanea, and vectors, strings, closures, and pairs have a
;; uniform representation where the first word of the heap object is
;; tagged with the type and size of the payload and payload refs
;; follow.

(define-inline *tc1-mask* (ash 1 15))
(define-inline *tc2-mask* (logior *tc1-mask* (ash 1 14)))
(define-inline *tc3-mask* (logior *tc2-mask* (ash 1 13)))
(define-inline *tc8-mask* #xff00)

(define-inline *data-ref-tc1* (ash 1 15))
(define-inline *prog-ref-tc2* 0)
(define-inline *immediate-tc2* (ash 1 14))
(define-inline *fixnum-tc3* (logior *immediate-tc2* (ash 1 13)))
(define-inline *fixnum-sign-bit* 12)
(define-inline *fixnum-min* (- 0 (ash 1 *fixnum-sign-bit*)))
(define-inline *fixnum-max* (- (ash 1 *fixnum-sign-bit*) 1))
(define-inline *tc8-tc3* *immediate-tc2*)

(define-inlinable (make-tc8 code) (logior (ash code 11) *tc8-tc3*))

(define-inline *char-tc8* (make-tc8 0))
(define-inline *symbol-tc8* (make-tc8 1))
(define-inline *true-tc8* (make-tc8 2))
(define-inline *false-tc8* (make-tc8 3))
(define-inline *eol-tc8* (make-tc8 4))

(define-inlinable (has-tc1? u16 tag)
  (= (logand u16 *tc1-mask*) tag))
(define-inlinable (has-tc2? u16 tag)
  (= (logand u16 *tc2-mask*) tag))
(define-inlinable (has-tc3? u16 tag)
  (= (logand u16 *tc3-mask*) tag))
(define-inlinable (has-tc8? u16 tag)
  (= (logand u16 *tc8-mask*) tag))

(define (data-ref-tagged? u16)
  (has-tc1? u16 *data-ref-tc1*))
(define (data-ref-addr u16)
  (unless (data-ref-tagged? u16) (error "badness" u16))
  (ash (- u16 *data-ref-tc1*) 1))
(define (make-data-ref addr)
  (+ (ash addr -1) *data-ref-tc1*))

(define (prog-ref-tagged? u16)
  (has-tc2? u16 *prog-ref-tc2*))
(define (prog-ref-addr u16)
  (unless (prog-ref-tagged? u16) (error "badness" u16))
  (ash (- u16 *prog-ref-tc2*) 1))
(define (immediate-tagged? u16)
  (has-tc2? u16 *immediate-tc2*))

(define (fixnum-tagged? u16)
  (has-tc3? u16 *fixnum-tc3*))
(define (fixnum-value u16)
  (unless (fixnum-tagged? u16) (error "badness" u16))
  (let ((u12 (logand u16 (1- (ash 1 12)))))
    (if (logbit? 12 u16)
        (- u12 (ash 1 12))
        u12)))

(define (char-tagged? u16)
  (has-tc8? u16 *char-tc8*))
(define (char-value u16)
  (unless (char-tagged? u16) (error "badness" u16))
  (integer->char (logand u16 #xff)))

(define (symbol-tagged? u16)
  (has-tc8? u16 *symbol-tc8*))
(define (symbol-value u16)
  (unless (symbol-tagged? u16) (error "badness" u16))
  (string->symbol
   (string-append "symbol" (number->string (logand u16 #xff)))))

(define (true-tagged? u16)
  (has-tc8? u16 *true-tc8*))
(define (true-value u16)
  (unless (true-tagged? u16) (error "badness" u16))
  #t)

(define (false-tagged? u16)
  (has-tc8? u16 *false-tc8*))
(define (false-value u16)
  (unless (false-tagged? u16) (error "badness" u16))
  #f)

(define (eol-tagged? u16)
  (has-tc8? u16 *eol-tc8*))
(define (eol-value u16)
  (unless (eol-tagged? u16) (error "badness" u16))
  '())

(define (immediate-value u16)
  (unless (immediate-tagged? u16) (error "badness" u16))
  (cond
   ((fixnum-tagged? u16) (fixnum-value u16))
   ((char-tagged? u16) (char-value u16))
   ((symbol-tagged? u16) (symbol-value u16))
   ((true-tagged? u16) (true-value u16))
   ((false-tagged? u16) (false-value u16))
   ((eol-tagged? u16) (eol-value u16))
   (else (error "badness" u16))))

;; Heap objects, whether ram or rom, have a tag+length field in their
;; first word.
(define-inline *heap-tag-mask*  #xf000)
(define-inline *heap-size-mask* #x0fff)

(define-inlinable (make-heap-tag code) (ash code 12))

(define-inline *pair-heap-tag* (make-heap-tag 0))
(define-inline *vector-heap-tag* (make-heap-tag 1))
(define-inline *string-heap-tag* (make-heap-tag 2))
(define-inline *closure-heap-tag* (make-heap-tag 3))
(define-inline *box-heap-tag* (make-heap-tag 4))

(define-inlinable (has-heap-tag? header tag)
  (= (logand header *heap-tag-mask*) tag))
(define-inlinable (heap-tag-code header)
  (ash header -12))
(define-inlinable (heap-object-payload-size header)
  (logand header *heap-size-mask*))

(define-record-type <prog-object>
  (make-prog-object addr kind members)
  prog-object?
  (addr prog-object-addr)
  (kind prog-object-kind)
  (members prog-object-members))

(define-record-type <data-object>
  (make-data-object addr kind members)
  data-object?
  (addr data-object-addr)
  (kind data-object-kind)
  (members data-object-members))

(define* (prog-object-ref heap addr #:optional (prog empty-heap))
  (cond
   ((heap-ref prog addr (lambda (_) #f))
    => (lambda (obj) (values obj prog)))
   (else
    (let* ((header (heap-ref-u16 heap addr))
           (len (heap-object-payload-size header))
           (members (make-vector len #f))
           (obj (make-prog-object addr (heap-tag-code header) members))
           (prog (heap-set prog addr obj)))
      (let lp ((i 0) (prog prog))
        (if (< i len)
            (let* ((addr (+ addr (ash (1+ i) 1)))
                   (u16 (heap-ref-u16 heap addr)))
              (cond
               ((prog-ref-tagged? u16)
                (call-with-values (lambda ()
                                    (prog-object-ref heap addr prog))
                  (lambda (obj prog)
                    (vector-set! members i obj)
                    (lp (1+ i) prog))))
               (else
                (vector-set! members i (immediate-value u16))
                (lp (1+ i) prog))))
            (values obj prog)))))))

(define* (data-object-ref data-heap prog-heap addr #:optional
                          (data-objs empty-heap) (prog-objs empty-heap))
  (cond
   ((heap-ref data-objs addr (lambda (_) #f))
    => (lambda (obj) (values obj data-objs prog-objs)))
   (else
    (let* ((header (heap-ref-u16 data-heap addr))
           (len (heap-object-payload-size header))
           (members (make-vector len #f))
           (obj (make-data-object addr (heap-tag-code header) members))
           (data-objs (heap-set data-objs addr obj)))
      (let lp ((i 0) (data-objs data-objs) (prog-objs prog-objs))
        (if (< i len)
            (let* ((addr (+ addr (ash (1+ i) 1)))
                   (u16 (heap-ref-u16 data-heap addr)))
              (cond
               ((data-ref-tagged? u16)
                (call-with-values
                    (lambda ()
                      (data-object-ref data-heap prog-heap addr
                                       data-objs prog-objs))
                  (lambda (obj data-objs prog-objs)
                    (vector-set! members i obj)
                    (lp (1+ i) data-objs prog-objs))))
               ((prog-ref-tagged? u16)
                (call-with-values (lambda ()
                                    (prog-object-ref prog-heap addr prog-objs))
                  (lambda (obj prog-objs)
                    (vector-set! members i obj)
                    (lp (1+ i) data-objs prog-objs))))
               (else
                (vector-set! members i (immediate-value u16))
                (lp (1+ i) data-objs prog-objs))))
            (values obj data-objs prog-objs)))))))

(define (data-object-next-addr obj)
  (+ (data-object-addr obj)
     (ash (1+ (vector-length (data-object-members obj))) 1)))

(define-record-type <symbol>
  (make-symbol id)
  %symbol?
  (id symbol-id))

(define (make-ref obj)
  (define (make-immediate/tc8 tag payload)
    (unless (<= 0 payload #xff) (error "bad payload" payload))
    (logior tag payload))
  (define (make-immediate/tc3 tag payload)
    (unless (<= 0 payload #x1fff) (error "bad payload" payload))
    (logior tag payload))
  (match obj
    (($ <data-object> addr)
     (logior (ash addr -1) *data-ref-tc1*))
    (($ <prog-object> addr)
     (logior (ash addr -1) *prog-ref-tc2*))
    ((? number?)
     (unless (<= *fixnum-min* obj *fixnum-max*)
       (error "bad fixnum" obj))
     (make-immediate/tc3 *fixnum-tc3*
                         (if (< obj 0) (+ obj (ash 1 *fixnum-sign-bit*)) obj)))
    (#t (make-immediate/tc8 *true-tc8* 0))
    (#f (make-immediate/tc8 *false-tc8* 0))
    (() (make-immediate/tc8 *eol-tc8* 0))
    (($ <symbol> id) (make-immediate/tc8 *symbol-tc8* id))
    ((? char?) (make-immediate/tc8 *char-tc8* (char->integer obj)))))

(define-record-type <heap-state>
  (make-heap-state prog data sp hp valid?)
  heap-state?
  (prog heap-state-prog)
  (data heap-state-data)
  (sp heap-state-sp)
  (hp heap-state-hp)
  (valid? heap-state-valid?))

(define (allocated-data-objects heap-state)
  (match heap-state
    (($ <heap-state> prog-heap data-heap sp hp valid?)
     (let lp ((addr *hp-start*) (data-objs empty-heap) (prog-objs empty-heap))
       (if (< addr hp)
           (call-with-values
               (lambda ()
                 (data-object-ref data-heap prog-heap addr data-objs prog-objs))
             (lambda (obj data-objs prog-objs)
               (lp (data-object-next-addr obj) data-objs prog-objs)))
           (values data-objs prog-objs))))))

(define (live-data-objects heap-state)
  (match heap-state
    (($ <heap-state> prog-heap data-heap sp hp valid?)
     (let lp ((addr sp) (data-objs empty-heap) (prog-objs empty-heap))
       (if (< addr *sp-start*)
           (let ((u16 (heap-ref-u16 data-heap addr)))
             (cond
              ((data-ref-tagged? u16)
               (call-with-values
                   (lambda ()
                     (data-object-ref data-heap prog-heap u16 data-objs prog-objs))
                 (lambda (obj data-objs prog-objs)
                   (lp (+ addr 2) data-objs prog-objs))))
              (else
               (lp (+ addr 2) data-objs prog-objs))))
           (values data-objs prog-objs))))))

(define (fresh-heap-state prog)
  (make-heap-state prog empty-heap *sp-start* *hp-start* #t))

(define-syntax with-heap
  (syntax-rules (let$ $)
    ((_ (f arg ...) clause ...)
     (let ((heap (f arg ...)))
       (with-heap heap clause ...)))
    ((_ heap (let$ var (f arg ...)) clause ...)
     (call-with-values (lambda () (f heap arg ...))
       (lambda (heap val)
         (let ((var val)) (with-heap heap clause ...)))))
    ((_ heap ($ (f arg ...)))
     (f heap arg ...))
    ((_ heap ($ (f arg ...)) clause ...)
     (with-heap (f heap arg ...) clause ...))
    ((_ heap exp)
     (values heap exp))))

(define ($set-u16 state addr u16)
  (match state
    (($ <heap-state> prog data sp hp valid?)
     (let ((data (heap-set-u16 data addr u16)))
       (make-heap-state prog data sp hp valid?)))))

(define ($invalidate state)
  (match state
    (($ <heap-state> prog data sp hp #t)
     (make-heap-state prog data sp hp #f))))

(define ($set-valid state)
  (match state
    (($ <heap-state> prog data sp hp #f)
     (make-heap-state prog data sp hp #t))))

(define (heap-state-free state)
  (- (heap-state-sp state) (heap-state-hp state)))

(define ($clear-mark-bits state)
  (match state
    (($ <heap-state> prog data sp hp #t)
     (let lp ((data data) (i 0))
       (if (< i *mark-table-size*)
           (lp (heap-set-u8 data (+ *mark-table* i) 0) (1+ i))
           (make-heap-state prog data sp hp #t))))))

(define ($clear-visit-bits state)
  (match state
    (($ <heap-state> prog data sp hp #t)
     (let lp ((data data) (i 0))
       (if (< i *visit-table-size*)
           (lp (heap-set-u8 data (+ *visit-table* i) 0) (1+ i))
           (make-heap-state prog data sp hp #t))))))

(define-inlinable (mark-byte-index addr)
  (ash addr -4))

(define-inlinable (mark-byte-addr addr)
  (+ *mark-table* (mark-byte-index addr)))

(define-inlinable (mark-bit-index addr)
  (logand (ash addr -1) #x7))

(define-inlinable (visit-byte-addr addr)
  (+ (mark-byte-addr addr) *mark-table-size*))
  
(define ($mark-live state)
  (define (mark-byte data addr)
    (heap-ref-u8 data (mark-byte-addr addr)))
  (define (set-mark data addr)
    (heap-set-u8 data (mark-byte-addr addr)
                 (logior (ash 1 (mark-bit-index addr)) (mark-byte data addr))))

  (define (visit-byte data addr)
    (heap-ref-u8 data (visit-byte-addr addr)))
  (define (marked? data addr)
    (logbit? (mark-bit-index addr) (mark-byte data addr)))
  (define (set-visit data addr)
    (heap-set-u8 data (visit-byte-addr addr)
                 (logior (ash 1 (mark-bit-index addr)) (visit-byte data addr))))

  (define (visit-ref data ref)
    (if (data-ref-tagged? ref)
        (let ((addr* (data-ref-addr ref)))
          (if (marked? data addr*)
              data
              (set-visit (set-mark data addr*) addr*)))
        data))
  (define (visit-roots data addr end)
    (let lp ((data data) (addr addr))
      (if (< addr end)
          (lp (visit-ref data (heap-ref-u16 data addr)) (+ addr 2))
          data)))
  (define (visit-object data addr)
    (let* ((header (heap-ref-u16 data addr))
           (len (heap-object-payload-size header))
           (addr (+ addr 2))
           (end (+ addr (* len 2))))
      (let lp ((data data) (addr addr))
        (if (< addr end)
            ;; Mark body for copying but not visiting, because we do
            ;; that now.
            (lp (visit-ref (set-mark data addr) (heap-ref-u16 data addr))
                (+ addr 2))
            data))))

  (define (visit-table-empty? data)
    (let lp ((i 0))
      (or (= i *visit-table-size*)
          (and (zero? (heap-ref-u8 data (+ *visit-table* i)))
               (lp (1+ i))))))
  (define (process-visit-table-byte data i)
    (let ((byte (heap-ref-u8 data (+ *visit-table* i))))
      (if (zero? byte)
          data
          (let lp ((bit 0) (data (heap-set-u8 data (+ *visit-table* i) 0)))
            (if (< bit 8)
                (lp (1+ bit)
                    (if (logbit? bit byte)
                        (visit-object data (* (+ (* i 8) bit) 2))
                        data))
                (process-visit-table-byte data i))))))
  (define (process-visit-table data)
    ;; Going from high to low lets us visit newer objects before older
    ;; objects, which is a win if links are mostly from new to old,
    ;; which they will be unless older objects are mutated.
    (let lp ((i *visit-table-size*) (data data))
      (if (> i 0)
          (lp (1- i) (process-visit-table-byte data (1- i)))
          data)))
  (match state
    (($ <heap-state> prog data sp hp #t)
     (let lp ((data (visit-roots data sp *data-size*)))
       (if (visit-table-empty? data)
           (make-heap-state prog data sp hp #t)
           (lp (process-visit-table data)))))))

(define ($build-forwarding-table state)
  (match state
    (($ <heap-state> prog data sp hp #t)
     (let lp ((i 0) (data data) (sum 0))
       (if (< i *forward-table-size*)
           (lp (+ i 2)
               (heap-set-u16 data (+ *forward-table* i) sum)
               (+ sum (logcount (heap-ref-u16 data (+ *mark-table* i)))))
           (make-heap-state prog data sp hp #t))))))

(define ($compact state)
  (define (reloc data ref)
    (if (data-ref-tagged? ref)
        (let* ((addr (data-ref-addr ref))
               (byte-idx (mark-byte-index addr))
               (bit-idx (mark-bit-index addr))
               (fwd-offset (logand byte-idx (lognot 1)))
               (base (heap-ref-u16 data (+ *forward-table* fwd-offset)))
               ;; Each forward table entry is 16 bits and covers two
               ;; mark entries.  If the mark byte is the second byte,
               ;; add the count from the first byte.
               (base (if (logbit? 0 byte-idx)
                         (let* ((byte-idx0 (+ *mark-table* (1- byte-idx)))
                                (mark0 (heap-ref-u8 data byte-idx0)))
                           (+ base (logcount mark0)))
                         base))
               (mark (heap-ref-u8 data (+ *mark-table* byte-idx)))
               (mask (1- (ash 1 bit-idx)))
               (addr* (+ *hp-start* base (logcount (logand mark mask)))))
          (make-data-ref addr*))
        ref))
  (match state
    (($ <heap-state> prog data sp hp #t)
     (let lp ((i 0) (data data) (hp *hp-start*))
       (if (< i *mark-table-size*)
           (let ((byte (heap-ref-u8 data (+ *mark-table* i))))
             (let visit-bit ((bit 0) (data data) (hp hp))
               (if (< bit 8)
                   (if (logbit? bit byte)
                       (let* ((addr (ash (+ (* i 8) bit) 1))
                              (ref (heap-ref-u16 data addr)))
                         (visit-bit (1+ bit)
                                    (heap-set-u16 data hp (reloc data ref))
                                    (+ hp 2)))
                       (visit-bit (1+ bit) data hp))
                   (lp (1+ i) data hp))))
           ;; Relocate the roots too.
           (let lp ((data data) (addr sp))
             (if (< addr *data-size*)
                 (lp (let ((ref (reloc data (heap-ref-u16 data addr))))
                       (heap-set-u16 data addr ref))
                     (+ addr 2))
                 (make-heap-state prog data sp hp #t))))))))

(define ($gc state)
  (with-heap state
    ($ ($clear-mark-bits))
    ($ ($clear-visit-bits))
    ($ ($mark-live))
    ($ ($build-forwarding-table))
    ($ ($compact))))

(define ($maybe-gc state free reason)
  (if (< (heap-state-free state) free)
      (let ((state ($gc state)))
        (if (< (heap-state-free state) free)
            (error reason free (heap-state-free state))
            state))
      state))

(define ($bump-sp state count)
  (match ($maybe-gc state (* count 2) "stack overflow")
    (($ <heap-state> prog data sp hp #t)
     (let ((sp (- sp (* count 2))))
       (values (make-heap-state prog data sp hp #f)
               sp)))))

(define ($bump-hp state bytes)
  (match ($maybe-gc state bytes "out of memory")
    (($ <heap-state> prog data sp hp #t)
     (let ((hp* (+ hp bytes)))
       (values (make-heap-state prog data sp hp* #f)
               hp)))))

;; the rest of these are for testing

(define ($alloc-obj state tag nfields)
  (with-heap state
    (let$ addr ($bump-hp (* (1+ nfields) 2)))
    ($ ($set-u16 addr (logior tag nfields)))
    addr))

(define ($push state ref)
  (when (data-ref-tagged? ref)
    (error "gc might lose ref to this heap obj" ref))
  (with-heap state
    (let$ sp ($bump-sp 1))
    ($ ($set-u16 sp ref))
    ($ ($set-valid))
    sp))

(define ($cons state car cdr)
  (when (data-ref-tagged? car)
    (error "gc might lose ref to this heap obj" car))
  (when (data-ref-tagged? cdr)
    (error "gc might lose ref to this heap obj" cdr))
  (with-heap state
    (let$ addr ($alloc-obj *pair-heap-tag* 2))
    ($ ($set-u16 (+ addr 2) car))
    ($ ($set-u16 (+ addr 4) cdr))
    ($ ($set-valid))
    (make-data-ref addr)))

(define ($poke state offset ref)
  (with-heap state
    ($ ($set-u16 (+ (heap-state-sp state) offset) ref))))

(define ($poke-cons state car cdr)
  (when (data-ref-tagged? car)
    (error "gc might lose ref to this heap obj" car))
  (when (data-ref-tagged? cdr)
    (error "gc might lose ref to this heap obj" cdr))
  (with-heap state
    (let$ addr ($alloc-obj *pair-heap-tag* 2))
    ($ ($set-u16 (+ addr 2) car))
    ($ ($set-u16 (+ addr 4) cdr))
    ($ ($set-valid))
    ($ ($poke 0 (make-data-ref addr)))))

(define ($push-cons state car cdr)
  (when (data-ref-tagged? car)
    (error "gc might lose ref to this heap obj" car))
  (when (data-ref-tagged? cdr)
    (error "gc might lose ref to this heap obj" cdr))
  (with-heap state
    (let$ sp ($push (make-ref #f)))
    (let$ addr ($alloc-obj *pair-heap-tag* 2))
    ($ ($set-u16 (+ addr 2) car))
    ($ ($set-u16 (+ addr 4) cdr))
    ($ ($set-valid))
    ($ ($set-u16 sp (make-data-ref addr)))
    sp))

;; expectation: no live objects, can run forever
(define (test-cons)
  (let lp ((state (fresh-heap-state empty-heap)))
    (lp ($cons state (make-ref #t) (make-ref #f)))))

;; expectation: stack overflow
(define (test-push)
  (let lp ((state (fresh-heap-state empty-heap)))
    (lp ($push state (make-ref #f)))))

;; expectation: one live object, compacted, can run forever
(define (test-poke-cons)
  (let lp ((state ($push (fresh-heap-state empty-heap) (make-ref #f))))
    (lp ($poke-cons state (make-ref #t) (make-ref #f)))))

;; expectation: stack or heap overflow.
(define (test-push-cons)
  (let lp ((state (fresh-heap-state empty-heap)))
    (lp ($push-cons state (make-ref #t) (make-ref #f)))))

;;; Local Variables:
;;; eval: (put 'with-heap 'scheme-indent-function 1)
;;; End:
