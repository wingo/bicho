;; Free variables to be defined by caller:
;; ref-u8 addr -> u8
;; set-u8! addr u8
;; ref-u16 addr -> u16
;; set-u16! addr u16
;; *heap-size*

(define *heap-end* *heap-size*)

;; atmega328P-PU chip:
;;  #x0-#x20: registers
;;  #x20-#x60: i/o registers
(define *heap-start* #x60)

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
(define *mark-table* *heap-start*)
(define *mark-table-size* (ash *heap-end* -4))
;; #xe0-#x160 visit bits; a worklist for marking.
(define *visit-table* (+ *mark-table* *mark-table-size*))
(define *visit-table-size* *mark-table-size*)
;; #xe0-#x100 forwarding table, sharing space with visit table
(define *forward-table* (+ *mark-table* *mark-table-size*))
(define *forward-table-mark-bits-per-entry* 16)
(define *forward-table-mark-bytes-per-entry*
  (ash *forward-table-mark-bits-per-entry* -3))
(define *forward-table-size*
  (* (/ *mark-table-size* *forward-table-mark-bytes-per-entry*) 2))

;; the inliner doesn't know about "max" unfortunately; define a
;; version here that it can deal with
(define (max a b)
  (if (< a b) b a))

(define *alloc-start*
  (max (+ *forward-table* *forward-table-size*)
       (+ *visit-table* *visit-table-size*)))
(define *stack-start*
  *heap-end*)

;; Object reference ("ref") representation.  We differentiate between
;; references to data in RAM ("heap refs") and all other
;; references, including ROM references.

;; Tag in high bit.
(define *heap-ref-tag-mask* (ash 1 15))
(define *heap-ref-tag* (ash 1 15))
(define (heap-ref-tagged? u16)
  (= (logand u16 *heap-ref-tag-mask*) *heap-ref-tag*))
(define (heap-ref-addr u16)
  (unless (heap-ref-tagged? u16) (error "badness" u16))
  (- u16 *heap-ref-tag*))
(define (make-heap-ref addr)
  (+ addr *heap-ref-tag*))

;; Heap objects have a length field in their first word.
(define *heap-object-payload-size-mask* #x0fff)
(define (heap-object-payload-size header)
  (logand header *heap-object-payload-size-mask*))

(define (clear-mark-bits!)
  (let lp ((i 0))
    (when (< i *mark-table-size*)
      (set-u8! (+ *mark-table* i) 0)
      (lp (1+ i)))))

(define (clear-visit-bits!)
  (let lp ((i 0))
    (when (< i *visit-table-size*)
      (set-u8! (+ *visit-table* i) 0)
      (lp (1+ i)))))

;; >>1 because 16-bit alignment, then >>3 because 8 marks per byte.
(define (mark-byte-index addr)
  (ash addr -4))

(define (mark-byte-addr addr)
  (+ *mark-table* (mark-byte-index addr)))

;; >>1 because 16-bit alignment.
(define (mark-bit-index addr)
  (logand (ash addr -1) #x7))

;; The mark table can be addressed in 16-bit units as well.
(define (mark-u16-index addr)
  (ash addr -5))
(define (mark-u16-bit-index addr)
  (logand (ash addr -1) #xf))

(define (visit-byte-addr addr)
  (+ (mark-byte-addr addr) *mark-table-size*))
  
(define (mark-live!)
  (define (set-bit! addr bit)
    (set-u8! addr (logior (ash 1 bit) (ref-u8 addr))))

  (define (marked? addr)
    (logbit? (mark-bit-index addr) (ref-u8 (mark-byte-addr addr))))
  (define (set-mark! addr)
    (set-bit! (mark-byte-addr addr) (mark-bit-index addr)))
  (define (set-visit! addr)
    (set-bit! (visit-byte-addr addr) (mark-bit-index addr)))

  (define (visit-ref ref)
    (when (heap-ref-tagged? ref)
      (let ((addr (heap-ref-addr ref)))
	(unless (marked? addr)
	  (set-mark! addr)))))
  (define (visit-roots addr end)
    (let lp ((addr addr))
      (when (< addr end)
	(visit-ref (ref-u16 addr))
	(lp (+ addr 2)))))
  (define (visit-object addr)
    (let* ((header (ref-u16 addr))
           (len (heap-object-payload-size header))
           (addr (+ addr 2))
           (end (+ addr (* len 2))))
      (let lp ((addr addr))
        (when (< addr end)
	  ;; Mark body for copying.
	  (set-mark! addr)
	  (visit-ref (ref-u16 addr))
	  (lp (+ addr 2))))))

  (define (visit-table-empty?)
    (let lp ((i 0))
      (or (= i *visit-table-size*)
          (and (zero? (ref-u8 (+ *visit-table* i)))
               (lp (1+ i))))))
  (define (process-visit-table-byte i)
    (let ((byte (ref-u8 (+ *visit-table* i))))
      (unless (zero? byte)
	(set-u8! (+ *visit-table* i) 0)
	(let lp ((bit 0))
	  (when (< bit 8)
	    (when (logbit? bit byte)
	      (visit-object (* (+ (* i 8) bit) 2)))
	    (lp (1+ bit))))
	(process-visit-table-byte i))))
  (define (process-visit-table)
    ;; Going from high to low lets us visit newer objects before older
    ;; objects, which is a win if links are mostly from new to old,
    ;; which they will be unless older objects are mutated.
    (let lp ((i *visit-table-size*))
      (when (> i 0)
	(process-visit-table-byte (1- i))
	(lp (1- i)))))

  (visit-roots *stack-start* *heap-end*)
  (let lp ()
    (unless (visit-table-empty?)
      (process-visit-table)
      (lp))))

(define (build-forwarding-table!)
  (define (logcount16 n)
    (let* ((n (+ (logand #x5555 n) (logand #x5555 (ash n -1))))
	   (n (+ (logand #x3333 n) (logand #x3333 (ash n -2))))
	   (n (+ (logand #x0f0f n) (logand #x0f0f (ash n -4)))))
      (+ (logand n #x00ff) (logand #x00ff (ash n -8)))))
  (let lp ((i 0) (sum 0))
    (when (< i *forward-table-size*)
      (set-u16! (+ *forward-table* i) sum)
      (lp (+ i 2) (+ sum (logcount16 (ref-u16 (+ *mark-table* i))))))))

(define (compact!)
  ;; Duplicated logcount16 so that we are sure that it is inlined.
  (define (logcount16 n)
    (let* ((n (+ (logand #x5555 n) (logand #x5555 (ash n -1))))
	   (n (+ (logand #x3333 n) (logand #x3333 (ash n -2))))
	   (n (+ (logand #x0f0f n) (logand #x0f0f (ash n -4)))))
      (+ (logand n #x00ff) (logand #x00ff (ash n -8)))))
  (define (reloc-addr addr)
    (let* ((u16-idx (mark-u16-index addr))
	   (bit-idx (mark-u16-bit-index addr))
	   (base (ref-u16 (+ *forward-table* (* u16-idx 2))))
	   (mark (ref-u16 (+ *mark-table* (* u16-idx 2))))
	   (mask (1- (ash 1 bit-idx))))
      (+ *alloc-start* base (logcount16 (logand mark mask)))))
  (define (reloc ref)
    (if (heap-ref-tagged? ref)
        (make-heap-ref (reloc-addr (heap-ref-addr ref)))
        ref))

  ;; Relocate the roots.
  (let lp ((addr *stack-start*))
    (when (< addr *heap-end*)
      (set-u16! addr (reloc (ref-u16 addr)))
      (lp (+ addr 2))))
  ;; Compact and relocate the heap.  Return the new heap pointer when
  ;; done.
  (let lp ((i 0) (hp *alloc-start*))
    (if (< i *mark-table-size*)
	(let ((byte (ref-u8 (+ *mark-table* i))))
	  (let visit-bit ((bit 0) (hp hp))
	    (if (< bit 8)
		(if (logbit? bit byte)
		    (let ((addr (ash (+ (* i 8) bit) 1)))
		      (set-u16! hp (reloc (ref-u16 addr)))
		      (visit-bit (1+ bit) (+ hp 2)))
		    (visit-bit (1+ bit) hp))
		(lp (1+ i) hp))))
	hp)))

(define (gc)
  (clear-mark-bits!)
  (clear-visit-bits!)
  (mark-live!)
  (build-forwarding-table!)
  (compact!))

(unless (<= *heap-end* (ash 1 15))
  (error "invalid heap size"))
