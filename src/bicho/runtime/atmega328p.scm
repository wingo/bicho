(use-modules (rnrs bytevectors))
(define (gc heap)
  (define (ref-u8 addr) (bytevector-u8-ref heap addr))
  (define (set-u8! addr val) (bytevector-u8-set! heap addr val))
  (define (ref-u16 addr) (bytevector-u16-native-ref heap addr))
  (define (set-u16! addr val) (bytevector-u16-native-set! heap addr val))
  (define *heap-bits* 11) ;; 2KB
  (define *heap-size* (ash 1 *heap-bits*))

  ;; atmega328P-PU chip:
  ;;  #x0-#x20: registers
  ;;  #x20-#x60: i/o registers
  (define *heap-start* #x60)
  (define *heap-end* *heap-size*)

  (include "../heap/16-bit-harvard.scm")
  (gc))
