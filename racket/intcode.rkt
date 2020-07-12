#lang racket

(require racket/unsafe/ops
	 racket/fixnum)

(provide ; provisions
         step
         send-input
         get-input
         get-output
         read-output
         status
         run-until
         run-until-halt
         done?
         blocked?
         parse-intcode
         run-intcode)

(define (intcode program)
  (define ip 0)                           ; instruction pointer
  (define relative-base 0)                ; offset pointer
  (define memory-1 `#(,@program))         ; memory (also initially the program)
  (define memory-2 (make-eq-hashtable))   ; extra memory for out of range references
  (define in '())                         ; input signals
  (define out '())                        ; output signals
  (define size (vector-length memory-1))  ; size (for use in indexing)
  (define status 'ok)                     ; status for querying

  (define (reset!)
    (set! memory-1 `#(,@program))
    (set! memory-2 (make-eq-hashtable))
    (set! ip 0)
    (set! relative-base 0)
    (set! in '())
    (set! out '())
    (set! status 'ok))

  (define (ip! dx)
    (set! ip (fx+ ip dx)))
  
  (define (rb! dx)
    (set! relative-base (fx+ relative-base dx)))

  (define (store! addr val)
    (if (fx< addr size)
        (vector-set! memory-1 addr val)
        (hashtable-set! memory-2 addr val)))
  
  (define (ref addr)
    (if (fx< addr size)
        (vector-ref memory-1 addr)
        (hashtable-ref memory-2 addr 0)))

  (define (val opcode param)
    (case (digit-at param opcode)
      ((1) (ref (fx+ ip param)))
      ((2) (ref (fx+ relative-base (ref (fx+ ip param)))))
      ((0) (ref (ref (fx+ ip param))))))
  
  (define (addr opcode param)
    (case (digit-at param opcode)
      ((2) (fx+ relative-base (ref (fx+ ip param))))
      ((0) (ref (fx+ ip param)))
      ((1) (error 'intcode "addr is immediate" opcode param))))

  (define (step)
    (let ((op (ref ip)))
      (case (fxmod op 100)
        ((1) (store! (addr op 3) (fx+ (val op 1) (val op 2))) (ip! 4))
        ((2) (store! (addr op 3) (fx* (val op 1) (val op 2))) (ip! 4))
        ((3) (if (null? in) (set! status 'blocking-in)
                 (begin (set! status 'ok) (store! (addr op 1) (pop! in)) (ip! 2))))
        ((4) (set! status 'out) (push! (val op 1) out) (ip! 2))
        ((5) (if (fxzero? (val op 1)) (ip! 3) (set! ip (val op 2))))
        ((6) (if (fxzero? (val op 1)) (set! ip (val op 2)) (ip! 3)))
        ((7) (store! (addr op 3) (if (fx< (val op 1) (val op 2)) 1 0)) (ip! 4))
        ((8) (store! (addr op 3) (if (fx= (val op 1) (val op 2)) 1 0)) (ip! 4))
        ((9) (rb! (val op 1)) (ip! 2))
        ((99) (set! status 'done))
        (else (error 'intcode "bad opcode" op)))))

  (lambda (me . args)
    (case me
      ;; by default status is ok and any other states will be detected
      ;; in step (blocking-in, done, and out)
      ((step) (set! status 'ok) (step) status)
      ;; args represent input signals. generally 1 will be fed at a time
      ;; but this allows for more.
      ((in) (set! in `(,@in ,@args)) (set! status 'ok))
      ;; read the most recent output signal (car), without popping it.
      ((out) (if (null? out) 'no-out (car out)))
      ;; query the status/state of the cell
      ((status) status)
      ;; read the whole output, flushing it, and return in chronological
      ;; order.
      ((read-out!) (let ((tmp (reverse out))) (set! out '()) tmp))
      ;; the following are mostly for debugging and inspection
      ((peek-in) in)
      ((ip) ip)
      ((rb) relative-base)
      ((ref) (apply ref args))
      ((store!) (apply store! args))
      ((reset!) (reset!))
      ((program) program)
      (else (error 'cpu "unknown message" me)))))

(define (parse-intcode . port)
  (define in (if (null? port) (current-input-port) (car port)))
  (map string->number (string-split (read-line in) ",")))

(define (read-memory M addr)
  (M 'ref addr))

(define (store! M addr val)
  (M 'store! addr val))

(define (reset! M)
  (M 'reset!))

(define (step M)
  (M 'step))

(define (send-input M . values)
  (apply M 'in values))

(define (read-output M)
  (M 'read-out!))

(define (get-input M)
  (M 'peek-in))

(define (get-output M)
  (M 'out))

(define (status M)
  (M 'status))

(define (run-until status M)
  (let run ((s (step M)))
    (if (memq s status) s (run (step M)))))

(define (run-until-halt M)
  (run-until '(done blocking-in) M))

(define (done? M)
  (eq? 'done (status M)))

(define (blocked? M)
  (eq? 'blocking-in (status M)))

(define (run-intcode program . input)
  (define M (intcode program))
  (apply M 'in input)
  (run-until-halt M)
  (read-output M))

(define fxmod unsafe-fxmodulo)
(define fx/ unsafe-fxquotient)
(define fx+ unsafe-fx+)
(define fx* unsafe-fx*)
(define make-eq-hashtable make-hasheq)
(define hashtable-set! hash-set!)
(define hashtable-ref hash-ref)
(define (fxzero? x)
  (unsafe-fx= 0 x))

(define-syntax push!
  (lambda (x)
    (syntax-case x ()
      ((_ x xs)
       #'(set! xs (cons x xs))))))

(define-syntax pop!
  (lambda (x)
    (syntax-case x ()
      ((_ xs)
       #'(let ((x (car xs)))
	   (set! xs (cdr xs))
	   x)))))

(define (digit-at i n)
  (fxmod (fx/ n (expt 10 (fx+ i 1))) 10))
