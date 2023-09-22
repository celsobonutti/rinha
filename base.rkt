#lang racket

;; Contracts
(define (summable? a)
  (or (number? a) (string? a)))

(define (comparable? a) (or (number? a) (string? a) (boolean? a)))

(define (simple-pair? a) (and (pair? a) (not (list? a))))

(define/contract (__builtin__sum a b)
  (-> summable? summable? summable?)
  (cond ((and (number? a) (number? b)) (+ a b))
        ((and (string? a) (string? b)) (string-append a b))
        ((and (string? a) (number? b)) (string-append a (number->string b)))
        ((and (number? a) (string? b)) (string-append (number->string a) b))))

(define (/ x y) (quotient x y))
(define (% x y) (remainder x y))

(define/contract (fail-if-not-bool x)
  (-> boolean? boolean?)
  x)

(define/contract (__builtin__or x y)
  (-> boolean? boolean? boolean?)
  (or x y))

(define/contract (__builtin__and x y)
  (-> boolean? boolean? boolean?)
  (and x y))

(define/contract (__builtin__eq? x y)
  (-> comparable? comparable? boolean?)
  (cond ((and (number? x) (number? y)) (eq? x y))
        ((and (string? x) (string? y)) (eq? x y))
        ((and (boolean? x) (boolean? y)) (eq? x y))
        (else (error 'safe-eq? "Arguments not comparable: ~s ~s" x y))))

(define/contract (__builtin__neq? x y)
  (-> comparable? comparable? boolean?)
  (not (__builtin__eq? x y)))

(define/contract (safe-car x)
  (-> simple-pair? any/c)
  (car x))

(define/contract (safe-cdr x)
  (-> simple-pair? any/c)
  (cdr x))

(define show-pair (lambda (x) (string-append "(" (show (car x)) ", " (show (cdr x)) ")")))
(define show (lambda (x) (cond ((string? x) x)
                          ((number? x) (number->string x))
                          ((pair? x) (show-pair x))
                          ((procedure? x) "<#closure>")
                          ((boolean? x) (if x "true" "false")))))

(define __builtin__println (lambda (x) (display (show x)) (newline) x))

(define (memoize f)
  (let ((table (make-hash)))
    (lambda args
      (let ((key (list->vector args)))
        (or (hash-ref table key #f)
            (let ((result (apply f args)))
              (hash-set! table key result)
              result))))))

(define (discard x) x (void))
