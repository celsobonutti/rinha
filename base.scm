;; Functions for checking types
(define neq? (lambda (x y) (not (eq? x y))))
(define bool? (lambda (x) (or (eq? x #t) (eq? x #f))))
(define safe-if (lambda (p c a) (if (bool? p) (if p c a) (error 'safe-if "Predicate not a boolean: ~s" p))))
(define safe-car (lambda (x) (if (pair? x) (car x) (error 'safe-car "Argument not a pair: ~s" x))))
(define safe-cdr (lambda (x) (if (pair? x) (cdr x) (error 'safe-cdr "Argument not a pair: ~s" x))))
(define safe-or (lambda (x y) (if (and (bool? x) (bool? y)) (or x y) (error 'safe-or "Arguments not booleans: ~s ~s" x y))))
(define safe-and (lambda (x y) (if (and (bool? x) (bool? y)) (and x y) (error 'safe-and "Arguments not booleans: ~s ~s" x y))))

;; Functions for showing values and printing them to the console
(define show-pair (lambda (x) (string-append "(" (show (car x)) ", " (show (cdr x)) ")")))
(define show (lambda (x) (cond ((string? x) x)
                          ((number? x) (number->string x))
                          ((pair? x) (show-pair x))
                          ((procedure? x) "<#closure>")
                          ((bool? x) (if x "true" "false")))))
(define print (lambda (x) (display (show x)) newline x))
