(define my-even? (lambda (n)
  (if (= n 0)
      #t
      (my-odd? (- n 1)))))

(define my-odd? (lambda (n)
  (if (= n 0)
      #f
      (my-even? (- n 1)))))

(my-even? 1000000)
