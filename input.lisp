((fn return-two-numbers ()
     (quote (4 4)))
 (eval
   (cons (quote *)
     (cons (quote 4)
       (list (cons (quote *)
               (return-two-numbers)))))))
