((macro add-plus (list-of-nums)
   (cons (quote +) list-of-nums))
 (+ 1 (add-plus (2 5))))
