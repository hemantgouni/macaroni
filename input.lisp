((fn exp (base exponent)
    (if (== exponent 0)
      1
      (* base (exp base (- exponent 1)))))
 (exp 2 7))
