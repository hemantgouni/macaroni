((declare staged-exp-helper (-> (I64 I64) I64))
 (fn staged-exp-helper (base exp)
   (if (== exp 0)
     1
     (list (quote *) base (staged-exp-helper base (- exp 1)))))
 (declare-macrotype staged-exp (I64 (Lit I64)) "Integer expected, got ???")
 (macro staged-exp (base exp)
   (staged-exp-helper base exp))
 (staged-exp (+ 1 1) 7))
