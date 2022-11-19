Macaroni is a language for prototyping easy-to-use analysis-aware macros
(without having to rely on things like elaborator programming). It currently
implements a simple dynamically typed lisp-like language. Here's an example
program that sorts a list: 

```lisp
((fn length (input-list)
   (if (empty? input-list) 0 (+ 1 (length (cdr input-list)))))
 (fn merge (input-list-1 input-list-2)
   (if (empty? input-list-1)
       input-list-2
       (if (empty? input-list-2)
           input-list-1
           (let elem-1 (car input-list-1)
             (let elem-2 (car input-list-2)
               (if (|| (< elem-1 elem-2) (== elem-1 elem-2))
                   (cons elem-1 (merge (cdr input-list-1) input-list-2))
                   (cons elem-2 (merge input-list-1 (cdr input-list-2)))))))))
 (fn take (num input-list)
   (if (== num 0)
       (list)
       (cons (car input-list) (take (- num 1) (cdr input-list)))))
 (fn drop (num input-list)
   (if (== num 0) input-list (drop (- num 1) (cdr input-list))))
 (fn sort (input-list)
   (if (|| (empty? input-list) (== (length input-list) 1))
       input-list
       (let half-length (/ (length input-list) 2)
         (merge (sort (take half-length input-list))
                (sort (drop half-length input-list))))))
 (sort (list 8 11 3 4 7)))
```

As you can see, it's pretty minimal. The end goal is to have a macro system
capable of interleaving macro expansion with existing compiler analyses,
conditionally generating code based on analysis results. 
