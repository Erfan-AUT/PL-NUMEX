;; PL Project - Fall 2019
;; NUMEX interpreter

#lang racket
(provide (all-defined-out)) ;; so we can put tests in a second file
;;(require rebellion/collection/record)

;; definition of structures for NUMEX programs

(struct var  (string) #:transparent)  ;; a variable, e.g., (var "foo")
(struct num  (int)    #:transparent)  ;; a constant number, e.g., (num 17)
(struct bool (boolean) #:transparent)
(struct plus  (e1 e2)  #:transparent)  ;; add two expressions
(struct minus (e1 e2) #:transparent)
(struct mult (e1 e2) #:transparent)
(struct div (e1 e2) #:transparent)
(struct neg (e1) #:transparent)
(struct andalso (e1 e2) #:transparent)
(struct orelse (e1 e2) #:transparent)
(struct cnd (e1 e2 e3) #:transparent)
(struct iseq (e1 e2) #:transparent)
(struct ifnzero (e1 e2 e3) #:transparent)
(struct ifleq (e1 e2 e3 e4) #:transparent)
(struct lam  (nameopt formal body) #:transparent) ;; a recursive(?) 1-argument function
(struct apply (funexp actual)       #:transparent) ;; function application
(struct with (s e1 e2) #:transparent)
(struct apair (e1 e2) #:transparent)
(struct 1st (e1) #:transparent)
(struct 2nd (e1) #:transparent)
(struct munit   ()      #:transparent) ;; unit value -- good for ending a list
(struct ismunit (e1)     #:transparent) ;; if e1 is unit then true else false
;; a closure is not in "source" programs; it is what functions evaluate to
(struct closure (env f) #:transparent) 
(struct key  (s e) #:transparent) ;; key holds corresponding value of s which is e
(struct record (k rm) #:transparent) ;; record holds several keys
(struct value (s r) #:transparent) ;; value returns corresponding value of s in r
(struct letrec (s1 e1 s2 e2 e3) #:transparent) ;; a letrec expression for recursive definitions

;; Problem 1

(define (racketlist->numexlist lst) 
  (cond [(null? lst) (munit)]
        ;; This line had a typo in the submitted version.
        [#t (apair (first lst) (racketlist->numexlist (rest lst)))]
  ))

(define (numexlist->racketlist lst)
  (cond [(munit? lst) null]
        [#t (cons (apair-e1 lst) (numexlist->racketlist (apair-e2 lst)))]
  )
)

;; Problem 2

;; lookup a variable in an environment
;; Complete this function

(define (envlookup env str)
  (let* (
      [currentKey (caar env)]
      [currentValue (cdar env)]
      [restOfEnv (cdr env)]
  )
  (cond [(null? env) (error "Unbound variable found: " str)]
        [(not (string? str)) (error "Non-String names aren't part of the env")]
        [(not (list? env)) (error "Env should be a list")]
        [(equal? currentKey str) currentValue]
  	    [#t (envlookup restOfEnv str)]
	))
)

(define (extendEnvNoEval name val env)
  (cons (cons name val) env)
)


(define (apply-part2 funClosure actualParams)
    (let* ([closFun (closure-f funClosure)]
            [funName (lam-nameopt closFun)])
            
            (if (lam? closFun)
                (eval-under-env 
                    (lam-body closFun) 
                    (extendEnvNoEval (lam-formal closFun) actualParams
                        (extendEnvNoEval (lam-nameopt closFun) funClosure (closure-env funClosure))))
                        
                (error "Closure's function isn't a function")))
)



(define (record-find-key strKey recrd)
  (let ([keyString (key-s (record-k recrd))]
        [keyValue (key-e (record-k recrd))]
        [recordNext (record-rm recrd)])
  (if (eq? strKey keyString)
      keyValue
      (if (munit? (eval-exp recordNext))
          recordNext
          (record-find-key strKey recordNext))))
)

;; Complete more cases for other kinds of NUMEX expressions.
;; We will test eval-under-env by calling it directly even though
;; "in real life" it would be a helper function of eval-exp.
(define (eval-under-env e env)

  (cond [(var? e)
         (cond [(string? (var-string e))(envlookup env (var-string e))]
               [#t (error "Variable should be a string, yours isn't.")])]

        [(bool? e)
         (cond [(boolean? (bool-boolean e)) e]
               [#t (error "bool should be an boolean, yours isn't.")])]

        [(munit? e)
           (munit)]
        
        [(num? e)
         (cond [(integer? (num-int e)) e]
               [#t (error "Num should be an integer, yours isn't.")])]

        [(plus? e) 
         (let ([v1 (eval-under-env (plus-e1 e) env)]
               [v2 (eval-under-env (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number / div by zero")))]
        
        [(minus? e) 
         (let ([v1 (eval-under-env (minus-e1 e) env)]
               [v2 (eval-under-env (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))]

        [(div? e) 
         (let ([v1 (eval-under-env (div-e1 e) env)]
               [v2 (eval-under-env (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2)
                    (not (zero? (num-int v2))))
               (num (quotient (num-int v1) 
                       (num-int v2)))
               (error "NUMEX division applied to non-number")))]
               
        [(mult? e) 
         (let ([v1 (eval-under-env (mult-e1 e) env)]
               [v2 (eval-under-env (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX multiplication applied to non-number")))]

        [(neg? e) 
         (let ([v1 (eval-under-env (neg-e1 e) env)])
           (if (num? v1)
               (num (- (num-int v1)))
               (if (bool? v1)
                    (bool (not (bool-boolean v1)))
               (error "NUMEX negation applied to non-number"))))]

        [(andalso? e) 
         (let ([v1 (eval-under-env (andalso-e1 e) env)])
          
           (if (and (bool? v1)
                    (eq? (bool-boolean v1) #f)) v1
              (let ([v2 (eval-under-env (andalso-e2 e) env)])
               (if (bool? v2) v2
                   (error "NUMEX andalso applied to non-bool")))))]
        
        [(orelse? e) 
         (let ([v1 (eval-under-env (orelse-e1 e) env)])
          
           (if (and (bool? v1)
                    (bool-boolean v1)) v1
              (let ([v2 (eval-under-env (orelse-e2 e) env)])
               (if (bool? v2) v2
                   (error "NUMEX orelse applied to non-bool")))))]
                   
        [(cnd? e) 
          (let ([v1 (eval-under-env (cnd-e1 e) env)])
            (if (bool? v1)
                (if (bool-boolean v1) 
                      (let ([v2 (eval-under-env (cnd-e2 e) env)]) v2) 
                (eval-under-env (cnd-e3 e) env))
                (error "Not boo-lean meat!"))
          )]

        [(iseq? e) 
         (let ([v1 (eval-under-env (iseq-e1 e) env)]
               [v2 (eval-under-env (iseq-e2 e) env)])
               (cond [(bool? v1)
                      (cond [(bool? v2) (bool (eq? (bool-boolean v1) (bool-boolean v2)))]
                            [#t (bool #f)])]
                     [(num? v1)
                      (cond [(num? v2) (bool (eq? (num-int v1) (num-int v2)))]
                            [#t (bool #f)])]
               [#t (error "sth is def wrong!")])
          )]

        [(ifnzero? e) 
          (let ([v1 (eval-under-env (ifnzero-e1 e) env)])
            (if (num? v1)
                (if (zero? (num-int v1)) 
                        (let ([v3 (eval-under-env (ifnzero-e3 e) env)]) v3) 
                (let ([v2 (eval-under-env (ifnzero-e2 e) env)])
                  v2))
            (error "UNNumber!"))
          )]     

        [(ifleq? e) 
        (let ([v1 (eval-under-env (ifleq-e1 e) env)]
              [v2 (eval-under-env (ifleq-e2 e) env)])
          (if (and (num? v1)
                    (num? v2))
                      (if (> (num-int v1) (num-int v2))
                        (eval-under-env (ifleq-e4 e) env)         
                        (eval-under-env (ifleq-e3 e) env))
                (error "One of them is not an integer."))
        )]  
        
        [(ismunit? e)
          (let ([v1 (eval-under-env (ismunit-e1 e) env)])
              (if (munit? v1) (bool #t) (bool #f))
          )]

        [(apair? e)
         (let ([v1 (eval-under-env (apair-e1 e) env)]
               [v2 (eval-under-env (apair-e2 e) env)])
           (apair v1 v2))]
     
        [(with? e)
         (define name (with-s e))
         (let ([v1 (eval-under-env (with-e1 e) env)])
           (eval-under-env (with-e2 e) (extendEnvNoEval name v1 env)))]
        
        [(closure? e) e]

        [(lam? e)
         (closure env e)]
       
        ;; Because lam's should always be applied and are meaningless if otherwise evaluated,
        ;; This function's conditioning serves us well.
        [(apply? e)
        (let* ([funClosure (eval-under-env (apply-funexp e) env)]
                [actualParams (eval-under-env (apply-actual e) env)])
            (if (closure? funClosure)
              (apply-part2 funClosure actualParams)
              (if (lam? funClosure)
                (let* ([lamToFunClosure (eval-under-env funClosure env)])
                    (apply-part2 lamToFunClosure actualParams))
                (error "Function doesn't return closure!")))
        )]
        
        [(1st? e)
        (let ([v1 (eval-under-env (1st-e1 e) env)])
            (if (apair? v1) (apair-e1 v1)
                (error ("First part isn't a pair")))
        )]

        [(2nd? e)
        (let ([v1 (eval-under-env (2nd-e1 e) env)])
            (if (apair? v1) (apair-e2 v1)
                (error ("second part isn't a pair")))
        )]

        [(letrec? e)
            (let (  [s1 (letrec-s1 e)]
                    [s2 (letrec-s2 e)]
                    [e1 (letrec-e1 e)]
                    [e2 (letrec-e2 e)]
                    [e3 (letrec-e3 e)])
            (eval-under-env e3
                (extendEnvNoEval s1 e1
                    (extendEnvNoEval s2 e2 env)))
        )]
 
        
        [(key? e)
          (let ([ev (eval-under-env (key-e e) env)])
            (if (string? (key-s e)) e
                (error "Not a proper key")))]

        [(record? e)
         (let ([sk (eval-under-env (record-k e) env)]
               [rm (eval-under-env (record-rm e) env)])
            (if (key? sk)
              (if (or (munit? (eval-exp rm))
                      (record? rm))
                  (record sk rm)
                  (error ("Bad record")))
              (error "improper key")))]
              

        [(value? e)
          (let ([r (eval-under-env (value-r e) env)]
                [keyStr (value-s e)])
              (if (and (string? keyStr)
                       (record? r))
                       (record-find-key keyStr r)
                  (error "Problematic key")))]      
        
        [#t (error (format "bad NUMEX expression: ~v" e))]))

;; Do NOT change
(define (eval-exp e)
  (eval-under-env e null))
        
;; Problem 3

;; These functions should return NUMEX expressions and not evaluate anything.

(define (ifmunit e1 e2 e3)
   (cnd (ismunit e1) e2 e3)
)


(define (with* bindings e)
  (let* (
    [currentS (caar bindings)]
    [currentE (cdar bindings)]
    [next (cdr bindings)]
  )
  (if (null? next) 
      (with currentS currentE e)
      (with currentS currentE (with* next e))
  )
))

;; This should be a macro, meaning it shouldn't evaluate anything (including when we're not using
;; eval-exp)
(define (ifneq e1 e2 e3 e4) 
    (cnd (iseq e1 e2) e4 e3)
)

;; Problem 4

;; This function should use NUMEX syntax entirely.
(define numex-filter 
  (lam "outer" "mapper" 
    (lam "map" "list" 
    ; Must be cnd and not if! It's a numex function after all.
      (cnd (ismunit (var "list")) 
        (munit)
        (with "result" (apply (var "mapper") (1st (var "list"))) 
          ;; Must be Numex's ifnzero, unless it'll get evaluated immediately!
          (ifnzero (var "result")
            (apair (var "result") (apply (var "map") (2nd (var "list"))))
            (apply (var "map") (2nd (var "list"))))))
)))

;; This function should use NUMEX syntax entirely.
(define numex-all-gt
  (with "filter" numex-filter
    (lam null "i"
      (lam null "lst"
        (apply 
          (apply (var "filter")
              (lam null "current" ; This is our mapper
                ;; If you reverse the order in here, the function will return a wrong value!
                (ifleq (var "current") (var "i") 
                        (num 0) ;; Disregards 0 itself.

                        (var "current"))))
                (var "lst"))
))))
 

;; Challenge Problem

(struct fun-challenge (nameopt formal body freevars) #:transparent) ;; a recursive(?) 1-argument function

;; We will test this function directly, so it must do
;; as described in the assignment

;; sCompute : Compute free-variables for a struct with a "S"ingle inner value.
;; dCompute : Compute free-variables for a struct with a "D"ouble inner value.
;; tCompute : Compute free-variables for a struct with a "T"riple inner value.
;; qCompute : Compute free-variables for a struct with a "Q"uadruple inner value.

;; These compute-free-vars functions should be applied in the same manner as 
;; eval-env, because they both are really trying to extract their results
;; Using a top-down approach.

;; The set becomes our new env

;; Type is the constructor for our given type, because we
;; Want to use this function for various single-valued types.
;; Expr is our expression, whose inner value (same as eval-env)
;; is going to be constructed of our type after evaluating its
;; inner value for further reference.
(define (sCompute type expr extrFun)
    (let ([v (compute-free-vars-with-e (extrFun expr))])
        (cons (type (car v)) (cdr v)))
)

;; ExtrFun1 extracts the expression's first value.
(define (dCompute type expr extrFun1 extrFun2)
    (let ([v1 (compute-free-vars-with-e (extrFun1 expr))]
          [v2 (compute-free-vars-with-e (extrFun2 expr))])

        (cons (type (car v1) (car v2)) 
              (set-union (cdr v1) (cdr v2) ))
))

(define (tCompute type expr extrFun1 extrFun2 extrFun3)
    (let ([v1 (compute-free-vars-with-e (extrFun1 expr))]
          [v2 (compute-free-vars-with-e (extrFun2 expr))]
          [v3 (compute-free-vars-with-e (extrFun3 expr))])

        (cons (type (car v1) (car v2) (car v3)) 
              (set-union (cdr v1) 
                (set-union (cdr v2) (cdr v3))))
))

(define (qCompute type expr extrFun1 extrFun2 extrFun3 extrFun4)
    (let ([v1 (compute-free-vars-with-e (extrFun1 expr))]
          [v2 (compute-free-vars-with-e (extrFun2 expr))]
          [v3 (compute-free-vars-with-e (extrFun3 expr))]
          [v4 (compute-free-vars-with-e (extrFun4 expr))])

        (cons (type (car v1) (car v2) (car v3) (car v4)) 
              (set-union (cdr v1) 
                (set-union (cdr v2) 
                    (set-union (cdr v3) (cdr v4)))))
))

;;;;;; TODO: do this for letrec and record.

;; THIS IS OUR EQUIVALENT TO EVAL-ENV
;; With the difference that it returns a cons 
;; (expression, free vars)
(define (compute-free-vars-with-e e)
    (cond
        [(var? e)
            (cons e (set (var-string e)))]
        ;; The following returns an empty set because
        ;; They are immediate values and have no free vars.
        [(or (num? e)
             (bool? e)
             (munit? e)
             (closure? e))

             (cons e (set))]
        [(neg? e)
            (sCompute neg e neg-e1)]
        [(1st? e)
            (sCompute 1st e 1st-e1)]
        [(2nd? e)
            (sCompute 2nd e 2nd-e1)]
        [(ismunit? e)
            (sCompute ismunit e ismunit-e1)]
        
        [(plus? e)
            (dCompute plus e plus-e1 plus-e2)]
        [(minus? e)
            (dCompute minus e minus-e1 minus-e2)]
        [(mult? e)
            (dCompute mult e mult-e1 mult-e2)]
        [(div? e)
            (dCompute div e div-e1 div-e2)]
        [(apair? e)
            (dCompute apair e apair-e1 apair-e2)]
        [(andalso? e)
            (dCompute andalso e andalso-e1 andalso-e2)]
        [(orelse? e)
            (dCompute orelse e orelse-e1 orelse-e2)]
        [(iseq? e)
            (dCompute iseq e iseq-e1 iseq-e2)]
        [(apply? e)
            (dCompute apply e apply-funexp apply-actual)]
        [(key? e)
            (dCompute key e key-s key-e)]
        [(record? e)
            (dCompute record e record-k record-rm)]
        [(value? e)
            (dCompute value e value-s value-r)]
        
        [(cnd? e)
            (tCompute cnd e cnd-e1 cnd-e2 cnd-e3)]
        [(ifnzero? e)
            (tCompute ifnzero e ifnzero-e1 ifnzero-e2 ifnzero-e3)]
        
        [(ifleq? e)
            (qCompute ifleq e ifleq-e1 ifleq-e2 ifleq-e3 ifleq-e4)]

        [(letrec? e)
            (let* (
                [s1 (letrec-s1 e)]
                [s2 (letrec-s2 e)]
                [v1 (compute-free-vars-with-e (letrec-e1 e))]
                [v2 (compute-free-vars-with-e (letrec-e2 e))]
                [v3 (compute-free-vars-with-e (letrec-e3 e))]
                [v1e (car v1)]
                [v1vars (cdr v1)]
                [v2e (car v2)]
                [v2vars (cdr v2)]
                [v3e (car v3)]
                [v3vars (cdr v3)]
                )
            (cons (letrec s1 v1e s2 v2e v3e)
                (set-remove 
                  (set-remove 
                    (set-union v1vars 
                        (set-union v2vars v3vars)) 
                    s1) s2))
        )]

        
        ;; Up until here, none of our expresssions were named,
        ;; So we'd just map their "mapEnv"s to the expressions
        ;; Themselves, but everything changes from here on out.
        [(lam? e)
            (let* (
                [body (lam-body e)]
                [name (lam-nameopt e)]
                [formalParams (lam-formal e)]
                [pure-free-vars (cdr (compute-free-vars-with-e body))]
                ;; We remove the function's formal parameters
                ;; And its name because they're bound in it
                ;; By default; we only need FREE variables.
                [filtered-free-vars 
                    (set-remove 
                        (set-remove pure-free-vars name) formalParams)]
                )
                (cons 
                    (fun-challenge name formalParams body filtered-free-vars) 
                    filtered-free-vars)
        )]
        ;; This is the reason we made our compute-free-vars-with-e return the cons it returns
        ;; This and letrec need to have both the expression and their bound vars in order to 
        ;; compute the final free vars.
        [(with? e)
            (let* (
                [s (with-s e)]
                [v1 (compute-free-vars-with-e (with-e1 e))]
                [v2 (compute-free-vars-with-e (with-e2 e))]
                [v1e (car v1)]
                [v1vars (cdr v1)]
                [v2e (car v2)]
                [v2vars (cdr v2)]
                )
            (cons 
                (with s v1e v2e) 
                (set-remove 
                    (set-union v1vars v2vars) 
                    s))
        )]
        [#t (error "BAUD numEX")]
        
    )
)

;; Because we decided to return a pair of e's evaluation
;; results and the set it's mapped to, for convenience.
(define (compute-free-vars e)
    (car (compute-free-vars-with-e e))
)

(define (remove-bound-vars env free-vars-set)
    (if (empty? env)
        env
        ;; If the variables is a free one, keep it in env
        ;; And remove it otherwise.
        (let* (
        [currentVar (caar env)]
        [envUntilHere (car env)]
        [restOfEnv (cdr env)])
        (if (set-member? free-vars-set currentVar)
            (cons envUntilHere (remove-bound-vars restOfEnv free-vars-set))
            (remove-bound-vars restOfEnv free-vars-set)
        ))
    )
)

;; Do NOT share code with eval-under-env because that will make grading
;; more difficult, so copy most of your interpreter here and make minor changes
(define (eval-under-env-c e env)

  (cond [(var? e)
         (cond [(string? (var-string e))(envlookup env (var-string e))]
               [#t (error "Variable should be a string, yours isn't.")])]

        [(bool? e)
         (cond [(boolean? (bool-boolean e)) e]
               [#t (error "bool should be an boolean, yours isn't.")])]

        [(munit? e)
           (munit)]
        
        [(num? e)
         (cond [(integer? (num-int e)) e]
               [#t (error "Num should be an integer, yours isn't.")])]

        [(plus? e) 
         (let ([v1 (eval-under-env-c (plus-e1 e) env)]
               [v2 (eval-under-env-c (plus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (+ (num-int v1) 
                       (num-int v2)))
               (error "NUMEX addition applied to non-number / div by zero")))]
        
        [(minus? e) 
         (let ([v1 (eval-under-env-c (minus-e1 e) env)]
               [v2 (eval-under-env-c (minus-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (- (num-int v1) 
                       (num-int v2)))
               (error "NUMEX subtraction applied to non-number")))]

        [(div? e) 
         (let ([v1 (eval-under-env-c (div-e1 e) env)]
               [v2 (eval-under-env-c (div-e2 e) env)])
           (if (and (num? v1)
                    (num? v2)
                    (not (zero? (num-int v2))))
               (num (quotient (num-int v1) 
                       (num-int v2)))
               (error "NUMEX division applied to non-number")))]
               
        [(mult? e) 
         (let ([v1 (eval-under-env-c (mult-e1 e) env)]
               [v2 (eval-under-env-c (mult-e2 e) env)])
           (if (and (num? v1)
                    (num? v2))
               (num (* (num-int v1) 
                       (num-int v2)))
               (error "NUMEX multiplication applied to non-number")))]

        [(neg? e) 
         (let ([v1 (eval-under-env-c (neg-e1 e) env)])
           (if (num? v1)
               (num (- (num-int v1)))
               (if (bool? v1)
                    (bool (not (bool-boolean v1)))
               (error "NUMEX negation applied to non-number"))))]

        [(andalso? e) 
         (let ([v1 (eval-under-env-c (andalso-e1 e) env)])
          
           (if (and (bool? v1)
                    (eq? (bool-boolean v1) #f)) v1
              (let ([v2 (eval-under-env-c (andalso-e2 e) env)])
               (if (bool? v2) v2
                   (error "NUMEX andalso applied to non-bool")))))]
        
        [(orelse? e) 
         (let ([v1 (eval-under-env-c (orelse-e1 e) env)])
          
           (if (and (bool? v1)
                    (bool-boolean v1)) v1
              (let ([v2 (eval-under-env-c (orelse-e2 e) env)])
               (if (bool? v2) v2
                   (error "NUMEX orelse applied to non-bool")))))]
                   
        [(cnd? e) 
          (let ([v1 (eval-under-env-c (cnd-e1 e) env)])
            (if (bool? v1)
                (if (bool-boolean v1) 
                      (let ([v2 (eval-under-env-c (cnd-e2 e) env)]) v2) 
                (eval-under-env-c (cnd-e3 e) env))
                (error "Not boo-lean meat!"))
          )]

        [(iseq? e) 
         (let ([v1 (eval-under-env-c (iseq-e1 e) env)]
               [v2 (eval-under-env-c (iseq-e2 e) env)])
               (cond [(bool? v1)
                      (cond [(bool? v2) (bool (eq? (bool-boolean v1) (bool-boolean v2)))]
                            [#t (bool #f)])]
                     [(num? v1)
                      (cond [(num? v2) (bool (eq? (num-int v1) (num-int v2)))]
                            [#t (bool #f)])]
               [#t (error "sth is def wrong!")])
          )]

        [(ifnzero? e) 
          (let ([v1 (eval-under-env-c (ifnzero-e1 e) env)])
            (if (num? v1)
                (if (zero? (num-int v1)) 
                        (let ([v3 (eval-under-env-c (ifnzero-e3 e) env)]) v3) 
                (let ([v2 (eval-under-env-c (ifnzero-e2 e) env)])
                  v2))
            (error "UNNumber!"))
          )]     

        [(ifleq? e) 
        (let ([v1 (eval-under-env-c (ifleq-e1 e) env)]
              [v2 (eval-under-env-c (ifleq-e2 e) env)])
          (if (and (num? v1)
                    (num? v2))
                      (if (> (num-int v1) (num-int v2))
                        (eval-under-env-c (ifleq-e4 e) env)         
                        (eval-under-env-c (ifleq-e3 e) env))
                (error "One of them is not an integer."))
        )]  
        
        [(ismunit? e)
          (let ([v1 (eval-under-env-c (ismunit-e1 e) env)])
              (if (munit? v1) (bool #t) (bool #f))
          )]

        [(apair? e)
         (let ([v1 (eval-under-env-c (apair-e1 e) env)]
               [v2 (eval-under-env-c (apair-e2 e) env)])
           (apair v1 v2))]
     
        [(with? e)
         (define name (with-s e))
         (let ([v1 (eval-under-env-c (with-e1 e) env)])
           (eval-under-env-c (with-e2 e) (extendEnvNoEval name v1 env)))]
        
        [(closure? e) e]

        ;; Lam doesn't exist in this context anymore!
        ;; Therefore both lam and apply are subject to change.

        [(fun-challenge? e)
         (closure (remove-bound-vars env (fun-challenge-freevars e)) e)]
       
        ;; Because lam's should always be applied and are meaningless if otherwise evaluated,
        ;; This function's conditioning serves us well.
        [(apply? e)
        (let* ([funClosure (eval-under-env-c (apply-funexp e) env)]
                [actualParams (eval-under-env-c (apply-actual e) env)])
            (if (closure? funClosure)
              (apply-part2 funClosure actualParams)
              (if (lam? funClosure)
                (let* ([lamToFunClosure (eval-under-env-c funClosure env)])
                    (apply-part2 lamToFunClosure actualParams))
                (error "Function doesn't return closure!")))
        )]
        
        [(1st? e)
        (let ([v1 (eval-under-env-c (1st-e1 e) env)])
            (if (apair? v1) (apair-e1 v1)
                (error ("First part isn't a pair")))
        )]

        [(2nd? e)
        (let ([v1 (eval-under-env-c (2nd-e1 e) env)])
            (if (apair? v1) (apair-e2 v1)
                (error ("second part isn't a pair")))
        )]

        [(letrec? e)
            (let ([s1 (letrec-s1 e)]
                    [s2 (letrec-s2 e)]
                    [e1 (letrec-e1 e)]
                    [e2 (letrec-e2 e)]
                    [e3 (letrec-e3 e)])
            (eval-under-env-c e3
                (extendEnvNoEval s1 e1
                    (extendEnvNoEval s2 e2 env)))
        )]
 
        
        [(key? e)
          (let ([ev (eval-under-env-c (key-e e) env)])
            (if (string? (key-s e)) e
                (error "Not a proper key")))]

        [(record? e)
         (let ([sk (eval-under-env-c (record-k e) env)]
               [rm (eval-under-env-c (record-rm e) env)])
            (if (key? sk)
              (if (or (munit? (eval-exp rm))
                      (record? rm))
                  (record sk rm)
                  (error ("Bad record")))
              (error "improper key")))]
              

        [(value? e)
          (let ([r (eval-under-env-c (value-r e) env)]
                [keyStr (value-s e)])
              (if (and (string? keyStr)
                       (record? r))
                       (record-find-key keyStr r)
                  (error "Problematic key")))]      
        
        [#t (error (format "bad NUMEX expression: ~v" e))]))




;; Do NOT change this
(define (eval-exp-c e)
  (eval-under-env-c (compute-free-vars e) null))

