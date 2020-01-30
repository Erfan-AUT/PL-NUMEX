#| (define (extendEnv ky unevaled env)
(cons (cons ky (eval-under-env unevaled env)) env))


(define (extendEnvReturnCons env ky unevaled)
  (let ([evaled (eval-under-env unevaled env)])
      (cons evaled (extendEnvNoEval ky evaled env))
)) |#

#| (define (appendEnv name val env)
    (if (munit? env) 
        (cons (cons name val) env)
        (cons (car (env) (appendEnv name val (cdr env))))
    )
) |#
        
        
#|        [(lam? e)
         (closure env e)]
       
        [(apply? e)
        (let* ([funClosure (eval-under-env (apply-funexp e) env)]
                [actualParams (eval-under-env (apply-actual e) env)])
            (if (closure? funClosure)
              (let* ([closFun (closure-f funClosure)]
                    [funName (lam-nameopt closFun)])
                (if (lam? closFun)
                  (eval-under-env 
                        (lam-body closFun) 
                        (extendEnvNoEval (lam-formal closFun) actualParams
                          (extendEnvNoEval (lam-nameopt closFun) funClosure (closure-env funClosure))))
                        
                  (error "Closure's function isn't a function")))
              (error "Function doesn't return closure!")))]
        


[(letrec? e)
          (let* (
            [s1 (letrec-s1 e)]
            [s2 (letrec-s2 e)]
            [e1 (letrec-e1 e)]
            [e2 (letrec-e2 e)])
          (eval-under-env (letrec-e3 e)
                (extendEnvNoEval s2 (lam null null e2)
                  (extendEnvNoEval  s1 (lam null null e1) env))))]


 [(letrec? e)
          (let* (
            [s1 (letrec-s1 e)]
            [s2 (letrec-s2 e)]
            [e1 (letrec-e1 e)]
            [e2 (letrec-e2 e)]
            [semiEnv
                (extendEnv
                  (extendEnv 
                    (extendEnvNoEval s2 e2
                      (extendEnvNoEval s1 e1 env))
                    s2 e2)
                  s1 e1)])
          (eval-under-env (letrec-e3 e)
                (extendEnv semiEnv s2 e2)))]
 
 [(letrec? e)
          (let* (
            [s1 (letrec-s1 e)]
            [s2 (letrec-s2 e)]
            [e1 (letrec-e1 e)]
            [e2 (letrec-e2 e)]
            [semiEnv
                (extendEnv
                  (extendEnv 
                    (extendEnvNoEval s2 e2
                      (extendEnvNoEval s1 e1 env))
                    s2 e2)
                  s1 e1)])
          (eval-under-env (letrec-e3 e)
                (extendEnv semiEnv s2 e2)))]
 
 [(letrec? e)
          (eval-under-env (letrec-e3 e)
            (extendEnv
                 (extendEnv 
                    (extendEnvNoEval (letrec-s2 e) (letrec-e2 e)
                      (extendEnvNoEval (letrec-s1 e) (letrec-e1 e) env))
                    (letrec-s2 e) (letrec-e2 e))
                  (letrec-s1 e) (letrec-e1 e)))] #|
 
 #| [(letrec? e)
          (eval-under-env (letrec-e3 e)
            (extendEnv
                 (extendEnv 
                    (extendEnvNoEval (letrec-s2 e) (letrec-e2 e)
                      (extendEnvNoEval (letrec-s1 e) (letrec-e1 e) env))
                    (letrec-s2 e) (letrec-e2 e))
                  (letrec-s1 e) (letrec-e1 e)))] |#

#|  [(letrec? e)
          (eval-under-env (letrec-e3 e)
            (extendEnvNoEval (letrec-s2 e) (letrec-e2 e)
                    (extendEnvNoEval (letrec-s1 e) (letrec-e1 e))))]
 |#


#|  [(record? e)
         (let ([sk (eval-under-env (record-k e) env)]
               [rm (eval-under-env (record-rm e) env)])
            (if (key? sk)
              (if (or (ismunit? rm)
                      (record? rm))
                  (record sk rm)
                  (error ("Bad record")))
              (error "improper key")))]
 |#

#| (define numex-all-gt
  (with "filter" numex-filter
    (lam null "i"
     #|  (apply 
          (var "filter")
          (lam null "x"
              (ifleq (var "i") (var "x") null (var "x")))) |#
)))
 |#

#| (define numex-filter
  (lam "outer" "fun"
    (lam "map" "list"
        (ifmunit (var "list") 
                  (munit)
                  (apair 
                      (apply (var "fun") (1st (var "list"))) 
                      (apply (var "map") (2nd (var "list")))))
)))
 |#
#| (define numex-filter
  (lam "outer" "fun"
    (lam "map" "list"
        (let* ([newFun (lam "newFun" "mapp" 
                            (ifmunit (var "list") 
                                (munit)
                                (apply (var "mapp") (var "list"))))])
          (apair 
              (apply (var "fun") (1st (var "list"))) 
              (apply newFun (2nd (var "list")))))
)))
 |#

#| (define numex-filter
  (lam "outer" "fun"
    (lam "map" "list"
        (ifmunit (var "list") 
                  (munit)
                  (apair 
                      (apply (var "fun") (1st (var "list"))) 
                      (apply (var "map") (2nd (var "list")))))
))) |#

#| (define (EQUALdifferentBools e1 e2)
  (cond [(and (bool? e1) (bool? e2)) (eq? (bool-boolean e1) (bool-boolean e2))]
        [(and (ismunit? e1) (ismunit? e2)) (eq? (munit? (ismunit-e1 e1)) (munit? (ismunit-e1 e2)))]
        [(and (ismunit? e1) (bool? e2)) (eq? (munit? (ismunit-e1 e1)) (bool-boolean e2))]
        [(and (bool? e1) (ismunit? e2)) (eq? (bool-boolean e1) (munit? (ismunit-e1 e2)))]  
        [#t (error "Insane?")]
)) |#


(#| define (ifneq e1 e2 e3 e4)
   (let ([v1 e1]
         [v2 e2])
    (if (and (num? v1)
             (num? v2))
        (if (eq?  (num-int v1)
                  (num-int v2))
                  e4
                  e3)
        (if (EQUALdifferentBools v1 v2)
            e4
            e3)
)))
 |#
 



#| 
 [(with? e)
         (define name (with-s e))
         (let ([v1 (eval-under-env (with-e1 e) env)])
           (eval-under-env (with-e2 e) (extendEnvNoEval name v1 env)))]
           ;(cons (cons name v1) env)
        

[(apply? e)
        (let* ([funClosure (eval-under-env (apply-funexp e) env)]
                [actualResult (eval-under-env (apply-actual e) env)])
            (if (closure? funClosure)
              (let* ([closFun (closure-f funClosure)]
                    [funName (lam-nameopt closFun)])
                (if (lam? closFun)
                  (eval-under-env 
                        (lam-body closFun) 
                        (cons (cons (lam-formal closFun) actualResult)
                        (cons (cons (lam-nameopt closFun) funClosure) (closure-env funClosure))))
                  (error "Closure's function isn't a function")))
              (error "Function doesn't return closure!")))]


#| (define (ifneq e1 e2 e3 e4) |#
  (if (num? e1)
        (if (num? e2)
              (if (eq? (num-int e1) (num-int e2))
                    e4
                    e3) 
              (error "Mismatched types"))
        (if (bool? e1)
            (if (bool? e2)
                (if (eq? (bool-boolean e1) (bool-boolean e2))
                    e4
                    e3)
                (error "Mismatched types"))
              (error "Neither an int nor a boolean")))
) |#
#| [(with? e)
          (eval-under-env (with-e2 e) (extendEnv env (with-s e) (with-e1 e)))]
 |#
 #| [(apply? e)
          (let ([funClosure (eval-under-env (apply-funexp e) env)])
            (cond
              [(closure? funClosure) (let ([functionDeclaration (closure-f funClosure)])
                                       (let ([evaluatedActual (eval-under-env (apply-actual e) env)])
                                         (eval-under-env (lam-body functionDeclaration) (cons (cons (lam-formal functionDeclaration) evaluatedActual)
                                                                                          (cons (cons (lam-nameopt functionDeclaration) funClosure) (closure-env funClosure))))))]
              [true (error (format "Dude! numex Pass a closure in call!"))]))]   |#
        ; ?!



#| (define numex-all-gt
  (with "filter" numex-filter
        (lam null "gt"
            (lam "inner" "nlist"
                (apply 
                  (apply numex-filter
                      (lam "gt" "x"
                          (ifleq (var "i") (var "x") null (var "x"))))
                  (var "nlist"))))))
 |#


#| [(apply? e)
          (let([v1 (eval-under-env (apply-e1 e) env)])
           (if (closure? v1)
                ))]  |#
  #|  [(with? e)
          (eval-under-env (with-e2 e) (append env (cons (cons with-s (eval-under-env (with-e1 e) env)) null)))] |#

          #| (if (or [(ismunit? rm) (record sk rm)]
                    [(record? rm) rec]
                    [#t (error "Wrong value for record")])
              (error "Wrong key for record")))] |#

  #|   (define (recr nlist)
        (let (
          [frst (1st nlist)]
        )
        (if (ismunit nlist)
            nlist
            (if (apair? nlist)
                (let ([firstApplied (f frst)])
                  (if (num? firstApplied)
                      (if (zero? (num-int firstApplied))
                              (recr (2nd nlist)))
                              (apair firstApplied (recr (2nd nlist)))
                      (error "Non-number return value!")))
                (error "The list should be either a pair or an Munit"))))
    
  ) recr)
  da
) |#