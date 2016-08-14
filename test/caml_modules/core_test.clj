(ns caml-modules.core-test
  (:refer-clojure :exclude [struct])
  (:require [clojure.test :refer :all]
            [caml-modules.core :refer :all]
            [clojure.core.match :refer [match]]))

;;;;;;;;;;;;;;;;;;;; basic_gates.ml ;;;;;;;;;;;;;;;;;;;;;

(def SYM (sig
          lit
          neg
          an_
          or_
          observe))

(reify-funs lit neg an_ or_ observe)

(def ex1 (an_ (lit true) (neg (lit false))))

(def SYMW
  (concat SYM
          (sig
           wire-x
           wire-y
           wire-z)))

(reify-syms wire-x wire-y wire-z)

(def ex2 (an_ (lit true) (neg wire-x)))

(defn xor [x y]
  (an_ (or_ x y) (neg (an_ x y))))

(def exadd2 (xor wire-x wire-y))

(def exadd3 (xor (xor wire-x wire-y) wire-z))

(def exadd-xy1 (xor wire-x (xor wire-y (lit true))))

(def R (struct
        (:let lit identity)
        (:let neg not)
        (:letfn an_ [x y] (and x y))
        (:letfn or_ [x y] (or x y))
        (:let observe identity)))

(deftest r-test-1
  (is (true? (eval-in R ex1))))

(def RW (struct
         (:include R)
         (:let wire-x true)
         (:let wire-y false)
         (:let wire-z true)))

(deftest rw-tes-1
  (is (true? (eval-in RW exadd2))))

(defn evl [x] (eval-in RW (observe x)))

(def S0 (struct
         (:letfn paren [x] (str "(" x ")"))
         (:letfn lit [x] (if x "tt" "ff"))
         (:letfn neg [x] (str "~" x))
         (:letfn an_ [x y] (paren (str x " && " y)))
         (:letfn or_ [x y] (paren (str x " || " y)))
         (:let observe identity)))

(def SW0 (struct
          (:include S0)
          (:let wire-x "X")
          (:let wire-y "Y")
          (:let wire-z "Z")))

(deftest s0-test
  (is (= "((X || Y) && ~(X && Y))" (eval-in SW0 exadd2)))
  (is (= "((((X || Y) && ~(X && Y)) || Z) && ~(((X || Y) && ~(X && Y)) && Z))" (eval-in SW0 exadd3))))

(def S (struct
        (:letfn paren [c] (if c
                            (fn [x] (str "(" x ")"))
                            identity))
        (:letfn lit [x] (fn [_] (if x "tt" "ff")))
        (:letfn neg [x] (fn [p] ((paren (> p 10)) (str "~" (x 11)))))
        (:letfn an_ [x y] (fn [p] ((paren (> p 4)) (str (x 4) " && " (y 4)))))
        (:letfn or_ [x y] (fn [p] ((paren (> p 3)) (str (x 3) " || " (y 3)))))
        (:letfn observe [x] (x 0))))

(def SW (struct
         (:include S)
         (:let wire-x (constantly "X"))
         (:let wire-y (constantly "Y"))
         (:let wire-z (constantly "Z"))))

(defn view [x] (eval-in SW (observe x)))

(deftest view-test-1
  (is (= "((X || Y) && ~(X && Y) || Z) && ~((X || Y) && ~(X && Y) && Z)" (view exadd3))))

;;;;;;;;;;;;;;;;; end of basic_gates.ml ;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;; bneg_adhoc.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn TNegDown [I]
  (let [I (>< I SYM)]
    (struct
     (:letfn lit [x] (fn [ctx] (case ctx
                                :pos (($ I lit) x)
                                :neg (($ I lit) (not x)))))
     (:letfn neg [e] (fn [ctx] (case ctx
                                :pos (e :neg)
                                :neg (e :pos))))
     (:letfn an_ [e1 e2] (fn [ctx] (case ctx
                                    :pos (($ I an_) (e1 :pos) (e2 :pos))
                                    :neg (($ I or_) (e1 :neg) (e2 :neg)))))
     (:letfn or_ [e1 e2] (fn [ctx] (case ctx
                                    :pos (($ I or_) (e1 :pos) (e2 :pos))
                                    :neg (($ I an_) (e1 :neg) (e2 :neg)))))
     (:letfn observe [x] (($ I observe) (x :pos))))))

(defn TNegDownW [I]
  (let [I (>< I SYMW)]
    (struct
     (:include (TNegDown I) SYM)
     (:let wire-x (fn [ctx] (case ctx
                             :pos ($ I wire-x)
                             :neg (($ I neg) ($ I wire-x)))))
     (:let wire-y (fn [ctx] (case ctx
                             :pos ($ I wire-y)
                             :neg (($ I neg) ($ I wire-y)))))
     (:let wire-z (fn [ctx] (case ctx
                             :pos ($ I wire-z)
                             :neg (($ I neg) ($ I wire-z))))))))

(defn push-neg [I x] (eval-in (TNegDownW I) (observe x)))

(def ex2n (neg (an_ (lit true) (neg wire-x))))

(deftest neg-down-test
  (is (= (evl ex2n) (push-neg RW ex2n)))
  (is (= "~(tt && ~X)" (view ex2n)))
  (is (= "ff || X" (push-neg SW ex2n)))
  (is (= "(X || Y) && ~(X && Y)" (view exadd2)))
  (is (= "(X || Y) && (~X || ~Y)" (push-neg SW exadd2)))
  (is (= "((X || Y) && ~(X && Y) || Z) && ~((X || Y) && ~(X && Y) && Z)" (view exadd3)))
  (is (= "((X || Y) && (~X || ~Y) || Z) && (~X && ~Y || X && Y || ~Z)" (push-neg SW exadd3))))

;;;;;;;;;;;;;;;;;;;;;;;; end of bneg_adhoc.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;; bconst_prop.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn T0 [I]
  (let [I (>< I SYM)]
    (struct
     (:let lit ($ I lit))
     (:let neg ($ I neg))
     (:let an_ ($ I an_))
     (:let or_ ($ I or_))
     (:let observe ($ I observe)))))

(defn T0W [I]
  (let [I (>< I SYMW)]
    (struct
     (:include (T0 I) SYMW)
     (:let wire-x ($ I wire-x))
     (:let wire-y ($ I wire-y))
     (:let wire-z ($ I wire-z)))))

(deftest t0-test
  (is (= (eval-in (T0W SW) (observe exadd3)) (view exadd3))))

(defn TCP [I]
  (let [I (>< I SYM)]
    (struct
     (:letfn dyn [x] (match x
                            {:unk e} e
                            {:lit e} (($ I lit) e)))
     (:letfn lit [x] {:lit x})
     (:letfn neg [x] (match x
                            {:unk e} {:unk (($ I neg) e)}
                            {:lit e} {:lit (not e)}))
     (:letfn an_ [x y](match [x y]
                             [{:lit true} e] e
                             [e {:lit true}] e
                             [{:lit false} e] {:lit false}
                             [e {:lit false}] {:lit false}
                             [{:unk e1} {:unk e2}] {:unk (($ I an_) e1 e2)}))
     (:letfn or_ [x y](match [x y]
                             [{:lit true} e] {:lit true}
                             [e {:lit true}] {:lit true}
                             [{:lit false} e] e
                             [e {:lit false}] e
                             [{:unk e1} {:unk e2}] {:unk (($ I or_) e1 e2)}))
     (:letfn observe [x] (($ I observe) (dyn x))))))

(defn TCPW [I]
  (let [I (>< I SYMW)]
    (struct
     (:include (TCP I) SYMW)
     (:let wire-x {:unk ($ I wire-x)})
     (:let wire-y {:unk ($ I wire-y)})
     (:let wire-z {:unk ($ I wire-z)}))))

(defn obscp [I x] (eval-in (TCPW I) (observe x)))

(deftest tcp-test
  (is (= (evl exadd-xy1) (obscp RW exadd-xy1)))
  (is (= "(X || (Y || tt) && ~(Y && tt)) && ~(X && (Y || tt) && ~(Y && tt))" (view exadd-xy1)))
  (is (= "(X || ~Y) && ~(X && ~Y)" (obscp SW exadd-xy1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;; end of bconst_prop.ml ;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;; rr.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def TransBase
  (sig
   fwd
   bwd))

(def Trans
  (concat TransBase
          (sig
           map1
           map2)))

(defn TransDef [X]
  (let [X (>< X TransBase)]
    (struct
     (:open X TransBase)
     (:letfn map1 [f t] (fwd (f (bwd t))))
     (:letfn map2 [f t1 t2] (fwd (f (bwd t1) (bwd t2)))))))

(defn SYMT [X F]
  (let [X (>< X Trans)
        F (>< F SYM)]
    (struct
     (:open X Trans)
     (:let lit (comp fwd ($ F lit)))
     (:let neg (partial map1 ($ F neg)))
     (:let an_ (partial map2 ($ F an_)))
     (:let or_ (partial map2 ($ F or_)))
     (:let observe (comp ($ F observe) bwd)))))

(defn SYMTW [X F]
  (let [X (>< X Trans)
        F (>< F SYMW)]
    (struct
     (:include (SYMT X F) SYM)
     (:let wire-x (($ X fwd) ($ F wire-x)))
     (:let wire-y (($ X fwd) ($ F wire-y)))
     (:let wire-z (($ X fwd) ($ F wire-z))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;; end of rr.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;; bneg_double.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn DN2N [F]
  (let [F (>< F SYM)]
    (struct
     (:let X (struct
              (:letfn fwd [x] {:unk x})
              (:letfn bwd [x] (match x
                                     {:unk e} e
                                     {:neg e} (($ F neg) e)))))
     (:include X TransBase)
     (:include (TransDef X) [map1 map2])
     (:let IDelta (struct
                   (:letfn neg [x] (match x
                                          {:unk e} {:neg e}
                                          {:neg e} {:unk e})))))))

(defn PN2NW [F]
  (let [F (>< F SYMW)]
    (struct
     (:let OptM (DN2N F))
     (:include (SYMTW OptM F) SYMW)
     (:include ($ OptM IDelta) [neg]))))

(defn obsn2n [F x] (eval-in (PN2NW F) (observe x)))

(def exnn (neg (neg (an_ (neg (neg wire-x)) wire-y))))

(deftest n2n-test
  (is (= "~(~(~(~X) && Y))" (view exnn)))
  (is (= "X && Y" (obsn2n SW exnn)))
  (is (= "(X || (Y || tt) && ~(Y && tt)) && ~(X && (Y || tt) && ~(Y && tt))" (view exadd-xy1)))
  (is (= "(X || (Y || tt) && ~(Y && tt)) && ~(X && (Y || tt) && ~(Y && tt))" (obsn2n SW exadd-xy1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;; end of bneg_double.ml ;;;;;;;;;;;;;;;;;;;;;;;;

(def FR (struct
         (:let lit (partial freeze-fun 'lit))
         (:let neg (partial freeze-fun 'neg))
         (:let an_ (partial freeze-fun 'an_))
         (:let or_ (partial freeze-fun 'or_))
         (:let observe identity)))

(def FRW (struct
          (:include FR)
          (:let wire-x (freeze-sym 'wire-x))
          (:let wire-y (freeze-sym 'wire-y))
          (:let wire-z (freeze-sym 'wire-z))))

(deftest fr-test
  (is (= (view (obsn2n FRW exnn)) (obsn2n SW exnn)))
  (is (= (view (obsn2n FRW exadd-xy1)) (obsn2n SW exadd-xy1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; bneg_down.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn flip-conn [x]
  (case x
    :cand :cor
    :cor :cand))

(defn DNDown [F]
  (let [F (>< F SYM)]
    (struct
     (:let X (struct
              (:letfn fwd [x] {:unk x})
              (:letfn bwd [x] (match x
                                     {:unk e} e
                                     {:con [:cand e1 e2]} (($ F an_) e1 e2)
                                     {:con [:cor e1 e2]} (($ F or_) e1 e2)))))
     (:include X [fwd bwd])
     (:include (TransDef X) [map1 map2])
     (:let IDelta (struct
                   (:letfn neg [x]
                           (match x
                                  {:unk e}
                                  {:unk (($ F neg) e)}
                                  
                                  {:con [c e1 e2]}
                                  {:con [(flip-conn c) (($ F neg) e1) (($ F neg) e2) ]}))
                   (:letfn an_ [e1 e2] {:con [:cand (bwd e1) (bwd e2)]})
                   (:letfn or_ [e1 e2] {:con [:cor (bwd e1) (bwd e2)]}))))))

(defn PNDownW [F]
  (let [F (>< F SYMW)]
    (struct
     (:let OptM (DNDown F))
     (:include (SYMTW OptM F) SYMW)
     (:include ($ OptM IDelta) [neg an_ or_]))))

(defn obsndown [F x] (eval-in (PNDownW F) (observe x)))

(deftest ndown-test
  (is (= "~(~(~(~X) && Y))" (view exnn)))
  (is (= "~(~(~(~X))) && ~(~Y)" (obsndown SW exnn)))
  (is (= "~(~(~(~X))) && ~(~Y)" (eval-in (PNDownW (PNDownW SW)) (observe exnn))))
  (is (= "(X || (Y || tt) && (~Y || ~tt)) && (~X || ~((Y || tt) && (~Y || ~tt)))" (obsndown SW exadd-xy1)))
  (is (= "(X || (Y || tt) && (~Y || ~tt)) && (~X || ~(Y || tt) || ~(~Y || ~tt))" (eval-in (PNDownW (PNDownW SW)) (observe exadd-xy1))))
  (is (= "(X || (Y || tt) && (~Y || ~tt)) && (~X || ~Y && ~tt || ~(~Y) && ~(~tt))" (eval-in (PNDownW (PNDownW (PNDownW SW))) (observe exadd-xy1))))
  (is (= "(X || ~Y) && (~X || ~(~Y))" (eval-in (TCPW (PNDownW (PNDownW (PNDownW SW)))) (observe exadd-xy1))))
  (is (= "(X || ~Y) && (~X || Y)" (eval-in (TCPW (PNDownW (PNDownW (PNDownW (PN2NW SW))))) (observe exadd-xy1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; end of bneg_down.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; hgates.ml ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def SYMHO (concat SYM
                   (sig
                    lam
                    app)))

(reify-funs lam app)

(defn applies [f & args]
  (loop [f f args args]
    (if (seq args)
      (recur (f (first args)) (rest args))
      f)))

(defn >> [& args]
  (apply applies args))

(defn apps [f & args]
  (loop [f f args args]
    (if (seq args)
      (recur (app  f (first args)) (rest args))
      f)))

(defn >a> [& args]
  (apply apps args))

(def ehadd3
  (lam (fn [x]
         (lam (fn [y]
                (lam (fn [z]
                       (xor (xor x y) z))))))))

(def ehadd3t
  (lam (fn [x]
         (lam (fn [y]
                (>a> ehadd3 x y (lit true)))))))

(def RHO (struct
          (:include R)
          (:let lam identity)
          (:letfn app [f x] (f x))))

(defn evalho [x]
  (eval-in RHO (observe x)))

(deftest evalho-test
  (is (true? (evalho ex1)))
  (is (false? (>> (evalho ehadd3) true false true)))
  (is (false? (>> (evalho ehadd3t) true false))))

(defn cc
  "Count occurences of c in s"
  [c s]
  (reduce #(if (= c %2) (inc %1) %1) 0 s))

(def SHO (struct
          (:include S)
          (:letfn app [f x] (fn [p] ((paren (> p 10)) (str (f 10) " " (x 11)))))
          (:let varnames "xyzuvw")
          (:letfn varname [i]
                  (if (< i (count varnames))
                    (nth varnames i)
                    (str "x" i)))
          (:letfn lam [f]
                  (let [body0 (observe (f (constantly "XXX")))
                        var (varname (cc \λ body0))]
                    (fn [p] ((paren (pos? p)) (str "λ" var "." (observe (f (constantly var))))))))))

(defn viewho [x]
  (eval-in SHO (observe x)))

(deftest viewho-test
  (is (= "λz.λy.λx.((z || y) && ~(z && y) || x) && ~((z || y) && ~(z && y) && x)" (viewho ehadd3)))
  (is (= "λv.λu.(λz.λy.λx.((z || y) && ~(z && y) || x) && ~((z || y) && ~(z && y) && x)) v u tt" (viewho ehadd3t))))

(defn TCPHO [I]
  (let [I (>< I SYMHO)]
    (struct
     (:include (TCP I) [dyn lit neg an_ or_ observe])
     (:letfn app [f x]
             (match f
                    {:unk f} {:unk (($ I app) f (dyn x))}))
     (:letfn lam [f] {:unk (($ I lam) (fn [x] (dyn (f {:unk x}))))}))))

(defn obscpho [I e]
  (eval-in (TCPHO I) (observe e)))

(def mex1 (lam (fn [x] (an_ x (lit false)))))

(deftest tcpho-test
  (is (= "λx.ff" (obscpho SHO mex1))))

(defn SYMTHO [X F]
  (let [X (>< X Trans)
        F (>< F SYMHO)]
    (struct
     (:open X Trans)
     (:include (SYMT X F) SYM)
     (:let app (partial map2 ($ F app)))
     (:letfn lam [f] (fwd (($ F lam) (fn [x] (bwd (f (fwd x))))))))))

(defn PN2NHO [F]
  (let [F (>< F SYMHO)]
    (struct
     (:let OptM (DN2N F))
     (:include (SYMTHO OptM F) SYMHO)
     (:include ($ OptM IDelta) [neg]))))

(obsn2n SW (neg (neg (lit true))))
(eval-in (PN2NHO SHO) (observe (neg (neg (lit true)))))
(eval-in (PN2NHO SHO) (observe (lam (fn [x] (neg (neg x))))))
(eval-in (PN2NHO SHO) (observe (lam (fn [x] (an_ (lit true) (neg (neg x)))))))
(eval-in (PN2NHO (TCPHO SHO)) (observe (lam (fn [x] (an_ (lit true) (neg (neg x)))))))

(defn PNDownHO [F]
  (let [F (>< F SYMHO)]
    (struct
     (:let OptM (DNDown F))
     (:include (SYMTHO OptM F) SYMHO)
     (:include ($ OptM IDelta) [neg an_ or_]))))

(eval-in (PNDownHO SHO) (observe (app (lam (fn [x] (lam (fn [y] (neg (an_ x y)))))) (lit true))))

(defn DStaticApp [F]
  (let [F (>< F SYMHO)]
    (struct
     (:let X (struct
              (:letfn fwd [x] {:unk x})
              (:let bwd (fn bwd [e] (match e
                                          {:unk x} x
                                          {:fun f} (($ F lam) (fn [x] (bwd (f (fwd x))))))))))
     (:include X [fwd bwd])
     (:include (TransDef X) [map1 map2])
     (:let IDelta (struct
                   (:letfn lam [f] {:fun f})
                   (:letfn app [f x]
                           (match f
                                  {:fun ff} (ff x)
                                  _ {:unk (($ F app) (bwd f) (bwd x))})))))))

(defn PStaticApp [F]
  (let [F (>< F SYMHO)]
    (struct
     (:let OptM (DStaticApp F))
     (:include (SYMTHO OptM F) SYMHO)
     (:include ($ OptM IDelta) [lam app]))))

(viewho ehadd3t);; => "λv.λu.(λz.λy.λx.((z || y) && ~(z && y) || x) && ~((z || y) && ~(z && y) && x)) v u tt"

(eval-in (PStaticApp SHO) (observe ehadd3t));; => "λy.λx.((y || x) && ~(y && x) || tt) && ~((y || x) && ~(y && x) && tt)"

(eval-in (PStaticApp (PNDownHO SHO)) (observe ehadd3t));; => "λy.λx.((y || x) && (~y || ~x) || tt) && (~((y || x) && (~y || ~x)) || ~tt)"


(eval-in (PStaticApp (TCPHO (PNDownHO SHO))) (observe ehadd3t));; => "λy.λx.~(y || x) || ~(~y || ~x)"
(eval-in (PStaticApp (TCPHO (PNDownHO (PNDownHO SHO)))) (observe ehadd3t))
;; => "λy.λx.~y && ~x || ~(~y) && ~(~x)"
(eval-in (PStaticApp (TCPHO (PNDownHO (PNDownHO (PN2NHO SHO))))) (observe ehadd3t))
;; => "λy.λx.~y && ~x || y && x"
