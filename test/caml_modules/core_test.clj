(ns caml-modules.core-test
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
