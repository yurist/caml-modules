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
  (is (= (evl ex2n) (push-neg RW ex2n))))
