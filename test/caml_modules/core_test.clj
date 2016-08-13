(ns caml-modules.core-test
  (:require [clojure.test :refer :all]
            [caml-modules.core :refer :all]
            [clojure.core.match :refer [match]]))

(def A (struct
        (:let x 5)))

(def B (struct
        (:include A)))

(def C (struct
        (:let f (fn [x] (inc x)))))

(def D
  (let [E (struct
           (:let e1 10))
        F (struct
           #_(:include E e1)
           (:open E e1)
           (:let f (inc e1)))]
    F))

(def S
  (sig s1 s2))

(def T
  (struct
   (:let s1 1)
   (:let s2 2)
   (:let s3 3)))

#_(>< D S)

(>< T S)

($ D f)

(def Q
  (struct
   (:let f1 (fn [x] (inc x)))
   (:let c 3)))

(reify-funs f1)
(reify-syms c)

(run-in Q (f1 5))
(run-in Q (f1 c))
(run-in Q c)

(def M
  (struct
   (:let c1 5)
   (:let f1 inc)))

(def N
  (struct
   (:include M)
   (:open M)
   (:let c1 (inc c1))))

(reify-funs f1)
(reify-syms c1)

(run-in N (f1 c1))
(run-in M (f1 c1))
