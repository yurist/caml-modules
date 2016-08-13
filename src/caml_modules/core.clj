(ns caml-modules.core)

(defmacro struct
  "Creates a struct from a list of directives.
  Possible directives:
  :include expr symbols?
  :open expr symbols?
  :let symbol value"
  [& dirs]
  (let [go (fn [exps locs dirs]
             (let [[dir & dirs] dirs]
               (if-not dir
                 [exps locs]

                 (let [[op & opers] dir

                       [exps locs]
                       (case op
                         :let
                         (let [[sym ops] opers
                               symops [sym ops]]
                           [(conj exps symops) (conj locs symops)])

                         (:open :include)
                         (let [[e & syms] opers
                               syms (or syms
                                        (keys (:exports (eval e))))
                               exp (gensym "exp")
                               locs (conj locs [exp `(:exports ~e)])
                               symops (map (fn [sym] [sym `(~exp '~sym)]) syms)
                               locs (vec (concat locs symops))
                               exps (if (= op :include)
                                      (vec (concat exps symops))
                                      exps)]
                           [exps locs]))]

                   (recur exps locs dirs)))))

        [exps locs] (go [] [] dirs)
        qify (fn [xs] (vec (map (fn [[k _]] `['~k ~k]) xs)))
        qexps (qify exps)
        qlocs (qify locs)]

    `(let [~@(mapcat identity locs)]
       {:exports
        ~(into {} qexps)
        :locals
        ~(into {} qlocs)})))

(def sig* vector)

(defmacro sig [& syms]
  (let [qsyms (map (fn [s] `'~s) syms)]
    `(sig* ~@qsyms)))

(defn >< [struct sig]
  (let [s-keyset (into #{} (keys (:exports struct)))
        missing (remove s-keyset sig)]
    (if (seq missing)
      (throw (Exception. (str "Missing exports " (vec missing))))
      {:locals (:locals struct)
       :exports (into {}
                      (for [k sig] [k ((:exports struct) k)]))})))

(defn $* [struct sym]
  ((:exports struct) sym))

(defmacro $ [struct sym]
  `($* ~struct '~sym))

(defrecord FrozenFun [icicle])

(defrecord FrozenSym [icicle])

(defn freeze-fun [fsym & args]
  (->FrozenFun [fsym args]))

(defn freeze-sym [sym]
  (->FrozenSym sym))

(defmacro reify-funs [& syms]
  (let [defs (map (fn [sym] `(def ~sym (partial freeze-fun '~sym))) syms)]
    `(do ~@defs)))

(defmacro reify-syms [& syms]
  (let [defs (map (fn [sym] `(def ~sym (freeze-sym '~sym))) syms)]
    `(do ~@defs)))

(defn thaw [struct e]
  (let [locs (:locals struct)
        thaw' (partial thaw struct)]
    (cond
      (= (type e) FrozenFun)
      (let [{[fsym args] :icicle} e]
        (apply (locs fsym) (map thaw' args)))

      (= (type e) FrozenSym)
      (let [{sym :icicle} e]
        (locs sym))

      (fn? e)
      (fn [x] (thaw' (e x)))

      :else e)))

(def run-in thaw)
