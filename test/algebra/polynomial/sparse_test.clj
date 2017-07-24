(ns algebra.polynomial.sparse-test
  (:require [clojure.test :refer :all]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [algebra.polynomial :as p]
            [algebra.polynomial.sparse :refer :all]
            [algebra.polynomial.sparse :as ps]
            [algebra :as a]
            [criterium.core :as c]
            )
  (:import (algebra.polynomial Polynomial)))

(deftest sparse-evaluation
  (is (= 8 (shnf-eval a/NativeArithmetic [::ps/pow 3 1 0] [2])))
  (is (= 9 (shnf-eval a/NativeArithmetic [::ps/pow 3 1 1] [2])))
  (is (= 16 (shnf-eval a/NativeArithmetic [::ps/pow 3 2 0] [2])))
  (is (= 17 (shnf-eval a/NativeArithmetic [::ps/pow 3 2 1] [2])))
  (is (= 7 (shnf-eval a/NativeArithmetic [::ps/pop 1
                                          [::ps/pow 1 1 0]] [6 7 8])))
  (is (= 8 (shnf-eval a/NativeArithmetic [::ps/pop 2
                                          [::ps/pow 1 1 0]] [6 7 8])))
  (is (= 16 (shnf-eval a/NativeArithmetic [::ps/pop 1 [::ps/pow 2 4 0]] [1 2 3])))
  (is (= 186 (shnf-eval a/NativeArithmetic
                        [::ps/pow 3
                         [::ps/pow 1
                          [::ps/pop 1
                           [::ps/pow 2 4 0]]
                          3]
                         [::ps/pop 1
                          [::ps/pow 4 2 5]]]
                        [1 2 3])))

  (is (= 1 (->shnf (p/make [1]))))
  (is (= 99 (->shnf (p/make [99]))))
  (is (= [::ps/pow 1 1 0] (->shnf (p/make [0 1]))))
  (is (= [::ps/pow 2 1 0] (->shnf (p/make [0 0 1]))))
  (is (= [::ps/pow 1 [::ps/pow 1 1 1] 0] (->shnf (p/make [0 1 1]))))
  (is (= [::ps/pow 1 [::ps/pow 1 1 1] 1] (->shnf (p/make [1 1 1]))))
  (let [[k x y z] (p/basis a/NativeArithmetic 3)
        R (p/make a/NativeArithmetic 3 [[[4 2 0] 4]
                                        [[3 0 0] 3]
                                        [[0 0 4] 2]
                                        [[0 0 0] 5]])
        Rx (->shnf R)]
    (is (= [::ps/pow 3 [::ps/pow 1 [::ps/pop 1 [::ps/pow 2 4 0]] 3] [::ps/pop 1 [::ps/pow 4 2 5]]] Rx))
    (is (= 186 (shnf-eval a/NativeArithmetic Rx [1 2 3])))))

(defn generate-poly
  ([generator]
   (gen/bind
     (gen/sized #(gen/choose 1 (inc %)))
     (fn [arity]
       (generate-poly generator arity))))
  ([generator arity]
   (gen/fmap #(p/make arity %)
             (gen/vector
               (gen/tuple
                 (gen/vector gen/pos-int arity)
                 generator)))))

(defn ^:private shnf-evaluate
  [p xs]
  (shnf-eval a/NativeArithmetic (->shnf p) xs))

(defspec evaluation-homomorphism 50
  (gen/let [arity (gen/choose 1 6)]
    (prop/for-all [p (generate-poly gen/int arity)
                   q (generate-poly gen/int arity)
                   xs (gen/vector gen/int arity)]
                  (= (*' (shnf-evaluate p xs) (shnf-evaluate q xs))
                     (shnf-evaluate (p/mul p q) xs)))))

(defspec naive-and-shnf-evaluation-agree 25
  (gen/let [arity (gen/choose 1 10)]
    (prop/for-all [p (generate-poly gen/int arity)
                   xs (gen/vector gen/int arity)]
                  (= (p/evaluate p xs) (shnf-evaluate p xs)))))

(defn -main
  [& args]
  (let [pxs (doall
              (gen/sample
                (gen/bind (gen/choose 8 9)
                          #(gen/tuple (generate-poly gen/int %)
                                      (gen/vector gen/int %)))
                256))
        shfxs (mapv #(vector (->shnf (first %)) (second %)) pxs)]
    (println "begin")
    (c/quick-bench (dorun (for [[p x] pxs] (shnf-evaluate p x))))
    (c/quick-bench (dorun (for [[p x] pxs] (p/evaluate p x))))
    (c/quick-bench (dorun (for [[s x] shfxs] (shnf-eval a/NativeArithmetic s x))))))
