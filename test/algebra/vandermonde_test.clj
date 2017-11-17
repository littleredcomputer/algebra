;; Copyright © 2017 Colin Smith. MIT License.

(ns algebra.vandermonde-test
  (:require [clojure.test :refer :all]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [algebra.vandermonde :refer :all]
            [algebra.polynomial :as p]
            [algebra :as a]))

(def gen-vandermonde-test-case
  (gen/bind (gen/fmap inc gen/nat)
            #(gen/tuple
              (gen/vector-distinct gen/ratio {:num-elements %})
              (gen/vector gen/ratio %))))

(def ^:private Rx (p/PolynomialRing a/NativeArithmetic 1))

(defspec vandermonde-solution 30
  (prop/for-all [[ks ws] gen-vandermonde-test-case]
                ;; The vandermonde solver computes a vector of polynomial
                ;; coefficients. The polynomial built from those coefficients
                ;; should map corresponding ks to ws (See Eq. 13.4 in Zippel)
                (let [p (p/make-unary Rx (solve a/NativeArithmetic ks ws))]
                  (every? true? (map #(= (p/evaluate p [%1]) %2) ks ws)))))

(defspec transposed-vandermonde-solution 30
  (prop/for-all [[ks ws] gen-vandermonde-test-case]
                ;; See Eq. 13.7 in Zippel
                (let [R a/NativeArithmetic
                      xs (solve a/NativeArithmetic ks ws :transposed true)
                      n (count xs)]
                  (every? true?
                          (for [e (range n)]
                            (= (nth ws e)
                               (reduce (partial a/add R)
                                       (for [i (range n)]
                                         (a/mul R (a/exponentiation-by-squaring R (nth ks i) e) (nth xs i))))))))))
