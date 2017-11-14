;; Copyright Copyright © 2017 Colin Smith. MIT License.

(ns algebra.vandermonde
  (:require [algebra :as a]
            [algebra.polynomial :as p]))

(defn solve
  "SolveVandermonde (p. 212 in Zippel: Effective Polynomial Computation)"
  [R ks ws]
  (assert (= (count ks) (count ws)))
  (assert (> (count ks) 0))
  (let [Rx (p/PolynomialRing R 1)
        ->binomial #(p/make-unary Rx [(a/negate R %1)
                                      (a/multiplicative-identity R)])
        n (count ks)
        kbs (map ->binomial ks)
        Q (reduce (partial a/mul Rx) kbs)
        Qi (map #(first (a/quorem Rx Q %)) kbs)
        Pi (mapv #(a/scale Rx (a/reciprocal R (p/evaluate %1 [%2])) %1) Qi ks)]
    (loop [i 0
           x (vec (repeat n (a/additive-identity R)))]
      (if (= i n)
        x
        (recur (inc i)
               (map-indexed
                (fn [j xj]
                  (a/add R xj (a/mul R (nth ws i) (p/coef (nth Pi i) [j]))))
                x))))))
