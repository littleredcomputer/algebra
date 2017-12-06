;; Copyright Copyright © 2017 Colin Smith. MIT License.

(ns algebra.vandermonde
  (:require [algebra :as a]
            [algebra.polynomial :as p]))

(defn solve
  "SolveVandermonde (p. 212 in Zippel: Effective Polynomial Computation)"
  [R ks ws & {:keys [transposed]}]
  (assert (= (count ks) (count ws)))
  (assert (> (count ks) 0))
  (let [Rx (p/PolynomialRing R 1)
        ->binomial #(p/make-unary Rx [(a/negate R %1)
                                      (a/multiplicative-identity R)])
        n (count ks)
        kbs (map ->binomial ks)
        Q (reduce (partial a/mul Rx) kbs)
        Qi (map #(first (a/quorem Rx Q %)) kbs)
        ;; If this is meant to work in Z, what operation would the
        ;; polynomial need to support? A down-scale with exact-division,
        ;; perhaps... is that a module operation? XXX
        Pi (mapv #(a/scale Rx (a/reciprocal R (p/evaluate %1 [%2])) %1) Qi ks)
        c #(p/coef (nth Pi %1) [%2])]
    (mapv
     (fn [i]
       (reduce (partial a/add R) (for [j (range n)] (a/mul R (nth ws j) (if transposed (c i j) (c j i))))))
     (range n))))
