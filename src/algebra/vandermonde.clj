;; Copyright Copyright © 2017 Colin Smith. MIT License.

(ns algebra.vandermonde
  (:require [algebra :as a]
            [algebra.polynomial :as p]))

;; thoughts: instead of calling functions in p/, we should
;; be doing a/ operations on elements of R[x]. We can form
;; R[x] from R. But where does the scale operation fit?
;; R[x] is an R-module as well as being a ring, for this
;; reason....

(defn solve
  "SolveVandermonde (p. 212 in Zippel: Effective Polynomial Computation)"
  [R ks ws]
  (assert (= (count ks) (count ws)))
  (assert (> (count ks) 0))
  (let [->binomial #(p/make 1 [[[1] (a/multiplicative-identity R)]
                               [[0] (a/negate R %1)]])
        n (count ks)
        kbs (map ->binomial ks)
        Q (reduce p/mul kbs)
        Qi (map #(first (p/divide Q %)) kbs)
        Pi (mapv #(p/scale %1 (a/reciprocal R (p/evaluate %1 [%2]))) Qi ks)]
    (loop [i 0
           x (vec (repeat n (a/additive-identity R)))]
      (if (= i n)
        x
        (recur
         (inc i)
         (map-indexed
          (fn [j xj]
            (a/add R xj (a/mul R (nth ws i) (p/coef (nth Pi i) [j])))
            )
          x))))))
