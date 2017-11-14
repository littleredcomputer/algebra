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
              (gen/such-that
               (fn [v] (= (count v) (count (distinct v))))
               (gen/vector gen/ratio %))
              (gen/vector gen/ratio %))))

(def ^:private Rx (p/PolynomialRing a/NativeArithmetic 1))

(defspec vandermonde-solution 25
  (prop/for-all [[ks ws] gen-vandermonde-test-case]
                ;; The vandermonde solver computes a vector of polynomial
                ;; coefficients. The polynomial built from those coefficients
                ;; should map corresponding ks to ws
                (let [p (p/make-dense Rx (solve a/NativeArithmetic ks ws))]
                  (every? true? (map #(= (p/evaluate p [%1]) %2) ks ws)))))
