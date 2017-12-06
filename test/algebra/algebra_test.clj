;; Copyright © 2017 Colin Smith. MIT License.

(ns algebra.algebra-test
  (:require [clojure.test :refer :all]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [algebra :as a]))

(deftest basics
  (let [R a/Z]
    (is (= 9 (a/exponentiation-by-squaring R 3 2)))
    (is (= 8 (a/exponentiation-by-squaring R 2 3)))
    (is (= 2 (a/euclid-gcd R 8 6)))
    (is (= 2 (a/euclid-gcd-seq R [8 6])))
    (is (= 8 (a/euclid-gcd-seq R [8])))
    (is (= [7 2 -7] (a/extended-euclid R 126 35)))
    (is (= 37 (a/chinese-remainder R [1 1 2] [2 3 5])))
    (is (= 63 (a/chinese-remainder R [0 11] [3 26])))))

(defspec gcd
  (let [R a/Z]
    (prop/for-all [u (gen/such-that (complement zero?) gen/nat)
                   v (gen/such-that (complement zero?) gen/int)]
                  (let [g (a/euclid-gcd R u v)]
                    (and (a/evenly-divides? R g u)
                         (a/evenly-divides? R g v))))))

(defspec extended-euclid
  (let [R a/Z]
    (prop/for-all [u gen/int
                   v gen/int]
                  (let [[g s t] (a/extended-euclid R u v)]
                    (and (or (a/additive-identity? R g)
                             (and (a/evenly-divides? R g u)
                                  (a/evenly-divides? R g v)))
                         (or (a/additive-identity? R u)
                             (a/additive-identity? R v)
                             (not (a/additive-identity? R g)))
                         (= g (a/add R (a/mul R s u) (a/mul R t v))))))))

(defspec expt
  (let [R a/Z]
    (prop/for-all [u gen/int
                   e gen/pos-int]
                  (is (= (a/exponentiation-by-squaring R u e)
                         (reduce #(a/mul R %1 %2) (a/multiplicative-identity R) (repeat e u)))))))

(defspec nontrivial-gcd
  (let [R a/Z]
    (prop/for-all [k (gen/such-that (complement zero?) gen/nat)
                   u (gen/such-that (complement zero?) gen/nat)
                   v (gen/such-that (complement zero?) gen/int)]
                  (let [ku (* k u)
                        kv (* k v)
                        g (a/euclid-gcd R ku kv)]
                    (and (a/evenly-divides? R g ku)
                         (a/evenly-divides? R g kv)
                         (a/evenly-divides? R k g))))))

(defspec gcd-seq
  (let [R a/Z]
    (prop/for-all [as (gen/not-empty (gen/vector (gen/such-that (complement zero?) gen/int)))]
                  (let [g (a/euclid-gcd-seq R as)]
                    (every? #(a/evenly-divides? R g %) as)))))

(defspec nontrival-gcd-seq
  (let [R a/Z]
    (prop/for-all [k-as (gen/let [k gen/s-pos-int
                                  as (gen/not-empty
                                      (gen/vector
                                       (gen/fmap #(* k %)
                                                 (gen/such-that (complement zero?) gen/int))))]

                          [k as])]
                  (let [[k as] k-as
                        g (a/euclid-gcd-seq R as)]
                    (and
                     (a/evenly-divides? R k g)
                     (every? #(a/evenly-divides? R g %) as))))))
