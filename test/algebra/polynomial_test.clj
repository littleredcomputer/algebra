;; Copyright © 2017 Colin Smith. MIT License.

(ns algebra.polynomial-test
  (:require [clojure.test :refer :all]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [algebra.polynomial :refer :all]
            [clojure.walk :as walk]
            [algebra :as a])
  (:import (algebra.polynomial Polynomial)
           (algebra Ring Field)))

(deftest poly-core
  ; need to rethink this in light of the library separation
  ;(testing "kind"
  ;  (is (= :sicmutils.polynomial/polynomial (v/kind (make [])))))
  (testing "zero"
    (is (polynomial-zero? (make [])))
    (is (polynomial-zero? (make [0])))
    (is (polynomial-zero? (make [])))
    (is (polynomial-zero? (make 2 [])))
    (is (polynomial-zero? (make 2 [])))
    (is (not (polynomial-zero? (make [1])))))
  (testing "unity"
    (is (polynomial-one? (make [1])))
    (is (polynomial-one? (make 2 [[[0 0] 1]])))
    (is (polynomial-one? (make 3 [[[0 0 0] 1]])))
    (is (not (polynomial-one? (make 3 [[[0 0 0] 1] [[0 0 1] 2]]))))
    (is (not (polynomial-one? (make [1.1]))))
    (is (not (polynomial-one? (make [1.0]))))               ;; though maybe it should be
    (is (polynomial-one? (make (PolynomialRing a/NativeArithmetic 1) 1 [[[0] (make [1])]])))
    (is (not (polynomial-one? (make (PolynomialRing a/NativeArithmetic 1) 1 [[[0] (make [2])]])))))
  (testing "make-constant"
    (is (= (make [99]) (make-constant 1 99)))
    (is (= (make 2 [[[0 0] 88]]) (make-constant 2 88)))
    (is (= (make 3 [[[0 0 0] 77]]) (make-constant 3 77))))
  (testing "degree"
    (is (= (degree (make [])) -1))
    (is (= (degree (make [-1 1])) 1))
    (is (= (degree (make [0 1])) 1))
    (is (= (degree (make [-1 0 2])) 2))
    (is (= (degree (make [-1 2 0])) 1))
    (is (= (degree (make [0 0])) -1)))
  (testing "zero-like"
    (is (= (make []) (polynomial-zero-like (make [1 2 3]))))
    (is (= (make 2 []) (polynomial-zero-like (make 2 [[[1 0] 1] [[2 1] 3]]))))
    (is (= (make 3 []) (polynomial-zero-like (make 3 [[[1 2 1] 4] [[0 1 0] 5]])))))
  (testing "one-like"
    (is (= (make [1]) (polynomial-one-like (make [1 2 3]))))
    (is (= (make 2 [[[0 0] 1]]) (polynomial-one-like (make 2 [[[1 0] 1] [[2 1] 3]]))))
    (is (= (make 3 [[[0 0 0] 1]]) (polynomial-one-like (make 3 [[[1 2 1] 4] [[0 1 0] 5]]))))
    (is (= (make 2 [[[0 0] 1]]) (polynomial-one-like (make 2 [])))))
  (testing "add constant"
    (is (= (make [3 0 2]) (add (make [0 0 2]) (make [3]))))
    (is (= (make [0 0 2]) (add (make [2 0 2]) (make [-2])))))
  (testing "add/sub"
    (is (polynomial-zero? (add (make [0 0 2]) (make [0 0 -2]))))
    (is (= (make []) (add (make [0 0 2]) (make [0 0 -2]))))
    (is (= (make [3]) (add (make [3 0 2]) (make [0 0 -2]))))
    (is (= (make [-1 1]) (add (make [0 1]) (make [-1]))))
    (is (polynomial-zero? (sub (make [0 0 2]) (make [0 0 2]))))
    (is (= (make [-3]) (sub (make [0 0 2]) (make [3 0 2]))))
    (is (= (make [0 1 2]) (sub (make [3 1 2]) (make [3]))))
    (is (= (make [-2 -2 -1]) (sub (make [1]) (make [3 2 1]))))
    (is (= (make [0 0 1 0 1 -1]) (sub (make [1 0 1 0 1]) (make [1 0 0 0 0 1]))))
    (is (= (make [0 0 -1 0 -1 1]) (sub (make [1 0 0 0 0 1]) (make [1 0 1 0 1]))))
    (is (= (make [-1 -2 -3]) (polynomial-negate (make [1 2 3])))))
  (testing "mul"
    (is (= (make []) (mul (make [1 2 3]) (make [0]))))
    (is (= (make []) (mul (make [0]) (make [1 2 3]))))
    (is (= (make []) (mul (make []) (make [1 2 3]))))
    (is (= (make [1 2 3]) (mul (make [1 2 3]) (make [1]))))
    (is (= (make [1 2 3]) (mul (make [1]) (make [1 2 3]))))
    (is (= (make [3 6 9]) (mul (make [1 2 3]) (make [3]))))
    (is (= (make [0 1 2 3]) (mul (make [0 1]) (make [1 2 3]))))
    (is (= (make [0 -1 -2 -3]) (mul (make [0 -1]) (make [1 2 3]))))
    (is (= (make [-1 0 1]) (mul (make [1 1]) (make [-1 1]))))
    (is (= (make [1 3 3 1]) (mul (make [1 1]) (mul (make [1 1]) (make [1 1])))))
    (is (= (make [1 -4 6 -4 1]) (mul (mul (make [-1 1]) (make [-1 1]))
                                     (mul (make [-1 1]) (make [-1 1]))))))
  (testing "div"
    (is (= [(make [1 1]) (make [])]
           (divide (make [-1 0 1]) (make [-1 1]))))
    (is (= [(make [-10 1]) (make [-32 -21])]
           (divide (make [-42 0 -12 1]) (make [1 -2 1]))))
    (is (= [(make [3 1 1]) (make [5])]
           (divide (make [-4 0 -2 1]) (make [-3 1]))))
    (is (= [(make [-5 0 3]) (make [60 -27 -11])]
           (divide (make [-45 18 72 -27 -27 0 9]) (make [21 -9 -4 0 3]))))
    (let [U (make [-5 2 8 -3 -3 0 1 0 1])
          V (make [21 -9 -4 0 5 0 3])
          [pr d] (pseudo-remainder U V)]
      (is (= [(make [-2/9 0 1/3]) (make [-1/3 0 1/9 0 -5/9])] (divide U V)))
      (is (= [(make [-3 0 1 0 -5]) 2] [pr d]))
      (is (= (make []) (sub (mul (make [(reduce * (repeat d 3))]) U) (add (mul (make [-2 0 3]) V) pr)))))
    ;; examples from http://www.mathworks.com/help/symbolic/mupad_ref/pdivide.html
    (let [p (make [1 1 0 1])
          q (make [1 1 3])]
      (is (= [(make [10 7]) 2] (pseudo-remainder p q))))
    (let [p (make [3 0 4])
          q (make [2 2])]
      (is (= [(make [28]) 2] (pseudo-remainder p q))))
    (is (= [(make 2 []) (make 2 [[[2 1] 1] [[1 2] 1]])]
           (divide (make 2 [[[2 1] 1] [[1 2] 1]]) (make 2 [[[1 2] 1]]))))
    (is (= [(make [1]) (make [])] (divide (make [3]) (make [3]))))
    (is (= [(make [0]) 1] (pseudo-remainder (make [7]) (make [2])))))
  (testing "expt"
    (let [x+1 (make [1 1])]
      (is (= (make [1]) (expt x+1 0)))
      (is (= x+1 (expt x+1 1)))
      (is (= (make [1 2 1]) (expt x+1 2)))
      (is (= (make [1 3 3 1]) (expt x+1 3)))
      (is (= (make [1 4 6 4 1]) (expt x+1 4)))
      (is (= (make [1 5 10 10 5 1]) (expt x+1 5)))))
  (testing "GF(2)"
    (let [GFp (fn [p]
                (reify
                  Ring
                  (member? [this x] (integer? x))
                  (additive-identity [this] 0)
                  (additive-identity? [this x] (= x 0))
                  (multiplicative-identity [this] 1)
                  (multiplicative-identity? [this x] (= x 1))
                  (add [this x y] (mod (+ x y) p))
                  (subtract [this x y] (mod (- x y) p))
                  (negate [this x] (mod (- x) p))
                  (mul [this x y] (mod (* x y) p))
                  Field
                  (divide [this x y] ((* x y)))))
          GF2 (GFp 2)
          P (make GF2 1 [[[2] 1] [[0] 1]])]
      (is (= (make GF2 1 [[[4] 1] [[0] 1]]) (expt P 2)))
      (is (= (make GF2 1 [[[6] 1] [[4] 1] [[2] 1] [[0] 1]]) (expt P 3)))
      (is (= (make GF2 1 [[[8] 1] [[0] 1]]) (mul (expt P 3) P)))
      (is (= (make GF2 1 []) (sub P P)))
      (is (= (make GF2 1 []) (add P P)))
      (is (= (make GF2 1 [[[2] 1]]) (add P (polynomial-one-like P))))
      (testing "CRC polynomials"
        ;; https://en.wikipedia.org/wiki/Computation_of_cyclic_redundancy_checks
        ;; http://www.lammertbies.nl/comm/info/crc-calculation.html
        (let [x (make GF2 1 [[[1] 1]])
              unit (make GF2 1 [[[0] 1]])
              x8 (expt x 8)
              CRC-8-ATM (reduce add [unit x (expt x 2) (expt x 8)])
              M (reduce add [unit x (expt x 2) (expt x 4) (expt x 6)])
              Mx8 (mul x8 M)
              [r1 _] (pseudo-remainder Mx8 CRC-8-ATM)
              CRC-16-CCITT (reduce add [unit (expt x 5) (expt x 12) (expt x 16)])
              x16 (mul x8 x8)
              T (reduce add [(expt x 2) (expt x 4) (expt x 6)])
              Tx16 (mul x16 T)
              [r2 _] (pseudo-remainder Tx16 CRC-16-CCITT)]
          (is (= (reduce add [x (expt x 5) (expt x 7)]) r1))
          (is (= (reduce add (map #(expt x %) [0 4 5 6 9 11 12])) r2))))))
  (testing "polynomial order"
    (let [Rx (PolynomialRing a/NativeArithmetic 1)]
      (is (= 1 (a/cmp Rx (make [2 1 1]) (make [2 1]))))
      (is (= -1 (a/cmp Rx (make [2 1]) (make [2 1 1]))))
      (is (= -1 (a/cmp Rx (make [3 2 1]) (make [4 2 1]))))
      (is (= 1 (a/cmp Rx (make [4 2 1]) (make [3 2 1]))))
      (is (= 0 (a/cmp Rx (make [4 2 1]) (make [4 2 1]))))
      (is (= -1 (a/cmp Rx (make [1 0 0 1 0 0]) (make [1 0 0 0 1 0]))))
      (is (= 1 (a/cmp Rx (make [1 0 0 0 1 0]) (make [1 0 0 1 0 0]))))
      (is (= 1 (a/cmp Rx (make [1 0 0 2 0 0]) (make [1 0 0 1 0 0]))))
      (is (= -1 (a/cmp Rx (make [1 0 0 1 0 0]) (make [1 0 0 2 0 0]))))))
  (testing "monomial order"
    (let [x3 [3 0 0]
          x2z2 [2 0 2]
          xy2z [1 2 1]
          z2 [0 0 2]
          monomials [x3 x2z2 xy2z z2]
          monomial-sort #(sort-by identity % monomials)]
      (is (= [z2 xy2z x2z2 x3] (monomial-sort lex-order)))
      (is (= [z2 x3 x2z2 xy2z] (monomial-sort graded-reverse-lex-order)))
      (is (= [z2 x3 xy2z x2z2] (monomial-sort graded-lex-order))))))

(deftest poly-evaluate
  (testing "arity 1"
    (let [[k x] (basis a/NativeArithmetic 1)
          p (reduce add [(scale 3 x) (scale 2 k)])]
      (is (= 14 (evaluate p [4])))
      (is (thrown? Error (evaluate p [3 2]))))
    (testing "arity 2"
      (let [[k x y] (basis a/NativeArithmetic 2)
            p (expt (add x y) 2)]
        (is (= 25 (evaluate p [2 3])))
        (is (= (make [4 4 1]) (evaluate p [2])))))
    (testing "arity 3"
      (let [[k x y z] (basis a/NativeArithmetic 3)
            p (reduce add [(expt x 3) (expt y 2) z k])]
        (is (= 19 (evaluate p [2 3 1])))))
    (testing "arity 4"
      (let [[k w x y z] (basis a/NativeArithmetic 4)
            p (expt (reduce sub [w x y z]) 2)]
        (is (= 36 (evaluate p [10 1 2 1])))))
    (testing "arity 5"
      (let [[k v w x z y] (basis a/NativeArithmetic 5)
            p (expt (reduce sub [v w x y z]) 2)]
        (is (= 16 (evaluate p [10 1 2 1 2])))))
    (testing "arity 10"
      (let [[k x0 x1 x2 x3 x4 x5 x6 x7 x8 x9] (basis a/NativeArithmetic 10)
            p (expt (reduce sub [x0 x1 x2 x3 x4 x5 x6 x7 x8 x9]) 3)]
        (is (= 216 (evaluate p [10 1 2 1 2 -3 1 -2 -1 3])))))
    (testing "constant polynomials"
      (let [p1 (make [3])
            p2 (make 2 [[[0 0] 5]])
            p3 (make 3 [[[1 0 0] 1]])
            p4 (make 3 [[[0 1 0] 1]])
            p5 (make 3 [[[0 0 1] 1]])]
        (is (= 3 (evaluate p1 [99])))
        (is (= 5 (evaluate p2 [99 98])))
        (is (= 7 (evaluate p3 [7 8 9])))
        (is (= 8 (evaluate p4 [7 8 9])))
        (is (= 9 (evaluate p5 [7 8 9])))))
    (testing "partial application"
      (let [[k x y z] (basis a/NativeArithmetic 3)
            p (reduce add [k (scale 2 x) (scale 3 (mul x y)) (scale 4 (reduce mul [x y z]))])]
        (is (= (let [[k y z] (basis a/NativeArithmetic 2)]
                 (reduce add [(scale 3 k) (scale 3 y) (scale 4 (mul y z))])) (evaluate p [1])))
        (is (= (make [9 8]) (evaluate p [1 2])))
        (is (= 33 (evaluate p [1 2 3])))
        (is (thrown? Error (evaluate p [1 2 3 4])))))))

(deftest poly-partial-derivatives
  (let [V (make [1 2 3 4])
        U (make 2 [[[1 1] 3] [[2 2] 4] [[0 0] 5] [[0 3] 7] [[4 0] -2]])]
    (is (= (make [2 6 12]) (partial-derivative V 0)))
    (is (= [(make [2 6 12])] (partial-derivatives V)))
    (is (= (make 2 [[[0 1] 3] [[1 2] 8] [[3 0] -8]]) (partial-derivative U 0)))
    (is (= (make 2 [[[1 0] 3] [[2 1] 8] [[0 2] 21]]) (partial-derivative U 1)))
    (is (= [(make 2 [[[0 1] 3] [[1 2] 8] [[3 0] -8]])
            (make 2 [[[1 0] 3] [[2 1] 8] [[0 2] 21]])]
           (partial-derivatives U)))))

(defn generate-poly
  [arity]
  (gen/fmap #(make arity %)
            (gen/vector
              (gen/tuple
                (gen/vector gen/pos-int arity)
                gen/int))))

(defn generate-nonzero-poly
  [arity]
  (gen/such-that (complement polynomial-zero?) (generate-poly arity)))

(def ^:private num-tests 50)

(defspec p+p=2p num-tests
         (prop/for-all [^Polynomial p (gen/bind gen/nat generate-poly)]
                       (= (add p p) (mul p (make-constant (.arity p) 2)))))

(defspec p-p=0 num-tests
         (prop/for-all [p (gen/bind gen/nat generate-poly)]
                       (polynomial-zero? (sub p p))))

(defspec pq-div-p=q num-tests
         (gen/let [arity (gen/fmap inc gen/nat)]
                  (prop/for-all [p (generate-poly arity)
                                 q (generate-nonzero-poly arity)]
                                (let [[Q R] (divide (mul p q) q)]
                                  (and (polynomial-zero? R)
                                       (= Q p))))))

(defspec p+q=q+p num-tests
         (gen/let [arity gen/nat]
                  (prop/for-all [p (generate-poly arity)
                                 q (generate-poly arity)]
                                (= (add p q) (add q p)))))

(defspec pq=qp num-tests
         (gen/let [arity gen/nat]
                  (prop/for-all [p (generate-poly arity)
                                 q (generate-poly arity)]
                                (= (mul p q) (mul q p)))))

(defspec p*_q+r_=p*q+p*r num-tests
         (gen/let [arity gen/nat]
                  (prop/for-all [p (generate-poly arity)
                                 q (generate-poly arity)
                                 r (generate-poly arity)]
                                (= (mul p (add q r)) (add (mul p q) (mul p r))))))

(defspec lower-and-raise-arity-are-inverse num-tests
         (prop/for-all [p (gen/bind (gen/choose 2 10) generate-nonzero-poly)]
                       (= p (raise-arity (lower-arity p)))))

(defspec evaluation-homomorphism num-tests
         (gen/let [arity (gen/choose 1 6)]
                  (prop/for-all [p (generate-poly arity)
                                 q (generate-poly arity)
                                 xs (gen/vector gen/int arity)]
                                (= (*' (evaluate p xs) (evaluate q xs))
                                   (evaluate (mul p q) xs)))))

