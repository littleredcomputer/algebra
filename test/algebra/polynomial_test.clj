;; Copyright © 2017 Colin Smith. MIT License.

(ns algebra.polynomial-test
  (:require [clojure.test :refer :all]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.test.check.clojure-test :refer [defspec]]
            [algebra.polynomial :refer :all]
            [clojure.walk :as walk]
            [criterium.core :as c]
            [algebra :as a])
  (:import (algebra.polynomial Polynomial)
           (algebra Ring Field)))

(def ^:private Rx (PolynomialRing a/NativeArithmetic 1))
(def ^:private P #(make-dense Rx %&))

(deftest poly-core
  (testing "zero"
    (is (polynomial-zero? (P)))
    (is (polynomial-zero? (P 0)))
    (is (polynomial-zero? (P)))
    (is (polynomial-zero? (make Rx 2 [])))
    (is (polynomial-zero? (make Rx 2 [])))
    (is (not (polynomial-zero? (P 1)))))
  (testing "unity"
    (is (polynomial-one? (P 1)))
    (is (polynomial-one? (make 2 [[[0 0] 1]])))
    (is (polynomial-one? (make 3 [[[0 0 0] 1]])))
    (is (not (polynomial-one? (make 3 [[[0 0 0] 1] [[0 0 1] 2]]))))
    (is (not (polynomial-one? (P 1.1))))
    (is (not (polynomial-one? (P 1.0))))               ;; though maybe it should be
    (is (polynomial-one? (make (PolynomialRing a/NativeArithmetic 1) 1 [[[0] (P 1)]])))
    (is (not (polynomial-one? (make (PolynomialRing a/NativeArithmetic 1) 1 [[[0] (P 2)]])))))
  (testing "degree"
    (is (= (degree (P)) -1))
    (is (= (degree (P -1 1)) 1))
    (is (= (degree (P 0 1)) 1))
    (is (= (degree (P -1 0 2)) 2))
    (is (= (degree (P -1 2 0)) 1))
    (is (= (degree (P 0 0)) -1)))
  (testing "zero-like"
    (is (= (P) (polynomial-zero-like (P 1 2 3))))
    (is (= (make 2 []) (polynomial-zero-like (make 2 [[[1 0] 1] [[2 1] 3]]))))
    (is (= (make 3 []) (polynomial-zero-like (make 3 [[[1 2 1] 4] [[0 1 0] 5]])))))
  (testing "one-like"
    (is (= (P 1) (polynomial-one-like (P 1 2 3))))
    (is (= (make 2 [[[0 0] 1]]) (polynomial-one-like (make 2 [[[1 0] 1] [[2 1] 3]]))))
    (is (= (make 3 [[[0 0 0] 1]]) (polynomial-one-like (make 3 [[[1 2 1] 4] [[0 1 0] 5]]))))
    (is (= (make 2 [[[0 0] 1]]) (polynomial-one-like (make 2 [])))))
  (testing "add constant"
    (is (= (P 3 0 2) (add (P 0 0 2) (P 3))))
    (is (= (P 0 0 2) (add (P 2 0 2) (P -2)))))
  (testing "add/sub"
    (is (polynomial-zero? (add (P 0 0 2) (P 0 0 -2))))
    (is (= (P) (add (P 0 0 2) (P 0 0 -2))))
    (is (= (P 3) (add (P 3 0 2) (P 0 0 -2))))
    (is (= (P -1 1) (add (P 0 1) (P -1))))
    (is (polynomial-zero? (sub (P 0 0 2) (P 0 0 2))))
    (is (= (P -3) (sub (P 0 0 2) (P 3 0 2))))
    (is (= (P 0 1 2) (sub (P 3 1 2) (P 3))))
    (is (= (P -2 -2 -1) (sub (P 1) (P 3 2 1))))
    (is (= (P 0 0 1 0 1 -1) (sub (P 1 0 1 0 1) (P 1 0 0 0 0 1))))
    (is (= (P 0 0 -1 0 -1 1) (sub (P 1 0 0 0 0 1) (P 1 0 1 0 1))))
    (is (= (P -1 -2 -3) (polynomial-negate (P 1 2 3)))))
  (testing "mul"
    (is (= (P) (mul (P 1 2 3) (P 0))))
    (is (= (P) (mul (P 0) (P 1 2 3))))
    (is (= (P) (mul (P) (make-dense Rx [1 2 3]))))
    (is (= (P 1 2 3) (mul (P 1 2 3) (P 1))))
    (is (= (P 1 2 3) (mul (P 1) (P 1 2 3))))
    (is (= (P 3 6 9) (mul (P 1 2 3) (P 3))))
    (is (= (P 0 1 2 3) (mul (P 0 1) (P 1 2 3))))
    (is (= (P 0 -1 -2 -3) (mul (P 0 -1) (P 1 2 3))))
    (is (= (P -1 0 1) (mul (P 1 1) (P -1 1))))
    (is (= (P 1 3 3 1) (mul (P 1 1) (mul (P 1 1) (P 1 1)))))
    (is (= (P 1 -4 6 -4 1) (mul (mul (P -1 1) (P -1 1))
                                (mul (P -1 1) (P -1 1))))))
  (testing "div"
    (is (= [(P 1 1) (P)]
           (divide (P -1 0 1) (P -1 1))))
    (is (= [(P -10 1) (P -32 -21)]
           (divide (P -42 0 -12 1) (P 1 -2 1))))
    (is (= [(P 3 1 1) (P 5)]
           (divide (P -4 0 -2 1) (P -3 1))))
    (is (= [(P -5 0 3) (P 60 -27 -11)]
           (divide (P -45 18 72 -27 -27 0 9) (P 21 -9 -4 0 3))))
    (let [U (P -5 2 8 -3 -3 0 1 0 1)
          V (P 21 -9 -4 0 5 0 3)
          pr (zippel-pseudo-remainder U V)]
      (is (= [(P -2/9 0 1/3) (P -1/3 0 1/9 0 -5/9)] (divide U V)))
      (is (= (P -3 0 1 0 -5) pr)))
    ;; examples from http://www.mathworks.com/help/symbolic/mupad_ref/pdivide.html
    (let [p (P 1 1 0 1)
          q (P 1 1 3)]
      (is (= (P 10 7) (zippel-pseudo-remainder p q))))
    (let [p (P 3 0 4)
          q (P 2 2)]
      (is (= (P 28) (zippel-pseudo-remainder p q))))
    (is (= [(make 2 []) (make 2 [[[2 1] 1] [[1 2] 1]])]
           (divide (make 2 [[[2 1] 1] [[1 2] 1]]) (make 2 [[[1 2] 1]]))))
    (is (= [(P 1) (P)] (divide (P 3) (P 3))))
    (is (= (P 0) (zippel-pseudo-remainder (P 7) (P 2)))))
  (testing "expt"
    (let [x+1 (P 1 1)]
      (is (= (P 1) (expt x+1 0)))
      (is (= x+1 (expt x+1 1)))
      (is (= (P 1 2 1) (expt x+1 2)))
      (is (= (P 1 3 3 1) (expt x+1 3)))
      (is (= (P 1 4 6 4 1) (expt x+1 4)))
      (is (= (P 1 5 10 10 5 1) (expt x+1 5)))))
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
              r1 (zippel-pseudo-remainder Mx8 CRC-8-ATM)
              CRC-16-CCITT (reduce add [unit (expt x 5) (expt x 12) (expt x 16)])
              x16 (mul x8 x8)
              T (reduce add [(expt x 2) (expt x 4) (expt x 6)])
              Tx16 (mul x16 T)
              r2 (zippel-pseudo-remainder Tx16 CRC-16-CCITT)]
          (is (= (reduce add [x (expt x 5) (expt x 7)]) r1))
          (is (= (reduce add (map #(expt x %) [0 4 5 6 9 11 12])) r2))))))
  (testing "pseudo remainder sequences"
    (let [F1 (P -5 2 8 -3 -3 0 1 0 1)
          F2 (P 21 -9 -4 0 5 0 3)]
      ;; As seen in:
      ;; https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Pseudo-remainder_sequences
      ;; "Trivial" PRS
      (is (= [F1
              F2
              (P -9 0 3 0 -15)
              (P -59535 30375 15795)
              (P -1654608338437500 1254542875143750)
              (P 12593338795500743100931141992187500)]
             ((pseudo-remainder-sequence classic-pseudo-remainder) F1 F2)))
      ;; "Primitive" PRS
      (is (= [F1
              F2
              (P -3 0 1 0 -5)
              (P -49 25 13)
              (P -6150 4663)
              (P 1)]
             ((pseudo-remainder-sequence #(univariate-primitive-part (zippel-pseudo-remainder %1 %2))) F1 F2)))
      (is (= [(P -5 2 8 -3 -3 0 1 0 1)
              (P 21 -9 -4 0 5 0 3)
              (P 9 0 -3 0 15)
              (P -245 125 65)
              (P -12300 9326)
              (P 260708)              ]
             (subresultant-polynomial-remainder-sequence F1 F2)))
      (is (= [(P -8 28 -22 -31 60 -21 -22 23 -8 1)
              (P -8 -4 26 9 -32 -5 18 -1 -4 1)
              (P 0 -32 48 40 -92 16 40 -24 4)
              (P -128 192 160 -368 64 160 -96 16)
              ]
             (let [xm1 (P -1 1)
                   xm2 (P -2 1)
                   xp1 (P 1 1)]
               (subresultant-polynomial-remainder-sequence
                (mul (mul (expt xm1 4) (expt xm2 3)) (expt xp1 2))
                (mul (mul (expt xm1 2) (expt xm2 3)) (expt xp1 4))))))
      (is (= [(P 0 0 -2) (P 0 -1)]
             (subresultant-polynomial-remainder-sequence (P 0 0 -2) (P 0 -1))))
      (is (= [(P 1) (P 1)]
             (subresultant-polynomial-remainder-sequence (P 1) (P 1))))))

  (testing "polynomial order"
    (let [Rx (PolynomialRing a/NativeArithmetic 1)]
      (is (= 1 (a/cmp Rx (P 2 1 1) (P 2 1))))
      (is (= -1 (a/cmp Rx (P 2 1) (P 2 1 1))))
      (is (= -1 (a/cmp Rx (P 3 2 1) (P 4 2 1))))
      (is (= 1 (a/cmp Rx (P 4 2 1) (P 3 2 1))))
      (is (= 0 (a/cmp Rx (P 4 2 1) (P 4 2 1))))
      (is (= -1 (a/cmp Rx (P 1 0 0 1 0 0) (P 1 0 0 0 1 0))))
      (is (= 1 (a/cmp Rx (P 1 0 0 0 1 0) (P 1 0 0 1 0 0))))
      (is (= 1 (a/cmp Rx (P 1 0 0 2 0 0) (P 1 0 0 1 0 0))))
      (is (= -1 (a/cmp Rx (P 1 0 0 1 0 0) (P 1 0 0 2 0 0))))))

  (testing "scalar multiplication"
    (let [Rx (PolynomialRing a/NativeArithmetic 1)]
      (is (= (P 3 6 9) (a/scale Rx 3 (P 1 2 3))))))

  (testing "monomial order"
    (let [x3 [3 0 0]
          x2z2 [2 0 2]
          xy2z [1 2 1]
          z2 [0 0 2]
          monomials [x3 x2z2 xy2z z2]
          monomial-sort #(sort-by identity % monomials)]
      (is (= [z2 xy2z x2z2 x3] (monomial-sort lex-order)))
      (is (= [z2 x3 x2z2 xy2z] (monomial-sort graded-reverse-lex-order)))
      (is (= [z2 x3 xy2z x2z2] (monomial-sort graded-lex-order)))))
  (testing "primitive part"
    (is (= (P 1 2 3 4) (univariate-primitive-part (P 2 4 6 8))))
    (is (= (P 2 3 4 5) (univariate-primitive-part (P 2 3 4 5))))))

(deftest poly-partial-derivatives
  (let [V (P 1 2 3 4)
        U (make 2 [[[1 1] 3] [[2 2] 4] [[0 0] 5] [[0 3] 7] [[4 0] -2]])]
    (is (= (P 2 6 12) (partial-derivative V 0)))
    (is (= [(P 2 6 12)] (partial-derivatives V)))
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

(defspec add=concat+make
  (gen/let [arity (gen/choose 1 10)]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)]
                  (= (add p q) (make (.arity p) (concat (.terms p) (.terms q)))))))

(defspec p+p=2p
  (prop/for-all [^Polynomial p (gen/bind gen/nat generate-poly)]
                (let [one (polynomial-one-like p)]
                  (= (add p p) (mul p (add one one))))))

(defspec p-p=0
  (prop/for-all [p (gen/bind gen/nat generate-poly)]
                (polynomial-zero? (sub p p))))

(defspec pq-div-q=p
  (gen/let [arity (gen/choose 1 10)]
    (prop/for-all [p (generate-poly arity)
                   q (generate-nonzero-poly arity)]
                  (let [[Q R] (divide (mul p q) q)]
                    (and (polynomial-zero? R)
                         (= Q p))))))

(defspec p+q=q+p
  (gen/let [arity gen/nat]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)]
                  (= (add p q) (add q p)))))

(defspec pq=qp
  (gen/let [arity gen/nat]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)]
                  (= (mul p q) (mul q p)))))

(defspec p*_q+r_=p*q+p*r
  (gen/let [arity gen/nat]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)
                   r (generate-poly arity)]
                  (= (mul p (add q r)) (add (mul p q) (mul p r))))))


(defn ^:private make-polynomial-from-ints
  "Given integers i0, i1, ... returns the polynomial (x+i0)(x+i1)..."
  [is]
  (reduce mul (P 1) (map #(P % 1) is)))

(def ^:private univariate-polynomial-gcd-test-case-generator
  "A generator which initially generates a vector of integers, and then
  partitions it into (typically) overlapping subsets. Returns the two
  subsets along with the overlap. These are used to generate
  polynomial pairs with (typically) nontrivial GCDs."
  (gen/fmap
   (fn [is]
     (let [c (count is)
           a0 (rand-int c)
           b0 (rand-int c)
           [a b] (if (> a0 b0) [b0 a0] [a0 b0])]
       [(subvec is 0 b) (subvec is a c) (subvec is a b)]))
   (gen/vector gen/int)))

(defn ^:private test-univariate-polynomial-gcd-with
  [gcd-er]
  (let [Rx (PolynomialRing a/NativeArithmetic 1)]
    (fn [test-case]
      (let [[u v k] (map make-polynomial-from-ints test-case)
           g (gcd-er u v)]
        (and (a/evenly-divides? Rx g u)
             (a/evenly-divides? Rx g v)
             (a/evenly-divides? Rx k g))))))


(defspec test-univariate-subresultant-gcd
  (prop/for-all [test-case univariate-polynomial-gcd-test-case-generator]
                ((test-univariate-polynomial-gcd-with univariate-subresultant-gcd) test-case)))

(defspec test-univariate-euclid-gcd
  (prop/for-all [test-case univariate-polynomial-gcd-test-case-generator]
                ((test-univariate-polynomial-gcd-with univariate-euclid-gcd) test-case)))

(defn -main
  [& args]
  #_(let [pqs  (gen/sample
              (gen/bind (gen/choose 8 12)
                        #(gen/tuple (generate-poly %)
                                    (generate-poly %)))
              256)]
    (println "benchmark add")
    (c/quick-bench (dorun (for [[p q] pqs] (add p q)))))
  #_(let [pqs (gen/sample
             (gen/let [u (generate-poly 1)
                       v (generate-nonzero-poly 1)
                       g (generate-nonzero-poly 1)]
               [(mul u g) (mul v g)])
             256)]
    (println "benchmark pr")
    (c/quick-bench (dorun (for [[p q] pqs] (zippel-pseudo-remainder p q)))))
  (let [test-cases (gen/sample univariate-polynomial-gcd-test-case-generator 100)]
    (println "benchmark subresultant gcd")
    (let [sr-test (test-univariate-polynomial-gcd-with univariate-subresultant-gcd)]
      (c/quick-bench
       (dorun (for [test-case test-cases]
                (sr-test test-case)))))
    (println "benchmark euclid gcd")
    (let [euc-test (test-univariate-polynomial-gcd-with univariate-euclid-gcd)]
      (c/quick-bench
       (dorun (for [test-case test-cases]
                (euc-test test-case)))))))
