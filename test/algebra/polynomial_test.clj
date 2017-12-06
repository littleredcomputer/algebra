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

(def ^:private Zx (PolynomialRing a/Z 1))
(def ^:private Zxy (PolynomialRing a/Z 2))
(def ^:private Zxyz (PolynomialRing a/Z 3))
(def ^:private ZZx (PolynomialRing Zx 1))
(def ^:private P #(make-unary Zx %&))

(deftest poly-core
  (testing "zero"
    (is (a/additive-identity? Zx (P)))
    (is (a/additive-identity? Zx (P 0)))
    (is (a/additive-identity? Zx (P)))
    (is (a/additive-identity? Zxy (make Zxy [])))
    (is (not (a/additive-identity? Zx (P 1)))))
  (testing "unity"
    (is (a/multiplicative-identity? Zx (P 1)))
    (is (a/multiplicative-identity? Zxy (make Zxy [[[0 0] 1]])))
    (is (a/multiplicative-identity? Zxyz (make Zxyz [[[0 0 0] 1]])))
    (is (not (a/multiplicative-identity? Zx (make Zxyz [[[0 0 0] 1] [[0 0 1] 2]]))))
    (is (not (a/multiplicative-identity? Zx (P 1.1))))
    (is (not (a/multiplicative-identity? Zx (P 1.0))))               ;; though maybe it should be
    (is (a/multiplicative-identity? ZZx (make ZZx [[[0] (P 1)]])))
    (is (not (a/multiplicative-identity? ZZx (make ZZx [[[0] (P 2)]])))))
  (testing "degree"
    (is (= (degree (P)) -1))
    (is (= (degree (P -1 1)) 1))
    (is (= (degree (P 0 1)) 1))
    (is (= (degree (P -1 0 2)) 2))
    (is (= (degree (P -1 2 0)) 1))
    (is (= (degree (P 0 0)) -1)))
  (testing "add constant"
    (is (= (P 3 0 2) (a/add Zx (P 0 0 2) (P 3))))
    (is (= (P 0 0 2) (a/add Zx (P 2 0 2) (P -2)))))
  (testing "add/sub"
    (is (a/additive-identity? Zx (a/add Zx (P 0 0 2) (P 0 0 -2))))
    (is (= (P) (a/add Zx (P 0 0 2) (P 0 0 -2))))
    (is (= (P 3) (a/add Zx (P 3 0 2) (P 0 0 -2))))
    (is (= (P -1 1) (a/add Zx (P 0 1) (P -1))))
    (is (a/additive-identity? Zx (a/subtract Zx (P 0 0 2) (P 0 0 2))))
    (is (= (P -3) (a/subtract Zx (P 0 0 2) (P 3 0 2))))
    (is (= (P 0 1 2) (a/subtract Zx (P 3 1 2) (P 3))))
    (is (= (P -2 -2 -1) (a/subtract Zx (P 1) (P 3 2 1))))
    (is (= (P 0 0 1 0 1 -1) (a/subtract Zx (P 1 0 1 0 1) (P 1 0 0 0 0 1))))
    (is (= (P 0 0 -1 0 -1 1) (a/subtract Zx (P 1 0 0 0 0 1) (P 1 0 1 0 1))))
    (is (= (P -1 -2 -3) (a/negate Zx (P 1 2 3)))))
  (testing "mul"
    (is (= (P) (a/mul Zx (P 1 2 3) (P 0))))
    (is (= (P) (a/mul Zx (P 0) (P 1 2 3))))
    (is (= (P) (a/mul Zx (P) (make-unary Zx [1 2 3]))))
    (is (= (P 1 2 3) (a/mul Zx (P 1 2 3) (P 1))))
    (is (= (P 1 2 3) (a/mul Zx (P 1) (P 1 2 3))))
    (is (= (P 3 6 9) (a/mul Zx (P 1 2 3) (P 3))))
    (is (= (P 0 1 2 3) (a/mul Zx (P 0 1) (P 1 2 3))))
    (is (= (P 0 -1 -2 -3) (a/mul Zx (P 0 -1) (P 1 2 3))))
    (is (= (P -1 0 1) (a/mul Zx (P 1 1) (P -1 1))))
    (is (= (P 1 3 3 1) (a/mul Zx (P 1 1) (a/mul Zx (P 1 1) (P 1 1)))))
    (is (= (P 1 -4 6 -4 1) (a/mul Zx (a/mul Zx (P -1 1) (P -1 1))
                                (a/mul Zx (P -1 1) (P -1 1))))))
  (testing "div"
    (is (= [(P 1 1) (P)]
           (a/quorem Zx (P -1 0 1) (P -1 1))))
    (is (= [(P -10 1) (P -32 -21)]
           (a/quorem Zx (P -42 0 -12 1) (P 1 -2 1))))
    (is (= [(P 3 1 1) (P 5)]
           (a/quorem Zx (P -4 0 -2 1) (P -3 1))))
    (is (= [(P -5 0 3) (P 60 -27 -11)]
           (a/quorem Zx (P -45 18 72 -27 -27 0 9) (P 21 -9 -4 0 3))))
    (let [U (P -5 2 8 -3 -3 0 1 0 1)
          V (P 21 -9 -4 0 5 0 3)
          pr (zippel-pseudo-remainder U V)]
      (is (= [(P -2/9 0 1/3) (P -1/3 0 1/9 0 -5/9)] (a/quorem Zx U V)))
      (is (= (P -3 0 1 0 -5) pr)))
    ;; examples from http://www.mathworks.com/help/symbolic/mupad_ref/pdivide.html
    (let [p (P 1 1 0 1)
          q (P 1 1 3)]
      (is (= (P 10 7) (zippel-pseudo-remainder p q))))
    (let [p (P 3 0 4)
          q (P 2 2)]
      (is (= (P 28) (zippel-pseudo-remainder p q))))
    ;; Multivariate polynomial rings are not Euclidean.
    (is (thrown-with-msg? IllegalArgumentException #"No implementation.*Euclidean"
                          (a/quorem Zxy (make Zxy [[[2 1] 1] [[1 2] 1]]) (make Zxy [[[1 2] 1]]))))
    (is (= [(P 1) (P)] (a/quorem Zx (P 3) (P 3))))
    (is (= (P 0) (zippel-pseudo-remainder (P 7) (P 2)))))
  (testing "expt"
    (let [x+1 (P 1 1)]
      (is (= (P 1) (a/exponentiation-by-squaring Zx x+1 0)))
      (is (= x+1 (a/exponentiation-by-squaring Zx x+1 1)))
      (is (= (P 1 2 1) (a/exponentiation-by-squaring Zx x+1 2)))
      (is (= (P 1 3 3 1) (a/exponentiation-by-squaring Zx x+1 3)))
      (is (= (P 1 4 6 4 1) (a/exponentiation-by-squaring Zx x+1 4)))
      (is (= (P 1 5 10 10 5 1) (a/exponentiation-by-squaring Zx x+1 5)))))
  (testing "GF(2)"
    (let [Z2 (a/->Zmod 2)
          Z2x (PolynomialRing Z2 1)
          P (make-unary Z2x [1 0 1])]
      (is (= (make Z2x [[[4] 1] [[0] 1]]) (a/exponentiation-by-squaring Zx P 2)))
      (is (= (make Z2x [[[6] 1] [[4] 1] [[2] 1] [[0] 1]]) (a/exponentiation-by-squaring Zx P 3)))
      (is (= (make Z2x [[[8] 1] [[0] 1]]) (a/mul Zx (a/exponentiation-by-squaring Zx P 3) P)))
      (is (= (make Z2x []) (a/subtract Zx P P)))
      (is (= (make Z2x []) (a/add Zx P P)))
      (is (= (make Z2x [[[2] 1]]) (a/add Zx P (a/multiplicative-identity Z2x))))
      (testing "CRC polynomials"
        ;; https://en.wikipedia.org/wiki/Computation_of_cyclic_redundancy_checks
        ;; http://www.lammertbies.nl/comm/info/crc-calculation.html
        (let [p+p (partial a/add Z2x)
              x (make-unary Z2x [0 1])
              unit (make-unary Z2x [1])
              x8 (a/exponentiation-by-squaring Z2x x 8)
              CRC-8-ATM (reduce p+p [unit
                                     x
                                     (a/exponentiation-by-squaring Z2x x 2)
                                     (a/exponentiation-by-squaring Z2x x 8)])
              M (reduce p+p [unit
                             x
                             (a/exponentiation-by-squaring Z2x x 2)
                             (a/exponentiation-by-squaring Z2x x 4)
                             (a/exponentiation-by-squaring Z2x x 6)])
              Mx8 (a/mul Z2x x8 M)
              r1 (zippel-pseudo-remainder Mx8 CRC-8-ATM)
              CRC-16-CCITT (reduce p+p [unit
                                        (a/exponentiation-by-squaring Z2x x 5)
                                        (a/exponentiation-by-squaring Z2x x 12)
                                        (a/exponentiation-by-squaring Z2x x 16)])
              x16 (a/mul Z2x x8 x8)
              T (reduce p+p [(a/exponentiation-by-squaring Z2x x 2)
                             (a/exponentiation-by-squaring Z2x x 4)
                             (a/exponentiation-by-squaring Z2x x 6)])
              Tx16 (a/mul Z2x x16 T)
              r2 (zippel-pseudo-remainder Tx16 CRC-16-CCITT)]
          (is (not= Z2x Zx))
          (is (= (reduce p+p [x
                              (a/exponentiation-by-squaring Z2x x 5)
                              (a/exponentiation-by-squaring Z2x x 7)]) r1))
          (is (= (reduce p+p (map #(a/exponentiation-by-squaring Z2x x %) [0 4 5 6 9 11 12])) r2))))))

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
              (P -128 192 160 -368 64 160 -96 16)]
             (let [xm1 (P -1 1)
                   xm2 (P -2 1)
                   xp1 (P 1 1)]
               (subresultant-polynomial-remainder-sequence
                (a/mul Zx (a/mul Zx (a/exponentiation-by-squaring Zx xm1 4)
                                 (a/exponentiation-by-squaring Zx xm2 3))
                       (a/exponentiation-by-squaring Zx xp1 2))
                (a/mul Zx (a/mul Zx (a/exponentiation-by-squaring Zx xm1 2)
                                 (a/exponentiation-by-squaring Zx xm2 3))
                       (a/exponentiation-by-squaring Zx xp1 4))))))
      (is (= [(P 0 0 -2) (P 0 -1)]
             (subresultant-polynomial-remainder-sequence (P 0 0 -2) (P 0 -1))))
      (is (= [(P 1) (P 1)]
             (subresultant-polynomial-remainder-sequence (P 1) (P 1))))))

  (testing "polynomial order"
    (is (= 1 (a/cmp Zx (P 2 1 1) (P 2 1))))
    (is (= -1 (a/cmp Zx (P 2 1) (P 2 1 1))))
    (is (= -1 (a/cmp Zx (P 3 2 1) (P 4 2 1))))
    (is (= 1 (a/cmp Zx (P 4 2 1) (P 3 2 1))))
    (is (= 0 (a/cmp Zx (P 4 2 1) (P 4 2 1))))
    (is (= -1 (a/cmp Zx (P 1 0 0 1 0 0) (P 1 0 0 0 1 0))))
    (is (= 1 (a/cmp Zx (P 1 0 0 0 1 0) (P 1 0 0 1 0 0))))
    (is (= 1 (a/cmp Zx (P 1 0 0 2 0 0) (P 1 0 0 1 0 0))))
    (is (= -1 (a/cmp Zx (P 1 0 0 1 0 0) (P 1 0 0 2 0 0)))))

  (testing "scalar multiplication"
    (is (= (P 3 6 9) (a/scale Zx 3 (P 1 2 3))))
    (is (= (P) (a/scale Zx 0 (P 1 2 3)))))

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

  (testing "field gcd"
    (is (= [(P -3/2 9/2)
            (P 1)
            (P -9/4 3/2)]
           (a/extended-euclid Zx (P -6 30 -42 18) (P -2 10 -12))))
    ;; XXX: need to implement the monic-remainder calculation in extended GCD to get this right.
    (is (= (P 14999180998204546086628509444183593910034968673275/141919206653976666794661960809129382074315418338)
           (first (a/extended-euclid Zx (P -764 -979 -741 -814 -65 824) (P 617 916 880 663 216)))))
    #_(is (= [] (a/extended-euclid Zx (P 2) (P 1 0))))
    ))

(deftest poly-partial-derivatives
  (let [V (P 1 2 3 4)
        U (make Zxy [[[1 1] 3] [[2 2] 4] [[0 0] 5] [[0 3] 7] [[4 0] -2]])]
    (is (= (P 2 6 12) (partial-derivative V 0)))
    (is (= [(P 2 6 12)] (partial-derivatives V)))
    (is (= (make Zxy [[[0 1] 3] [[1 2] 8] [[3 0] -8]]) (partial-derivative U 0)))
    (is (= (make Zxy [[[1 0] 3] [[2 1] 8] [[0 2] 21]]) (partial-derivative U 1)))
    (is (= [(make Zxy [[[0 1] 3] [[1 2] 8] [[3 0] -8]])
            (make Zxy [[[1 0] 3] [[2 1] 8] [[0 2] 21]])]
           (partial-derivatives U)))))

(defn generate-poly
  [arity]
  (gen/fmap #(make (PolynomialRing a/Z arity) %)
            (gen/vector
             (gen/tuple
              (gen/vector gen/pos-int arity)
              gen/int))))

(defn generate-nonzero-poly
  [arity]
  (gen/such-that #(not (a/additive-identity? Zx %)) (generate-poly arity)))

(def ^:private num-tests 50)

(defspec add=concat+make
  (gen/let [arity (gen/choose 1 10)]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)]
                  (= (a/add Zx p q) (make (PolynomialRing a/Z (.arity p))
                                          (concat (.terms p) (.terms q)))))))

(defspec rp+sp=_r+s_p
  (prop/for-all [[p r s] (gen/bind gen/nat #(gen/tuple
                                             (generate-poly %)
                                             gen/ratio
                                             gen/ratio))]
                (let [R (PolynomialRing a/Z (:arity p))]
                  (= (a/add R (a/scale R r p) (a/scale R s p))
                     (a/scale R (+ r s) p)))))

(defspec p-p=0
  (prop/for-all [p (gen/bind gen/nat generate-poly)]
                (a/additive-identity? Zx (a/subtract Zx p p))))

(defspec pq-div-q=p
  (gen/let [arity (gen/choose 1 10)]
    (prop/for-all [p (generate-poly arity)
                   q (generate-nonzero-poly arity)]
                  (let [[Q R] (a/quorem Zx (a/mul Zx p q) q)]
                    (and (a/additive-identity? Zx R)
                         (= Q p))))))

(defspec p+q=q+p
  (gen/let [arity gen/nat]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)]
                  (= (a/add Zx p q) (a/add Zx q p)))))

(defspec pq=qp
  (gen/let [arity gen/nat]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)]
                  (= (a/mul Zx p q) (a/mul Zx q p)))))

(defspec p*_q+r_=p*q+p*r
  (gen/let [arity gen/nat]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)
                   r (generate-poly arity)]
                  (= (a/mul Zx p (a/add Zx q r)) (a/add Zx (a/mul Zx p q) (a/mul Zx p r))))))


(defn ^:private polynomial-make-from-ints
  "Given integers i0, i1, ... returns the polynomial (x+i0)(x+i1)..."
  [is]
  (reduce #(a/mul Zx %1 %2) (P 1) (map #(P % 1) is)))

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
  (fn [test-case]
    (let [[u v k] (map polynomial-make-from-ints test-case)
          g (gcd-er u v)]
      (and (a/evenly-divides? Zx g u)
           (a/evenly-divides? Zx g v)
           (a/evenly-divides? Zx k g)))))

(defspec extended-euclid-over-polynomials 25
  (prop/for-all [p (generate-poly 1)
                 q (generate-poly 1)]
                (let [[g s t] (a/extended-euclid Zx p q)]
                  (and (or (a/additive-identity? Zx g)
                           (and (a/evenly-divides? Zx g p)
                                (a/evenly-divides? Zx g q)))
                       (or (a/additive-identity? Zx p)
                           (a/additive-identity? Zx q)
                           (not (a/additive-identity? Zx g)))
                       (= g (a/add Zx (a/mul Zx s p) (a/mul Zx t q)))))))

(defspec test-univariate-subresultant-gcd
  (prop/for-all [test-case univariate-polynomial-gcd-test-case-generator]
                ((test-univariate-polynomial-gcd-with univariate-subresultant-gcd) test-case)))

(defspec test-univariate-euclid-gcd
  (prop/for-all [test-case univariate-polynomial-gcd-test-case-generator]
                ((test-univariate-polynomial-gcd-with univariate-euclid-gcd) test-case)))

(defspec spmod 25
  (prop/for-all [p (generate-nonzero-poly 1)
                 q (generate-nonzero-poly 1)]
                (do
                  (small-primes-modular-univariate-gcd p q)
                  true)))

(defn -main
  [& args]
  #_(let [pqs  (gen/sample
              (gen/bind (gen/choose 8 12)
                        #(gen/tuple (generate-poly %)
                                    (generate-poly %)))
              256)]
    (println "benchmark add")
    (c/quick-bench (dorun (for [[p q] pqs] (a/add Zx p q)))))
  #_(let [pqs (gen/sample
             (gen/let [u (generate-poly 1)
                       v (generate-nonzero-poly 1)
                       g (generate-nonzero-poly 1)]
               [(a/mul Zx u g) (a/mul Zx v g)])
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
