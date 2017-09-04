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

(deftest poly-core
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
          pr (pseudo-remainder U V)]
      (is (= [(make [-2/9 0 1/3]) (make [-1/3 0 1/9 0 -5/9])] (divide U V)))
      (is (= (make [-3 0 1 0 -5]) pr)))
    ;; examples from http://www.mathworks.com/help/symbolic/mupad_ref/pdivide.html
    (let [p (make [1 1 0 1])
          q (make [1 1 3])]
      (is (= (make [10 7]) (pseudo-remainder p q))))
    (let [p (make [3 0 4])
          q (make [2 2])]
      (is (= (make [28]) (pseudo-remainder p q))))
    (is (= [(make 2 []) (make 2 [[[2 1] 1] [[1 2] 1]])]
           (divide (make 2 [[[2 1] 1] [[1 2] 1]]) (make 2 [[[1 2] 1]]))))
    (is (= [(make [1]) (make [])] (divide (make [3]) (make [3]))))
    (is (= (make [0]) (pseudo-remainder (make [7]) (make [2])))))
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
              r1 (pseudo-remainder Mx8 CRC-8-ATM)
              CRC-16-CCITT (reduce add [unit (expt x 5) (expt x 12) (expt x 16)])
              x16 (mul x8 x8)
              T (reduce add [(expt x 2) (expt x 4) (expt x 6)])
              Tx16 (mul x16 T)
              r2 (pseudo-remainder Tx16 CRC-16-CCITT)]
          (is (= (reduce add [x (expt x 5) (expt x 7)]) r1))
          (is (= (reduce add (map #(expt x %) [0 4 5 6 9 11 12])) r2))))))
  (testing "pseudo remainder sequence (Zippel p.132)"
    (let [F1 (make [-5 2 8 -3 -3 0 1 0 1])
          F2 (make [21 -9 -4 0 5 0 3])]
      (is (= [F1
              F2
              (make [-3 0 1 0 -5])
              (make [441 -225 -117])
              (make [224167500 -169966350])
              (make [-1712229591042652500])]
             ((pseudo-remainder-sequence pseudo-remainder) F1 F2)))
      (is (= [F1
              F2
              (make [-3 0 1 0 -5])
              (make [-49 25 13])
              (make [-6150 4663])
              (make [1])]
             ((pseudo-remainder-sequence #(univariate-primitive-part (pseudo-remainder %1 %2))) F1 F2)))
      ;; The values given in Zippel correspond to the definition of PRS
      ;; as typically given, not to the values generated by his algorithm,
      ;; whose coefficients grow more slowly
      (is (= [F1
              F2
              (make [-9 0 3 0 -15])
              (make [-59535 30375 15795])
              (make [-1654608338437500 1254542875143750])
              (make [12593338795500743100931141992187500])]
             ((pseudo-remainder-sequence pseudo-remainder-classic) F1 F2)))))
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
      (is (= [z2 x3 xy2z x2z2] (monomial-sort graded-lex-order)))))
  (testing "primitive part"
    (is (= (make [1 2 3 4]) (univariate-primitive-part (make [2 4 6 8]))))
    (is (= (make [2 3 4 5]) (univariate-primitive-part (make [2 3 4 5]))))))

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

(defspec add=concat+make
  (gen/let [arity (gen/choose 1 10)]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)]
                  (= (add p q) (make (.arity p) (concat (.terms p) (.terms q)))))))

(defspec p+p=2p
  (prop/for-all [^Polynomial p (gen/bind gen/nat generate-poly)]
                (= (add p p) (mul p (make-constant (.arity p) 2)))))

(defspec p-p=0
  (prop/for-all [p (gen/bind gen/nat generate-poly)]
                (polynomial-zero? (sub p p))))

(defspec pq-div-p=q
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

(defspec p*_q+r_=p*q+p*r num-tests
  (gen/let [arity gen/nat]
    (prop/for-all [p (generate-poly arity)
                   q (generate-poly arity)
                   r (generate-poly arity)]
                  (= (mul p (add q r)) (add (mul p q) (mul p r))))))

(defspec univariate-gcd-test
  (let [evenly-divides? #(polynomial-zero? (second (divide %2 %1)))]
    (prop/for-all [k (generate-nonzero-poly 1)
                   u (generate-nonzero-poly 1)
                   v (generate-nonzero-poly 1)]
                  (let [ku (mul k u)
                        kv (mul k v)
                        g (univariate-gcd ku kv)]
                    (and (evenly-divides? g ku)
                         (evenly-divides? g kv)
                         (evenly-divides? k g))))))

(defn -main
  [& args]
  (let [pqs  (gen/sample
              (gen/bind (gen/choose 8 12)
                        #(gen/tuple (generate-poly %)
                                    (generate-poly %)))
              256)]
    (println "benchmark add")
    (c/quick-bench (dorun (for [[p q] pqs] (add p q)))))
  (let [pqs (gen/sample
             (gen/let [u (generate-poly 1)
                       v (generate-nonzero-poly 1)
                       g (generate-nonzero-poly 1)]
               [(mul u g) (mul v g)])
             256)]
    (println "benchmark pr")
    (c/quick-bench (dorun (for [[p q] pqs] (pseudo-remainder p q))))))
