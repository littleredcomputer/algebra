;; Copyright Copyright © 2017 Colin Smith. MIT License.

(ns algebra.polynomial
  (:import (clojure.lang BigInt Ratio))
  (:require [algebra :as a]
            [clojure.set :as set]
            [clojure.string :as string]))

(declare operator-table operators-known make-constant)

(def coefficient second)
(def exponents first)

;; Monomials
;;
;; We represent a monomial as a vector of integers representing
;; the exponents of the indeterminates over some ring. For example;
;; we would represent x^2 as [2], and xy^2 as [1 2], though the
;; indeterminates have no name. Polynomials are linear combinations
;; of the monomials. When these are formed, it is important that the
;; monomial vectors all contain the same number of slots, so that
;; 3x + 2y^2 would be represented as: 3*[1 0] + 2*[0 2].

(defn ^:private monomial-degree
  "Compute the degree of a monomial. This is just the sum of the exponents."
  [m]
  (reduce + m))

;; Monomial Orderings
;;
;; These orderings are in the sense of Java: x.compareTo(y), so that
;; this returns >0 if x > y, <0 if x < y, and ==0 if x = y.

(defn lex-order
  "Lex order for monomials considers the power of x, then the power of y, etc."
  [xs ys]
  {:pre (= (count xs) (count ys))}
  (compare xs ys))

(defn graded-lex-order
  ""
  [xs ys]
  {:pre (= (count xs) (count ys))}
  (let [xd (monomial-degree xs)
        yd (monomial-degree ys)]
    (if (= xd yd) (lex-order xs ys) (- xd yd))))

(defn graded-reverse-lex-order
  ""
  [xs ys]
  {:pre (= (count xs) (count ys))}
  (let [xd (monomial-degree xs)
        yd (monomial-degree ys)]
    (if (= xd yd) (compare (vec (rseq ys)) (vec (rseq xs))) (- xd yd))))

(def ^:private monomial-order graded-lex-order)
(def ^:private empty-coefficients [])

;;
;; Polynomials
;;

(defprotocol IPolynomial
  (degree [this])
  (coef [this exponents])
  (evaluate [this args]))

(defrecord Polynomial [ring arity terms]
  IPolynomial
  (degree [this]
    (if (empty? terms) -1
        (reduce + (exponents (peek terms)))))
  (coef [_ exponents]
    (if-let [s (seq (drop-while #(not= exponents (first %)) terms))]
      (second (first s))
      (a/additive-identity ring)))
  (evaluate [_ args]
    (reduce (partial a/add ring) (a/additive-identity ring)
            (for [[es c] terms]
              (reduce (partial a/mul ring) c (map #(a/exponentiation-by-squaring ring %1 %2) args es))))))

(defn ^:private polynomial-zero? [^Polynomial p] (empty? (.terms p)))
(defn ^:private polynomial-one?
  "True if p has only a constant term which is equal to the multiplicative identity in its base ring"
  [^Polynomial p]
  (let [R (.ring p)
        xs->c (.terms p)]
    (when (= (count (.terms p)) 1)
      (let [[xs c] (first (.terms p))]
        (and (every? zero? xs)
             (a/multiplicative-identity? R c))))))

(defn ^:private make-polynomial
  "Constructs a polynomial with coefficients in `ring` with the given
  `arity` (number of indeterminates), followed by a sequence
  of exponent-coefficient pairs. Each exponent should be a vector with
  length equal to the arity, with non-negative integer exponent values. To
  make 4 x^2 y + 5 x y^2, an arity 2 polynomial (since it has two
  variables, x and y), we could write the following for xc-pairs:
  [[[2 1] 4] [[1 2] 5]]."
  [ring arity xc-pairs]
  (->Polynomial ring arity
                (->> (for [[xs cs] (group-by exponents xc-pairs)
                           :let [sum-cs (reduce #(a/add ring %1 (coefficient %2)) (a/additive-identity ring) cs)]
                           :when (not (a/additive-identity? ring sum-cs))]
                       [xs sum-cs])
                     (sort-by exponents monomial-order)
                     (into empty-coefficients))))

(defn ^:private lead-term
  "Return the leading (i.e., highest degree) term of the polynomial
  p. The return value is [exponents coefficient]."
  [^Polynomial p]
  (-> p .terms peek))

(defn coefficients
  [^Polynomial p]
  (->> p .terms (map coefficient)))

(defn ^:private compatible-ring
  [^Polynomial p ^Polynomial q]
  (assert (and (= (.arity p) (.arity q))
               (= (.ring p) (.ring q))))
  (.ring p))

(defn ^:private compatible-constructor
  [^Polynomial p ^Polynomial q]
  (assert (and (= (.arity p) (.arity q))
               (= (.ring p) (.ring q))))
  (fn [xs->c] (make-polynomial (.ring p) (.arity p) xs->c)))

(defn ^:private map-coefficients
  "Map the function f over the coefficients of p, returning a new Polynomial."
  [f ^Polynomial p]
  (let [R (.ring p)]
    (->Polynomial R (.arity p) (into empty-coefficients
                                     (for [[xs c] (.terms p)
                                           :let [fc (f c)]
                                           :when (not (a/additive-identity? R fc))]
                                       [xs fc])))))

(defn ^:private polynomial-negate
  [^Polynomial p]
  (let [R (.ring p)]
    (map-coefficients #(a/negate R %) p)))

(defn ^:private polynomial-basis
  [ring arity]
  (cons (->Polynomial ring arity [[(vec (repeat arity 0)) (a/multiplicative-identity ring)]])
        (for [i (range arity)]
          (->Polynomial ring arity [[(vec (for [j (range arity)] (if (= i j) 1 0))) (a/multiplicative-identity ring)]]))))

(defn ^:private compatible
  [^Polynomial p ^Polynomial q]
  (and (= (.ring p) (.ring q))
       (= (.arity p) (.arity q))))

(defn ^:private merge-term-lists
  "Merges term lists, both assumed sorted. Terms with same exponents are
  combined via op, and discarded if the combination is the additive
  identity in the ring R."
  [ps qs op R]
  (loop [ps ps
         qs qs
         s empty-coefficients]
    (cond (empty? ps) (into s qs)
          (empty? qs) (into s ps)
          :else (let [[pxs pc] (first ps)
                      [qxs qc] (first qs)
                      o (monomial-order pxs qxs)]
                  (cond
                    (zero? o) (recur (rest ps) (rest qs)
                                     (let [sc (op R pc qc)]
                                       (if (a/additive-identity? R sc)
                                         s
                                         (conj s [pxs sc]))))
                    (< o 0) (recur (rest ps) qs (conj s [pxs pc]))
                    :else (recur ps (rest qs) (conj s [qxs qc])))))))

(defn ^:private add
  "Adds the polynomials p and q"
  [^Polynomial p ^Polynomial q]
  {:pre [(instance? Polynomial p)
         (instance? Polynomial q)
         (compatible p q)]}
  (let [R (.ring p)]
    (->Polynomial R (.arity p)
                  (merge-term-lists (.terms p) (.terms q) a/add R))))

(defn ^:private sub
  "Adds the polynomials p and q"
  [p q]
  (add p (polynomial-negate q)))

(defn ^:private scale
  "Scalar multiply p by c, where c is in the same ring as the coefficients of p"
  [c ^Polynomial p]
  {:pre [(instance? Polynomial p)
         (a/member? (.ring p) c)]}
  (map-coefficients #(a/mul (.ring p) % c) p))

(defn ^:private mul
  "Multiply polynomials p and q, and return the product."
  [^Polynomial p ^Polynomial q]
  {:pre [(instance? Polynomial p)
         (instance? Polynomial q)]}
  (cond (polynomial-zero? p) p
        (polynomial-zero? q) q
        (polynomial-one? p) q
        (polynomial-one? q) p
        :else (let [R (.ring p)]
                ((compatible-constructor p q)
                 (for [[xp cp] (.terms p)
                       [xq cq] (.terms q)]
                   [(mapv + xp xq) (a/mul R cp cq)])))))

(defn ^:private polynomial-order
  [^Polynomial p ^Polynomial q]
  {:pre [(instance? Polynomial p)
         (instance? Polynomial q)
         (= (.arity p) (.arity q))
         (= (.ring p) (.ring q))]}
  (loop [pterms (rseq (.terms p))
         qterms (rseq (.terms q))]
    (cond (nil? qterms) (if pterms 1 0)
          (nil? pterms) -1
          :else (let [[ep cp] (first pterms)
                      [eq cq] (first qterms)]
                  (let [mo (monomial-order ep eq)]
                    (if (zero? mo)
                      (let [k (compare cp cq)]
                        (if (not= k 0) k (recur (next pterms) (next qterms))))
                      mo))))))

(defn ^:private divide
  "Divide polynomial u by v, and return the pair of [quotient, remainder]
  polynomials. This assumes that the coefficients are drawn from a field,
  and so support division."
  [^Polynomial u ^Polynomial v]
  {:pre [(instance? Polynomial u)
         (instance? Polynomial v)]}
  (cond (polynomial-zero? v) (throw (IllegalArgumentException. "internal polynomial division by zero"))
        (polynomial-zero? u) [u u]
        (polynomial-one? v) [u (->Polynomial (.ring u) (.arity u) empty-coefficients)]
        :else (let [ctor (compatible-constructor u v)
                    R (.ring u)
                    [vn-exponents vn-coefficient] (lead-term v)
                    good? (fn [residues]
                            (and (not-empty residues)
                                 (every? (complement neg?) residues)))]
                (loop [quotient (ctor [])
                       remainder u]
                  ;; find a term in the remainder into which the
                  ;; lead term of the divisor can be divided.
                  (let [[r-exponents r-coefficient] (lead-term remainder)
                        residues (mapv - r-exponents vn-exponents)]
                    (if (good? residues)
                      (let [new-coefficient (a/divide R r-coefficient vn-coefficient)
                            new-term (ctor [[residues new-coefficient]])]
                        (recur (add quotient new-term)
                               (sub remainder (mul new-term v))))
                      [quotient remainder]))))))

(defprotocol IPolynomialConstructor
  (basis [this]
    "Produces the constant unit polynomial polynomial in the base ring
     followed by one linear polynomial with unit linear coefficient
     and zero constant term for each indeterminate.")
  (make-unary [this dense-coefficients]
    "In the unary case, makes a polynomial with a dense coefficient
    list (beginning with the constant term and proceeding with each
    sequential exponent)")
  (make [this xc-pairs]
    "Makes a polynomial given a (sparse) list of `[exponent-vector
    coefficient]` pairs"))

(defmacro ^:private reify-polynomial-ring
  "A macro is used because we want to optionally configure a protocol
  in the reified object, and reify itself is a macro."
  [R arity & {:keys [euclidean]}]
  `(reify
     a/Ring
     (member? [_ p#] (instance? Polynomial p#))
     (additive-identity [_] (->Polynomial ~R ~arity []))
     (additive-identity? [_ p#] (polynomial-zero? p#))
     (multiplicative-identity [_]
       (->Polynomial ~R ~arity
                     [[(vec (repeat ~arity 0)) (a/multiplicative-identity ~R)]]))
     (multiplicative-identity? [_ p#] (polynomial-one? p#))
     (add [_ p# q#] (add p# q#))
     (subtract [_ p# q#] (sub p# q#))
     (negate [_ p#] (polynomial-negate p#))
     (mul [_ p# q#] (mul p# q#))
     ~@(if euclidean
         `(a/Euclidean
           (quorem [_ p# q#] (divide p# q#))))
     a/Ordered
     (cmp [_ p# q#] (polynomial-order p# q#))
     a/Module
     (scale [_ r# p#] (scale r# p#))
     IPolynomialConstructor
     (basis [_] (polynomial-basis ~R ~arity))
     (make-unary [_ dense-coefficients#]
       (assert (= ~arity 1))
       (make-polynomial ~R 1 (map #(vector [%1] %2) (range) dense-coefficients#)))
     (make [_ xc-pairs#] (make-polynomial ~R ~arity xc-pairs#))
     Object
     (toString [_] (format "%s[%dv]" ~R ~arity))))

(defn PolynomialRing
  [coefficient-ring arity]
  (if (= arity 1)
    (reify-polynomial-ring coefficient-ring arity :euclidean true)
    (reify-polynomial-ring coefficient-ring arity)))

(defn zippel-pseudo-remainder
  "The algorithm PolyPseudoRemainder from Zippel, p.132"
  [^Polynomial u ^Polynomial v]
  {:pre [(= (.arity u) (.arity v) 1)]}
  (let [R (compatible-ring u v)
        deg-u (degree u)
        deg-v (degree v)
        δ (- deg-u deg-v)]
    (if (< deg-u deg-v) u
        (loop [w u]
          (let [k (- (degree w) (degree v))
                lcv (coefficient (lead-term v))
                lcw (coefficient (lead-term w))
                w' (sub
                    (scale lcv w)
                    (mul v (->Polynomial R 1 [[[k] lcw]])))
                k' (- (degree w') (degree v))]
            (cond (polynomial-zero? w') w'
                  (< (degree w') deg-v) (scale (a/exponentiation-by-squaring R lcv k) w')
                  (> k (inc δ)) (let [e (- k (inc δ))
                                      lcv**e (a/exponentiation-by-squaring R lcv e)]
                                  (recur (scale lcv**e w')))
                  :else (recur w')))))))

(defn classic-pseudo-remainder
  "The pseudo-remainder straight from the definition. Makes no attempt
  to control coefficient growth."
  [^Polynomial u ^Polynomial v]
  {:pre [(instance? Polynomial u)
         (instance? Polynomial v)
         (not (polynomial-zero? v))
         (= (.arity u) (.arity v) 1)]}
  (let [R (compatible-ring u v)
        deg-u (degree u)
        deg-v (degree v)
        lcv (coefficient (lead-term v))
        e (- (inc deg-u) deg-v)
        lcv**e (a/exponentiation-by-squaring R lcv e)]
    (second (divide (scale lcv**e u) v))))

(defn ^:private univariate-content
  [^Polynomial p]
  {:pre [(= (.arity p) 1)]}
  (if (polynomial-zero? p) p
      (a/euclid-gcd-seq (.ring p) (coefficients p))))

(defn univariate-primitive-part
  [^Polynomial p]
  {:pre [(= (.arity p) 1)]}
  (let [R (.ring p)
        g (univariate-content p)]
    (map-coefficients #(a/exact-quotient R % g) p)))

(defn subresultant-polynomial-remainder-sequence
  [^Polynomial u ^Polynomial v]
  (assert (= (.arity u) (.arity v) 1))
  (let [R (compatible-ring u v)
        one (a/multiplicative-identity R)
        minus-one (a/negate R one)
        δ0 (- (degree u) (degree v))
        ψ0 (if (even? δ0) minus-one one)]
    (defn step [prr pr δr ψ β]
      (let [p (map-coefficients #(a/exact-quotient R % β) (classic-pseudo-remainder prr pr))
            a (coefficient (lead-term pr))
            ψ (if (zero? δr)
                ψ ; Avoid negative exponent
                (a/exact-quotient R (a/exponentiation-by-squaring R a δr)
                                  (a/exponentiation-by-squaring R ψ (dec δr))))
            δ (- (degree pr) (degree p))
            β (a/mul R (if (even? δ) minus-one one) (a/mul R (a/exponentiation-by-squaring R ψ δ) a))]
        (if (polynomial-zero? p)
          nil
          (cons p (lazy-seq (step pr p δ ψ β))))))
    (lazy-seq (cons u (cons v (if (< δ0 0)
                                (step v u (- δ0) one ψ0)
                                (step u v δ0 one ψ0)))))))

(defn univariate-subresultant-gcd
  [u v]
  (let [R (compatible-ring u v)
        prs (if (> (degree u) (degree v))
              (subresultant-polynomial-remainder-sequence u v)
              (subresultant-polynomial-remainder-sequence v u))
        g (last prs)]
    (if (zero? (degree g))
      (->Polynomial R 1 (conj empty-coefficients [[0] (a/multiplicative-identity R)]))
      g)))

(defn univariate-euclid-gcd
  [u v]
  (if (polynomial-zero? v) u
      (recur v (univariate-primitive-part (zippel-pseudo-remainder u v)))))

(defn pseudo-remainder-sequence
  [remainder]
  (fn step [u v]
    (if (polynomial-zero? v) (list u)
        (lazy-seq (cons u (step v (remainder u v)))))))

(defn ^:private abs
  [^Polynomial p]
  (let [R (.ring p)]
    (if (a/cmp R p (a/additive-identity R))
      (polynomial-negate p)
      p)))

(defn partial-derivative
  "The partial derivative of the polynomial with respect to the
  i-th indeterminate."
  [^Polynomial p i]
  (let [R (.ring p)]
    (make-polynomial (.ring p)
                     (.arity p)
                     (for [[xs c] (.terms p)
                           :let [xi (xs i)]
                           :when (not= 0 xi)]
                       [(update xs i dec) (a/mul R xi c)]))))

(defn partial-derivatives
  "The sequence of partial derivatives of p with respect to each
  indeterminate"
  [^Polynomial p]
  (for [i (range (.arity p))]
    (partial-derivative p i)))
