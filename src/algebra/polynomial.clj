;; Copyright Copyright © 2017 Colin Smith. MIT License.

(ns algebra.polynomial
  (:import (clojure.lang BigInt Ratio)
    #_(algebra Ring)
           )
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
;; this returns 1 if x > y, -1 if x < y, and 0 if x = y.

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

(declare evaluate)

(deftype Polynomial [ring arity xs->c]
  Object
  (equals [_ b]
    (and (instance? Polynomial b)
         (let [^Polynomial bp b]
           (and (= arity (.arity bp))
                (= xs->c (.xs->c bp))))))
  (toString [_]
    (let [n 10
          c (count xs->c)]
      (str "( "
           ring
           " a"
           arity
           " "
           (string/join ";"
                        (take n (for [[k v] xs->c]
                                  (str v "*" (clojure.string/join "," k)))))
           (if (> c n) (format " ...and %d more terms" (- c n)))
           ")"))))

(defn polynomial-zero? [^Polynomial p] (empty? (.xs->c p)))
(defn polynomial-one?
  "True if p has only a constant term which is equal to the multiplicative identity in its base ring"
  [^Polynomial p]
  (let [R (.ring p)
        xs->c (.xs->c p)]
    (when (= (count (.xs->c p)) 1)
      (let [[xs c] (first (.xs->c p))]
        (and (every? zero? xs)
             (a/multiplicative-identity? R c))))))
(defn polynomial-zero-like [^Polynomial p] (->Polynomial (.ring p) (.arity p) empty-coefficients))
(defn polynomial-one-like [^Polynomial p]
  (let [R (.ring p)
        a (.arity p)]
    (->Polynomial R a [[(vec (repeat a 0)) (a/multiplicative-identity R)]])))

(defn make
  "When called with two arguments, the first is the arity
  (number of indeterminates) of the polynomial followed by a sequence
  of exponent-coefficient pairs. Each exponent should be a vector with
  length equal to the arity, with integer exponent values. To
  make 4 x^2 y + 5 x y^2, an arity 2 polynomial (since it has two
  variables, x and y), we could write the following for xc-pairs:
  [[[2 1] 4] [[1 2] 5]]

  When called with one argument, the sequence is interpreted as a
  dense sequence of coefficients of an arity-1 (univariate)
  polynomial. The coefficients begin with the constant term and
  proceed to each higher power of the indeterminate. For example, x^2
  - 1 can be constructed by (make -1 0 1)."
  ([ring arity xc-pairs]
   (Polynomial. ring arity
                (->> (for [[xs cs] (group-by exponents xc-pairs)
                           :let [sum-cs (reduce #(a/add ring %1 (coefficient %2)) (a/additive-identity ring) cs)]
                           :when (not (a/additive-identity? ring sum-cs))]
                       [xs sum-cs])
                     (sort-by exponents monomial-order)
                     (into empty-coefficients))))
  ([arity xc-pairs]
   (make a/NativeArithmetic arity xc-pairs))
  ([dense-coefficients]
   (make 1 (zipmap (map vector (iterate inc 0)) dense-coefficients))))

(defn ^:private lead-term
  "Return the leading (i.e., highest degree) term of the polynomial
  p. The return value is [exponents coefficient]."
  [^Polynomial p]
  (-> p .xs->c peek))

(defn degree
  [p]
  (if (polynomial-zero? p) -1
                           (->> p lead-term exponents (reduce +))))

(defn monomial?
  [^Polynomial p]
  (-> p .xs->c count (= 1)))

(defn coefficients
  [^Polynomial p]
  (->> p .xs->c (map coefficient)))

(defn compatible-arity
  [^Polynomial p ^Polynomial q]
  (assert (and (= (.arity p) (.arity q))
               (= (.ring p) (.ring q))))
  (.arity p))

(defn compatible-constructor
  [^Polynomial p ^Polynomial q]
  (assert (and (= (.arity p) (.arity q))
               (= (.ring p) (.ring q))))
  (fn [xs->c] (make (.ring p) (.arity p) xs->c)))

(defn map-coefficients
  "Map the function f over the coefficients of p, returning a new Polynomial."
  [f ^Polynomial p]
  (let [R (.ring p)]
    (Polynomial. R (.arity p) (into empty-coefficients
                                    (for [[xs c] (.xs->c p)
                                          :let [fc (f c)]
                                          :when (not (a/additive-identity? R fc))]
                                      [xs fc])))))

(defn map-exponents
  "Map the function f over the exponents of each monomial in p,
  returning a new Polynomial."
  [f ^Polynomial p]
  (make (.ring p) (.arity p) (for [[xs c] (.xs->c p)]
                               [(f xs) c])))

(defn polynomial-negate
  [^Polynomial p]
  (let [R (.ring p)]
    (map-coefficients #(a/negate R %) p)))

;; this doesn't mention the ring, so maybe we should get rid of it
(defn make-constant
  "Return a constant polynomial of the given arity in the ring of native arithmetic."
  [arity c]
  (->Polynomial a/NativeArithmetic
                arity
                (if (zero? c) empty-coefficients
                              (conj empty-coefficients [(vec (repeat arity 0)) c]))))

(defn basis
  [ring arity]
  (for [i (range arity)]
    (->Polynomial ring arity [[(vec (for [j (range (inc arity))] (if (= i j) (a/multiplicative-identity ring) (a/additive-identity ring))))]])))

(defn add
  "Adds the polynomials p and q"
  [^Polynomial p ^Polynomial q]
  {:pre [(instance? Polynomial p)
         (instance? Polynomial q)]}
  (cond (polynomial-zero? p) q
        (polynomial-zero? q) p
        :else ((compatible-constructor p q) (concat (.xs->c p) (.xs->c q)))))

(defn sub
  "Subtract the polynomial q from the polynomial p."
  [^Polynomial p ^Polynomial q]
  {:pre [(instance? Polynomial p)
         (instance? Polynomial q)]}
  (cond (polynomial-zero? p) (polynomial-negate q)
        (polynomial-zero? q) p
        :else (let [R (.ring p)]
                ((compatible-constructor p q)
                  (concat (.xs->c p) (for [[xs c] (.xs->c q)]
                                       [xs (a/negate R c)]))))))

(defn scale
  "Scalar multiply p by c, where c is in the same ring as the coefficients of p"
  [c ^Polynomial p]
  {:pre [(instance? Polynomial p)
         (a/member? (.ring p) c)]}
  (map-coefficients #(a/mul (.ring p) c %) p))

(defn mul
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
                  (for [[xp cp] (.xs->c p)
                        [xq cq] (.xs->c q)]
                    [(mapv + xp xq) (a/mul R cp cq)])))))

(defn PolynomialRing
  [coefficient-ring arity]
  (reify
    a/Ring
    (member? [this p] (instance? Polynomial p))
    (additive-identity [this] (->Polynomial coefficient-ring arity []))
    (additive-identity? [this p] (polynomial-zero? p))
    (multiplicative-identity [this] (->Polynomial coefficient-ring arity [[(vec (repeat arity 0)) (a/multiplicative-identity coefficient-ring)]]))
    (multiplicative-identity? [this p] (polynomial-one? p))
    (negative? [this p] (->> p lead-term coefficient (a/negative? coefficient-ring)))
    (add [this p q] (add p q))
    (subtract [this p q] (sub p q))
    (negate [this p] (polynomial-negate p))
    (mul [this p q]
      (if (and (a/member? coefficient-ring p)
               (a/member? this q))
        (scale p q)
        (mul p q)))
    Object
    (toString [this] (format "%s[%dv]" coefficient-ring arity))))

(defn raise-arity
  "The opposite of lower-arity."
  [^Polynomial p]
  {:pre [(instance? Polynomial p)
         (= (.arity p) 1)]}
  (let [terms (for [[x ^Polynomial q] (.xs->c p)
                    [ys c] (.xs->c q)]
                [(into x ys) c])
        ^Polynomial ltc (coefficient (lead-term p))]
    (make (.ring ltc) (inc (.arity ltc)) terms)))

(defn lower-arity
  "Given a nonzero polynomial of arity A > 1, return an equivalent polynomial
  of arity 1 whose coefficients are polynomials of arity A-1."
  [^Polynomial p]
  {:pre [(instance? Polynomial p)
         (> (.arity p) 1)
         ;; XXX is this qualification needed (below, not zero)
         (not (polynomial-zero? p))]}
  ;; XXX observation:
  ;; XXX we often create polynomials of "one lower arity"
  ;; which are EFFECTIVELY UNIVARIATE. When this happens,
  ;; we should notice.
  ;; (but univariate in which variable? is it really that
  ;; common that it's the first one?)
  (let [R (.ring p)
        A (.arity p)]
    (->> p
         .xs->c
         (group-by #(-> % exponents first))
         (map (fn [[x cs]]
                [[x] (make (dec A) (for [[xs c] cs]
                                     [(subvec xs 1) c]))]))
         (make (PolynomialRing R (dec A)) 1))))

(defn ^:private evaluate-1
  "Evaluates a univariate polynomial p at x."
  [^Polynomial p x]
  (assert (= (.arity p) 1))
  (let [R (.ring p)]
    (loop [xs->c (.xs->c p)
           result (a/additive-identity R)
           x**e (a/multiplicative-identity R)
           e 0]
      (if-let [[[e'] c] (first xs->c)]
        ;; XXX slow exponentiation below
        (let [x**e' (reduce #(a/mul R %2 %1) x**e (repeat (- e' e) x))]
          (recur (next xs->c)
                 ;; question: should we define the order of multiplication
                 ;; in a polynomial?
                 (a/add R result (a/mul R c x**e'))
                 x**e'
                 e'))
        result))))

(defn evaluate
  "Evaluates a multivariate polynomial p at xs."
  [^Polynomial p xs]
  {:pre [(instance? Polynomial p)]}
  ;; XXX shouldn't we throw if nil xs? Or do we still want to consider
  ;; partial application of polynomials? (I bet not.)
  (cond (nil? xs) p
        (polynomial-zero? p) (a/additive-identity (.ring p))
        (= (.arity p) 1) (evaluate-1 p (first xs))
        :else (let [L (evaluate-1 (lower-arity p) (first xs))]
                ;; XXX does this check still make sense?
                (if (instance? Polynomial L)
                  (recur L (next xs))
                  L))))

(defn divide
  "Divide polynomial u by v, and return the pair of [quotient, remainder]
  polynomials. This assumes that the coefficients are drawn from a field,
  and so support division."
  [u v]
  {:pre [(instance? Polynomial u)
         (instance? Polynomial v)]}
  (cond (polynomial-zero? v) (throw (IllegalArgumentException. "internal polynomial division by zero"))
        (polynomial-zero? u) [u u]
        (polynomial-one? v) [u (polynomial-zero-like u)]
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

(defn pseudo-remainder
  "Compute the pseudo-remainder of univariate polynomials p and
  q. Fractions won't appear in the result; instead the divisor is
  multiplied by the leading coefficient of the dividend before
  quotient terms are generated so that division will not result in
  fractions. Only the remainder is returned, together with the
  integerizing factor needed to make this happen. Similar in spirit to
  Knuth's algorithm 4.6.1R, except we don't multiply the remainder
  through during gaps in the remainder. Since you don't know up front
  how many times the integerizing multiplication will be done, we also
  return the number d for which d * u = q * v + r."
  [^Polynomial u ^Polynomial v]
  {:pre [(instance? Polynomial u)
         (instance? Polynomial v)
         (not (polynomial-zero? v))
         (= (.arity u) (.arity v) 1)]}
  (let [ctor (compatible-constructor u v)
        R (.ring u)
        a (compatible-arity u v)
        [vn-exponents vn-coefficient] (lead-term v)
        *vn (partial scale vn-coefficient)
        n (reduce + vn-exponents)]
    (loop [remainder u d 0]
      (let [m (degree remainder)
            c (-> remainder lead-term coefficient)]
        (if (< m n)
          [remainder d]
          (recur (sub (*vn remainder)
                      (mul v (ctor [[[(- m n)] c]])))
                 (inc d)))))))

(defn evenly-divide
  "Divides the polynomial u by the polynomial v. Throws an IllegalStateException
  if the division leaves a remainder. Otherwise returns the quotient."
  [u v]
  {:pre [(instance? Polynomial u)
         (instance? Polynomial v)]}
  (let [[q r] (divide u v)]
    (when-not (polynomial-zero? r)
      (throw (IllegalStateException. (str "expected even division left a remainder!" u " / " v " r " r))))
    q))

(defn abs
  [p]
  (let [R (.ring p)]
    (if (->> p lead-term coefficient (a/negative? R))
      (polynomial-negate p)
      p)))

(defn expt
  "Raise the polynomial p to the (integer) power n."
  [^Polynomial p n]
  (when-not (and (integer? n) (>= n 0))
    (throw (ArithmeticException.
             (str "can't raise poly to " n))))
  (cond (polynomial-one? p) p
        (polynomial-zero? p) (if (zero? n)
                               (throw (ArithmeticException. "poly 0^0"))
                               p)
        (zero? n) (polynomial-one-like p)
        :else (loop [x p c n a (polynomial-one-like p)]
                (if (zero? c) a
                              (if (even? c)
                                (recur (mul x x) (quot c 2) a)
                                (recur x (dec c) (mul x a)))))))



(defn partial-derivative
  "The partial derivative of the polynomial with respect to the
  i-th indeterminate."
  [^Polynomial p i]
  (let [R (.ring p)]
    (make (.ring p)
          (.arity p)
          (for [[xs c] (.xs->c p)
                :let [xi (xs i)]
                :when (not= 0 xi)]
            [(update xs i dec) (a/mul R xi c)]))))

(defn partial-derivatives
  "The sequence of partial derivatives of p with respect to each
  indeterminate"
  [^Polynomial p]
  (for [i (range (.arity p))]
    (partial-derivative p i)))

;; The operator-table represents the operations that can be understood
;; from the point of view of a polynomial over a commutative ring. The
;; functions take polynomial inputs and return polynomials.

;  this stuff belongs near the simplifier library.
;(def ^:private operator-table
;  {'+ #(reduce g/add %&)
;   '- (fn [arg & args]
;        (if (some? args) (g/sub arg (reduce g/add args)) (g/negate arg)))
;   '* #(reduce g/mul %&)
;   'negate negate
;   'expt g/expt
;   'square #(mul % %)
;   'cube #(mul % (mul % %))
;   ;;`'g/gcd gcd
;   })
;
;(def ^:private operators-known (into #{} (keys operator-table)))
;
;(deftype PolynomialAnalyzer []
;  a/ICanonicalize
;  (expression-> [this expr cont] (a/expression-> this expr cont compare))
;  (expression-> [this expr cont v-compare]
;    ;; Convert an expression into Flat Polynomial canonical form. The
;    ;; expression should be an unwrapped expression, i.e., not an instance
;    ;; of the Expression type, nor should subexpressions contain type
;    ;; information. This kind of simplification proceeds purely
;    ;; symbolically over the known Flat Polynomial operations; other
;    ;; operations outside the arithmetic available in polynomials over
;    ;; commutative rings should be factored out by an expression analyzer
;    ;; before we get here. The result is a Polynomial object representing
;    ;; the polynomial structure of the input over the unknowns.
;    (let [expression-vars (sort v-compare (set/difference (x/variables-in expr) operators-known))
;          variables (zipmap expression-vars (a/new-variables this (count expression-vars)))]
;      (-> expr (x/walk-expression variables operator-table) (cont expression-vars))))
;  (->expression [this p vars]
;    ;; This is the output stage of Flat Polynomial canonical form simplification.
;    ;; The input is a Polynomial object, and the output is an expression
;    ;; representing the evaluation of that polynomial over the
;    ;; indeterminates extracted from the expression at the start of this
;    ;; process.
;    (if (instance? Polynomial p)
;      (let [^Polynomial p p]
;        (reduce
;         sym/add 0
;         (map (fn [[xs c]]
;                (sym/mul c
;                         (reduce sym/mul 1 (map (fn [exponent var]
;                                                  (sym/expt var exponent))
;                                                xs vars))))
;              (->> p .xs->c (sort-by exponents #(monomial-order %2 %1))))))
;      p))
;  (known-operation? [_ o] (operator-table o))
;  (new-variables [_ arity] (for [a (range arity)]
;                             (make arity [[(mapv #(if (= % a) 1 0) (range arity)) 1]]))))
;
;(defmethod g/add [::polynomial ::polynomial] [a b] (add a b))
;(defmethod g/mul [::polynomial ::polynomial] [a b] (mul a b))
;(defmethod g/sub [::polynomial ::polynomial] [a b] (sub a b))
;(defmethod g/exact-divide [::polynomial ::polynomial] [p q] (evenly-divide p q))
;(defmethod g/square [::polynomial] [a] (mul a a))
;
;(doseq [t [Long BigInt BigInteger Double Ratio]]
;  (defmethod g/mul
;    [t ::polynomial]
;    [c p]
;    (map-coefficients #(g/* c %) p))
;  (defmethod g/mul
;    [::polynomial t]
;    [p c]
;    (map-coefficients #(g/* % c) p))
;  (defmethod g/add
;    [t ::polynomial]
;    [c ^Polynomial p]
;    (add (make-constant (.arity p) c) p))
;  (defmethod g/add
;    [::polynomial t]
;    [^Polynomial p c]
;    (add p (make-constant (.arity p) c)))
;  (defmethod g/sub
;    [t ::polynomial]
;    [c ^Polynomial p]
;    (sub (make-constant (.arity p) c) p))
;  (defmethod g/sub
;    [::polynomial t]
;    [^Polynomial p c]
;    (sub p (make-constant (.arity p) c)))
;  (defmethod g/div
;    [::polynomial t]
;    [p c]
;    (map-coefficients #(g/divide % c) p)))
;
;(defmethod g/expt [::polynomial Integer] [b x] (expt b x))
;(defmethod g/expt [::polynomial Long] [b x] (expt b x))
;(defmethod g/negate [::polynomial] [a] (negate a))
