(ns algebra)

(defprotocol Ordered
  (cmp [this x y]))

(defprotocol Ring
  (member? [this x])
  (additive-identity [this])
  (additive-identity? [this x])
  (multiplicative-identity [this])
  (multiplicative-identity? [this x])
  (add [this x y])
  (subtract [this x y])
  (negate [this x])
  (mul [this x y])
  )

(defprotocol Euclidean
  (quorem [this x y]))

(defprotocol Field
  (divide [this x y]))

;; A module defines scalar multiplication (here, on the left)
(defprotocol Module
  (scale [this r x]))

(defrecord Zmod [n]
  Ring
  (member? [this x] (number? x))
  (additive-identity [this] 0)
  (additive-identity? [this x] (zero? (mod x n)))
  (multiplicative-identity [this] 1)
  (multiplicative-identity? [this x] (= (mod x n) 1))
  (add [this x y] (mod (+' x y) n))
  (subtract [this x y] (mod (-' x y) n))
  (negate [this x] (mod (-' x) n))
  (mul [this x y] (mod (*' x y) n)))

(def NativeArithmetic
  "The 'ring' of Clojure's native arithmetic (overflow-safe) operators."
  (reify
    Ring
    (member? [this x] (number? x))
    (additive-identity [this] 0)
    (additive-identity? [this x] (zero? x))
    (multiplicative-identity [this] 1)
    (multiplicative-identity? [this x] (= x 1))
    (add [this x y] (+' x y))
    (subtract [this x y] (-' x y))
    (negate [this x] (-' x))
    (mul [this x y] (*' x y))
    Euclidean
    (quorem [this x y] [(quot x y) (rem x y)])
    Ordered
    (cmp [this x y] (compare x y))
    Field
    (divide [this x y] (/ x y))
    Object
    (toString [this] "NativeArithmetic")))

(defn exponentiation-by-squaring
  [R x e]
  (cond
    (< e 0) (throw (IllegalArgumentException. "ring exponentiation to negative power"))
    (= e 0) (multiplicative-identity R)
    :else (loop [x x
                 y (multiplicative-identity R)
                 n e]
            (cond (= n 1) (mul R x y)
                  (even? n) (recur (mul R x x) y (bit-shift-right n 1))
                  :else (recur (mul R x x) (mul R x y) (bit-shift-right (dec n) 1))))))

(defn evenly-divides?
  [R u v]
  (additive-identity? R (second (quorem R v u))))

(defn reciprocal
  [R x]
  (divide R (multiplicative-identity R) x))

(defn exact-quotient
  [R u v]
  (let [[q r] (quorem R u v)]
    (assert (additive-identity? R r) (str "exact-quotient: " u " ÷ " v))
    q))

(defn euclid-gcd
  [R u v]
  (loop [u u v v]
    (if (additive-identity? R v) u
        (recur v (second (quorem R u v))))))

(defn extended-euclid
  [R u v]
  (loop [rr u
         sr (multiplicative-identity R)
         tr (additive-identity R)
         r v
         s (additive-identity R)
         t (multiplicative-identity R)]
    (if (additive-identity? R r)
      [rr sr tr]
      (let [q (first (quorem R rr r))]
        (recur r s t
               (subtract R rr (mul R q r))
               (subtract R sr (mul R q s))
               (subtract R tr (mul R q t)))))))

(defn euclid-gcd-seq
  [R as]
  (let [gcd-1 (fn [a b]
                (let [g (euclid-gcd R a b)]
                  (if (multiplicative-identity? R g) (reduced g) g)))]
    (reduce gcd-1 as)))

(defn chinese-remainder
  [R vs ms]
  (let [n (count vs)
        M (reduce (partial mul R) ms)
        Mm (mapv #(first (quorem R M %)) ms)]
    (reduce (partial add R)
            (map (partial mul R)
                 Mm
                 (for [i (range n)]
                   (let [mi (nth ms i)
                         [g s t] (extended-euclid R (nth Mm i) mi)]
                     (second (quorem R (mul R (nth vs i) s) mi))))))))
