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
  (mul [this x y]))

(defprotocol Field
  (divide [this x y]))

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
    Ordered
    (cmp [this x y] (compare x y))
    Field
    (divide [this x y] (/ x y))
    Object
    (toString [this] "NativeArithmetic")))

(defn exponentiation-by-squaring
  [r x e]
  (if (= e 0) (multiplicative-identity r)
              (loop [x x
                     y (multiplicative-identity r)
                     n e]
                (cond (<= n 1) (mul r x y)
                      (even? n) (recur (mul r x x) y (bit-shift-right n 1))
                      :else (recur (mul r x x) (mul r x y) (bit-shift-right (dec n) 1))))))

