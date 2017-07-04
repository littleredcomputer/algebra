(ns algebra)

(defprotocol Ring
  (member? [this x])
  (additive-identity [this])
  (additive-identity? [this x])
  (multiplicative-identity [this])
  (multiplicative-identity? [this x])
  (negative? [this x])
  (add [this x y])
  (subtract [this x y])
  (negate [this x])
  (mul [this x y]))

(defprotocol Field
  (divide [this x y]))

(def NativeArithmetic
  (reify
    Ring
    (member? [this x] (number? x))
    (additive-identity [this] 0)
    (additive-identity? [this x] (zero? x))
    (multiplicative-identity [this] 1)
    (multiplicative-identity? [this x] (= x 1))
    (negative? [this x] (< x 0))
    (add [this x y] (+' x y))
    (subtract [this x y] (-' x y))
    (negate [this x] (-' x))
    (mul [this x y] (*' x y))
    Field
    (divide [this x y] (/ x y))
    Object
    (toString [this] "NativeArithmetic")))

