(ns algebra.polynomial.sparse-test
  (:require [clojure.test :refer :all]
            [algebra.polynomial :as p]
            [algebra.polynomial.sparse :refer :all]
            [algebra.polynomial.sparse :as ps]
            [algebra :as a]))

(deftest sparse-evaluation
  (is (= 8 (shnf-eval a/NativeArithmetic [::ps/pow 3 1 0] [2])))
  (is (= 9 (shnf-eval a/NativeArithmetic [::ps/pow 3 1 1] [2])))
  (is (= 16 (shnf-eval a/NativeArithmetic [::ps/pow 3 2 0] [2])))
  (is (= 17 (shnf-eval a/NativeArithmetic [::ps/pow 3 2 1] [2])))
  (is (= 7 (shnf-eval a/NativeArithmetic [::ps/pop 1
                                          [::ps/pow 1 1 0]] [6 7 8])))
  (is (= 8 (shnf-eval a/NativeArithmetic [::ps/pop 2
                                          [::ps/pow 1 1 0]] [6 7 8])))
  (is (= 16 (shnf-eval a/NativeArithmetic [::ps/pop 1 [::ps/pow 2 4 0]] [1 2 3])))
  ;; Russinoff's paper says 207. Hmmm.
  (is (= 186 (shnf-eval a/NativeArithmetic
                        [::ps/pow 3
                         [::ps/pow 1
                          [::ps/pop 1
                           [::ps/pow 2 4 0]]
                          3]
                         [::ps/pop 1
                          [::ps/pow 4 2 5]]]
                        [1 2 3])))

  (is (= 1 (->shnf (p/make [1]))))
  (is (= 99 (->shnf (p/make [99]))))
  (is (= [::ps/pow 1 1 0] (->shnf (p/make [0 1]))))
  (is (= [::ps/pow 2 1 0] (->shnf (p/make [0 0 1]))))
  (is (= [::ps/pow 1 [::ps/pow 1 0 1] 0] (->shnf (p/make [0 1 1]))))
  (is (= [::ps/pow 1 [::ps/pow 1 1 1] 1] (->shnf (p/make [1 1 1]))))
  (let [[k x y z] (p/basis a/NativeArithmetic 3)
        R (p/make a/NativeArithmetic 3 [[[4 2 0] 4]
                                        [[3 0 0] 3]
                                        [[0 0 4] 2]
                                        [[0 0 0] 5]])]
    (is (= 'foo (->shnf R)))
    )

  )

