(defproject net.littleredcomputer/algebra "0.0.1"
  :description "A library for calculations involving multivariate polynomials"
  :url "http://github.com/littleredcomputer/sicmutils"
  :license {:name "MIT"
            :url "http://www.opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.8.0"]]
  :jvm-opts ["-Djava.util.logging.config.file=logging.properties"]
  :test-selectors {:default (complement :long)}
  :profiles {:test {:dependencies [[org.clojure/test.check "0.9.0"]
                                  [criterium "0.4.4"]]}

             }
  )
