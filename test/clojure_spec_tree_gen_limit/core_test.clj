(ns clojure-spec-tree-gen-limit.core-test
  (:require [clojure.test :refer :all]
            [lab79.clojure-spec-tree-gen-limit :refer :all]
            [clojure.spec :as s]
            [clojure.spec.test :as stest]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [clojure.pprint :refer [pprint]])
  (:import (clojure.lang ExceptionInfo)))

(doseq [x (stest/enumerate-namespace 'lab79.clojure-spec-tree-gen-limit)]
  (stest/instrument x))

(deftest test-is-keys-spec?
  (testing "should return true for a spec-name that will generate a map."
    (s/def :x/a integer?)
    (is (false? (is-keys-spec? :x/a)))
    (is (false? (is-keys-spec? :x/a)))
    (s/def :x/b keyword?)
    (is (false? (is-keys-spec? :x/b)))
    (s/def :x/keys (s/keys :req [:x/a] :opt [:x/b]))
    (is (true? (is-keys-spec? :x/keys)))
    (s/def :x/alias-keys :x/keys)
    (is (true? (is-keys-spec? :x/alias-keys)))))

(deftest test-extract-spec-keys
  (testing "should extract req and opt keys for a spec with both req and opt keys"
    (s/def :extract/map-req-opt (s/keys :req [:extract/a :extract/b] :opt [:extract/c :extract/d]))
    (let [out (extract-spec-keys :extract/map-req-opt)]
      (is (= [:extract/a :extract/b] (:req out)))
      (is (= [:extract/c :extract/d] (:opt out)))))
  (testing "should extract req and no opt keys for a spec with only req keys"
    (s/def :extract/map-req-only (s/keys :req [:extract/a :extract/b]))
    (let [out (extract-spec-keys :extract/map-req-only)]
      (is (= [:extract/a :extract/b] (:req out)))
      (is (empty? (:opt out)))))
  (testing "should extract no req and all opt keys for a spec with only opt keys"
    (s/def :extract/map-opt-only (s/keys :opt [:extract/c :extract/d]))
    (let [out (extract-spec-keys :extract/map-opt-only)]
      (is (= [:extract/c :extract/d] (:opt out)))
      (is (empty? (:req out))))))

(defn get-map-depth
  "Given a map, returns the max depth of the map.

  e.g., {:a 1} has a depth of 1.
  e.g., {:a {:b 2}} has a depth of 2.
  e.g., {:a [{:b 2}] has a depth of 2.
  e.g., {:a [{:b [{:c 2}]}]} has a depth of 3."
  [m]
  (reduce
    (fn [depth [k v]]
      (if (map? v)
        (+ depth (get-map-depth v))
        (if (vector? v)
          (->> v
               (filter map?)
               (map get-map-depth)
               (apply max)
               (+ depth))
          depth)))
    1 m))

(deftest test-gen-overrides-for-max-depth
  (testing "Working max-limit / spec topology combos"
    (s/def :x/x integer?)
    (s/def :a/friends (s/coll-of :person/b))
    (s/def :b/friends (s/coll-of :person/a))
    (s/def :person/a (s/keys :req [:x/x] :opt [:a/friends]))
    (s/def :person/b (s/keys :req [:x/x] :opt [:b/friends]))
    (doseq [max-depth (range 1 4)]
      (is (let [overrides (gen-overrides-for-max-depth :person/a max-depth)
                p (prop/for-all [person-a (s/gen :person/a overrides)]
                                (>= max-depth (get-map-depth person-a)))]
            (:result (tc/quick-check 1000 p))))))
  (testing "Violating max-limit / spec topology combos"
    (s/def :x/x integer?)
    (s/def :a/friends (s/coll-of :person/b))
    (s/def :b/friends (s/coll-of :person/a))
    (s/def :person/a (s/keys :req [:x/x :a/friends]))
    (s/def :person/b (s/keys :req [:x/x] :opt [:b/friends]))
    (is
      (thrown-with-msg?
        ExceptionInfo
        #"Impossible to generate data because a required nested map may lead to violations of the depth limit."
        (gen-overrides-for-max-depth :person/a 3)))))

(defn- select-branch
  "Given a map `m`, selects the sub-map that includes only the `path` of keys and all other parts of the map
  that include `path` as a prefix."
  [m path]
  (let [[key & rest] path
        subtree (get m key)]
    {key (if (seq rest)
           (select-branch subtree (vec rest))
           subtree)}))

(deftest test-gen-overrides-for-varying-max-depths
  (s/def :vary/int integer?)
  (s/def :vary/a (s/keys :req [:vary/int] :opt [:vary/b :vary/c]))
  (s/def :vary/b (s/keys :req [:vary/int] :opt [:vary/a]))
  (s/def :vary/c (s/keys :req [:vary/int] :opt [:vary/a]))
  (testing "Working max-limit / spec topology combos"
    (is (let [overrides (gen-overrides-for-varying-max-depths :vary/a
                                                              {[:vary/b :vary/a] 3
                                                               [:vary/c] 2})
              p (prop/for-all [person-a (s/gen :vary/a overrides)]
                              (and (>= 3 (get-map-depth (select-branch person-a [:vary/b :vary/a])))
                                   (>= 2 (get-map-depth (select-branch person-a [:vary/c])))))]
          (:result (tc/quick-check 1000 p)))))
  (testing "Fallback max depth specification"
    (is (let [overrides (gen-overrides-for-varying-max-depths :vary/a {[] 2})
              p (prop/for-all [person-a (s/gen :vary/a overrides)]
                              (>= 2 (get-map-depth person-a)))]
          (:result (tc/quick-check 1000 p)))))
  (testing "Exception because depth limits do not have full coverage of branches"
    (is (thrown-with-msg?
          ExceptionInfo
          #"Some branches do not have a max depth specified"
          (gen-overrides-for-varying-max-depths :vary/a {[:vary/b :vary/a] 3}))))
  (testing "Violating max-limit / spec topology combos"
    (s/def :vary/int integer?)
    (s/def :vary/a (s/keys :req [:vary/int :vary/b] :opt [:vary/c]))
    (s/def :vary/b (s/keys :req [:vary/int] :opt [:vary/a]))
    (s/def :vary/c (s/keys :req [:vary/int] :opt [:vary/a]))
    (is (thrown-with-msg?
          ExceptionInfo
          #"Impossible to generate data because a required nested map may lead to violations of the depth limit."
          (gen-overrides-for-varying-max-depths :vary/a {[:vary/b :vary/a] 3
                                                         [:vary/c] 2})))))