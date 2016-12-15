(ns lab79.clojure-spec-tree-gen-limit
  (:require [clojure.spec :as s]
            [clojure.spec.gen :as gen]
            [clojure.test.check.generators :refer [generator?]])
  (:import (com.sun.xml.internal.bind.v2 TODO)))

(s/def ::spec-name keyword?)
(s/def ::path (s/coll-of ::spec-name :kind vector?))
(s/def ::req (s/coll-of ::spec-name :kind vector?))
(s/def ::opt (s/coll-of ::spec-name :kind vector?))
(s/def ::map-form (s/cat :macro #{'keys}
                     :args (s/keys* :opt [::req ::opt])))
(s/def ::coll-form (s/cat :macro #{'every}
                          :spec-name ::spec-name
                          :rest (s/* any?)))
(s/def ::gen-factory (s/fspec :args (s/cat)
                              :ret generator?))

(s/fdef extract-spec-keys
        :args (s/cat :spec-name ::spec-name)
        :ret (s/keys :opt-un [::req ::opt]))
(defn extract-spec-keys
  [spec-name]
  (let [form (s/describe spec-name)
        out (s/conform ::map-form form)]
    (if (= ::s/invalid out)
      (let [out (s/conform ::coll-form form)]
        (if (= ::s/invalid out)
          (throw (ex-info "The spec should generate a map or collection of maps."
                          {:spec form})))
        (let [spec-name-for-possible-map (:spec-name out)]
          (extract-spec-keys spec-name-for-possible-map)))
      (:args out))))

(s/fdef is-keys-spec?
        :args (s/cat :spec-name ::spec-name)
        :ret boolean?)
(defn is-keys-spec?
  [spec-name]
  (let [spec (s/describe spec-name)]
    (or
      (and (coll? spec) (= 'keys (first spec)))
      (and (coll? spec) (= 'every (first spec)) (is-keys-spec? (second spec))))))

(s/fdef check-for-limit-req-violations!
        :args (s/cat :req (s/coll-of ::spec-name)
                     :rel-max-depth pos-int?
                     :curr-path ::path
                     :spec-name ::spec-name))
(defn- check-for-limit-req-violations!
  [req rel-max-depth curr-path spec-name]
  (doseq [req-spec-name req]
    (if (is-keys-spec? req-spec-name)
      (throw (ex-info "Impossible to generate data because a required nested map may lead to violations of the depth limit."
                      {:max-depth                 (+ rel-max-depth (count curr-path))
                       :root-spec-name            (first curr-path)
                       :path-to-violating-req-map (into (vec (rest curr-path)) [spec-name req-spec-name])})))))


(s/fdef gen-overrides
        :args (s/cat :curr-path ::path
                     :spec-name ::spec-name
                     :rel-max-depth pos-int?)
        :ret (s/map-of ::path ::gen-factory))
(defn- gen-overrides
  "Returns the generator overrides for use with (clojure.spec/gen spec overrides).
  This is a recursive helper function we use from the wrapper function,
  `gen-overrides-for-max-depth`.

  - `curr-path` is the spec path from the root spec (inclusive) to `spec-name` (exclusive).
  - `spec-name` is the name of the spec that we have recursed to.
  - `rel-max-depth` is the max depth of any subtree we generate rooted at `spec-name`"
  [curr-path spec-name rel-max-depth]
  (let [{:keys [req opt]} (extract-spec-keys spec-name)]
    (if (= 1 rel-max-depth)
      (do
        (check-for-limit-req-violations! req rel-max-depth curr-path spec-name)
        (let [[_ & curr-path-minus-root] curr-path
              path-to-map (conj (vec curr-path-minus-root) spec-name)
              map-spec `(s/keys :req ~req
                                :opt ~(vec (filter (complement is-keys-spec?) opt)))
              spec (if (= 'every (first (s/describe spec-name)))
                     `(s/coll-of ~map-spec)
                     map-spec)
              key (if (empty? curr-path)
                    spec-name
                    (vec path-to-map))]
          {key #(s/gen (eval spec))}))
      (->> (concat req opt)
           (filter is-keys-spec?)
           (map #(gen-overrides (conj curr-path spec-name) % (dec rel-max-depth)))
           (apply merge)))))

(s/fdef gen-overrides-for-max-depth
        :args (s/cat :root-spec-name ::spec-name
                     :max-depth pos-int?)
        :ret (s/map-of ::path ::gen-factory))
(defn gen-overrides-for-max-depth
  "Returns a map of generator factory overrides for use with
  `(clojure.spec/gen root-spec-name overrides)` where the map associates:

  1. Keys that are paths to subtrees of generated data.
  2. To values that are generator factories that return generators that
     generate trailing subtrees of leaves that will not violate the
     constraint of generating an entire tree that is an instance of
     `root-spec-name` with a depth no greater than `max-depth`."
  [root-spec-name max-depth]
  (gen-overrides [] root-spec-name max-depth))

(s/fdef gen-path-overrides
        :args (s/cat :curr-path ::path
                     :spec-name ::spec-name
                     :rel-path->rel-max-depth (s/map-of ::path pos-int?))
        :ret (s/map-of ::path ::gen-factory))
(defn- gen-path-overrides
  "Recursive helper function used from the wrapper function, `gen-overrides-for-varying-max-depths`."
  [curr-path spec-name rel-path->rel-max-depth]
  (let [{:keys [req opt]} (extract-spec-keys spec-name)]
    (if (empty? rel-path->rel-max-depth)
      (throw (ex-info "Some branches do not have a max depth specified"
                      {:path-minus-root (rest curr-path)
                       :root-spec (first curr-path)}))
      (if (= '([]) (keys rel-path->rel-max-depth))
        (let [rel-max-depth (get rel-path->rel-max-depth [])]
          (check-for-limit-req-violations! req rel-max-depth curr-path spec-name)
          (let [[_ & curr-path-minus-root] curr-path
                path-to-map (conj (vec curr-path-minus-root) spec-name)
                map-spec `(s/keys :req ~req
                                  :opt ~(vec (filter (complement is-keys-spec?) opt)))
                spec (if (= 'every (first (s/describe spec-name)))
                       `(s/coll-of ~map-spec)
                       map-spec)
                key (if (empty? curr-path)
                      spec-name
                      (vec path-to-map))]
            {key #(s/gen (eval spec))}))
        ; else
        (letfn [(next-rel-path->rel-max-depth
                  [rel-path->rel-max-depth key]
                  (let [fallback (get rel-path->rel-max-depth [])
                        next-minus-fallback (->> (dissoc rel-path->rel-max-depth [])
                                                 (filter (fn [[k v]] (= key (first k))))
                                                 (map (fn [[k v]] [(vec (rest k)) (dec v)]))
                                                 (into {}))]
                    (cond-> next-minus-fallback
                            (and (not (contains? next-minus-fallback []))
                                 (not (nil? fallback)))                   (assoc [] fallback))))]
          (->> (concat req opt)
               (filter is-keys-spec?)
               (map #(gen-path-overrides
                       (conj curr-path spec-name)
                       %
                       (next-rel-path->rel-max-depth rel-path->rel-max-depth %)))
               (apply merge)))))))

(s/fdef gen-overrides-for-varying-max-depths
        :args (s/cat :root-spec-name ::spec-name
                     :path->max-depth (s/map-of ::path pos-int?))
        :ret (s/map-of ::path ::gen-factory))
(defn gen-overrides-for-varying-max-depths
  "Similar to gen-overrides-for-max-depth, but allows you to specify different
  max-depths along different subpaths of the generated data or spec."
  [root-spec-name path->max-depth]
  (gen-path-overrides [] root-spec-name path->max-depth))