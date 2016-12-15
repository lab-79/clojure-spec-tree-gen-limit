# clojure-spec-tree-gen-limit

A Clojure library designed to help limit the depth of maps generated by clojure.spec/keys specs.

## What problem does this solve?

This solves the problem that can arise when using `test.check generators` based on `clojure.spec` definitions,
in which for the default generators derived from specs, there are no bounds to generating maps, so that
maps can grown in an unbounded way. As you generate more data with `(clojure.spec.gen/generate ...)` or
`(clojure.spec.gen/sample ...)`, each subsequent generated value becomes larger over time in the form of larger
sets, vectors, maps, etc. The result is it can either (a) take a long time to generate lots of large data or
(b) cause a Garbage Collection exception because the large amounts of data results in issues with GC. This
becomes an issue if you are trying to generate bootstrapped data quickly or are trying to run fast tests.

For example, consider the following simple specs:

```clojure
(s/def ::id #{:a})
(s/def :a/friend :person/b)
(s/def :b/friend :person/a)
(s/def :person/a (s/keys :opt [::id :a/friend]))
(s/def :person/b (s/keys :opt [::id :b/friend]))
```

Using `(clojure.spec.gen/generate (clojure.spec/gen :person/a))` with the above simple specs could result in
generated data that can grow in an unbounded way like the following:
 
```clojure
{:a/friend
  {:b/friend
    {:a/friend
      {:b/friend
        {:a/friend
          {:b/friend ...}}}}}}
```

Thankfully, we can leverage the [optional `overrides` argument to `(clojure.spec/gen spec overrides)`](
https://clojure.github.io/clojure/branch-master/clojure.spec-api.html#clojure.spec/gen)
that allows us to override the generator at a given spec path to generate a different subtrees than the
kinds generated by the default generator derived from the spec associated with that subtree.

In essence, this library allow you to bound the depth of trees generated by a given generator. It does
so by creating `overrides` that define generators at the edges of the map rooted at a spec in such a way
as to stop generating further subtrees at those edges.

In the example above, this would look like:

```clojure
(let [max-depth 2
      overrides (gen-overrides-for-max-depth :person/a max-depth)]
  (gen/sample (s/gen :person/a overrides)))
```

Given the overrides, the largest data that would be generated in a sample would look like:

```clojure
{::id :a ; depth of 1
 :a/friend
   {::id :a ; depth of 2
   }}
```

## Usage

```clojure
(require '[clojure.spec :as s])
(require '[clojure.spec.gen :as gen])

(s/def :x/x integer?)
(s/def :a/friends (s/coll-of :person/b))
(s/def :b/friends (s/coll-of :person/a))
(s/def :person/a (s/keys :req [:x/x] :opt [:a/friends]))
(s/def :person/b (s/keys :req [:x/x] :opt [:b/friends]))
(let [max-depth 2
      overrides (gen-overrides-for-max-depth :person/a max-depth)
      generator (s/gen :person/a overrides)]
  (gen/sample generator 4))
```

This will generate a sample of 4 maps conforming to the spec `:person/a`, but
will not generate a single map with a depth greater than the max depth of `2` 

```clojure
=> ({:x/x -1,
     :a/friends
     [#:x{:x -1}
      #:x{:x -1}
      #:x{:x -1}
      #:x{:x 0}
      #:x{:x -1}
      #:x{:x 0}
      #:x{:x -1}
      #:x{:x -1}
      #:x{:x 0}
      #:x{:x 0}
      #:x{:x 0}
      #:x{:x -1}
      #:x{:x -1}]}
    #:x{:x -1}
    #:x{:x 0}
    {:x/x -2,
     :a/friends
     [#:x{:x -1}
      #:x{:x -1}
      #:x{:x 1}
      #:x{:x -2}
      #:x{:x 0}
      #:x{:x -1}
      #:x{:x 2}
      #:x{:x 2}
      #:x{:x 0}
      #:x{:x -2}
      #:x{:x 2}
      #:x{:x -3}
      #:x{:x -1}
      #:x{:x -3}]})
```

In the above generated data set:

- `{:x/x -1}` has depth `1`.
- `{:x/x -2, :a/friends [{:x/x -1}, ...]}` has depth `2`.

Notice that data generation with the overrides above would never generate something like

`{:x/x 1 :a/friends [{:x/x 1 :b/friends [{:x/x 1}]}]}`

, which has a depth of `3`.

Sometimes you may need to specify max depths depending what path in a possible map spec is taken.
In this case, you can use `gen-overrides-for-varying-max-depths`.

In the following example, we constrain our generated data such that any branches that follow the path
[:vary/a :vary/b] don't have a tree depth greater than 3, and any branches that follow the path
[:vary/c] don't have a tree depth greater than 2, as measured from the root of the map / tree.

```clojure
(s/def :vary/int integer?)
(s/def :vary/a (s/keys :req [:vary/int] :opt [:vary/b :vary/c]))
(s/def :vary/b (s/keys :req [:vary/int] :opt [:vary/a]))
(s/def :vary/c (s/keys :req [:vary/int] :opt [:vary/a]))
(let [overrides (gen-overrides-for-varying-max-depths :vary/a
                                                              {[:vary/b :vary/a] 3
                                                               [:vary/c] 2})
      generator (s/gen :vary/a overrides)]
  (gen/sample generator 4))
```

This will generate a sample of 4 maps conforming to the spec `:vary/a`, but
will not generate a single map with a depth that violates the max depths specified above:

```clojure
=> (#:vary{:int -1}
    #:vary{:int 0}
    #:vary{:int -1, :b #:vary{:int -1}, :c #:vary{:int -2}}
    #:vary{:int -2,
           :c #:vary{:int -4},
           :b #:vary{:int -3, :a #:vary{:int 2}}})
```

## License

The MIT License (MIT) Copyright © 2016 Lab79, Inc.

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.