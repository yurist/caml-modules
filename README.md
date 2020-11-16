# caml-functors

OCaml functor-style polymorphism for Clojure

I wanted to implement tagless final style of DLS embedding in Clojure (see http://okmij.org/ftp/tagless-final/tagless-typed.html) That approach uses ad hoc polymorphism heavily, typically using Haskell or OCaml as host language.

Clojure as any Lisp of course lacks these mechanisms, so I wondered if it was possible to embed OCaml functor facilities in Clojure. This projects illustrates that this is in fact possible (with very little code.)

See the core_test.clj for usage. The syntax is as close to functors as possible, the scope and resolution are pretty close. What you see is in fact almost 1:1 rendition of OCaml samples from this page: http://okmij.org/ftp/tagless-final/course2/index.html

## Why would it be interesting?

Besides me proving my Clojure macro-fu, this little project may have a couple of things of value:

- Demonstrating how variable scope can be manipulated using macros. That was a pretty interesting excercize, and it proved once more how powerful Lisp is. The `eval-in` function and the macros it uses provide late binding environment and the scope modeled after OCaml. It shows that not only can one define their custom syntax in Lisp using macros, but also do custom variable scoping - essentially creating a *very* different language.
- I like Clojure more than OCaml, and would much prefer using it for complex data structure manipulation. But in certain areas of computer science, specifically static code analysis, lots of sample implementations are in OCaml. Having the functors implemented in Clojure makes rewriting OCaml code in Clojure fairly straightforward.


## License

EPL-1.0

Copyright © 2016 Yuri Steinschreiber
