# caml-functors

OCaml functor-style polymorphism for Clojure

I wanted to implement tagless final style of DLS embedding in Clojure (see http://okmij.org/ftp/tagless-final/tagless-typed.html) That approach uses ad hoc polymorphism heavily, typically using Haskell or OCaml as host language.

Clojure as any Lisp of course lacks these mechanisms, so I wondered if it was possible to embed OCaml functor facilities in Clojure. This projects illustrates that this is in fact possible (with very little code.)

See the core_test.clj for usage. The syntax is as close to functors as possible, the scope and resolution are pretty close. What you see is in fact almost 1:1 rendition of OCaml samples from this page: http://okmij.org/ftp/tagless-final/course2/index.html



## Usage

FIXME

## License

Copyright © 2016 Yuri Steinschreiber
