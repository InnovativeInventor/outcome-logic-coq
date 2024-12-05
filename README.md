# outcome logic in coq

OCaml version: 5.2.0

Coq version: 8.19.0

dependencies
---
1. `ctrees` (branch `jfp`, last tested with commit
[61428e]([url](https://github.com/vellvm/ctrees/commit/61428ec4dbc0bb82f91176e54f99bef52f9fd417)))

```
git clone git@github.com:vellvm/ctrees.git
cd ctrees
git checkout jfp
opam install .
```

(We recommend creating a new `opam` switch for this)

building
---
```
dune build
```
or
```
make -f CoqMakefile
```
