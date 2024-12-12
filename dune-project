(lang dune 2.9)
(using coq 0.3)
(name ol-coq)

(generate_opam_files true)

(package
 (name ol-coq)
 (version 0.1)
 (depends
  (coq (>= 8.15)))
)
