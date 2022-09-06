(lang dune 3.4)
(name myowntt)
(authors "AradArbel10")
(maintainers "AradArbel10")

(generate_opam_files true)

; (source (github username/reponame))
; (license LICENSE)
; (documentation https://url/to/documentation)

(package
  (name myowntt)
  (synopsis "A dependent type elaborator w/ NbE and glued evaluation.")
  (depends ocaml dune menhir angstrom)
  (tags
    (topics "to describe" your project)))

(using menhir 2.1)