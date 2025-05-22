(lang dune 3.17)
(cram enable)

(name cairo_ml)

(generate_opam_files true)

(source
 (github flydexo/stark))

(authors "Flydexo <flydexo@gmail.com>")

(maintainers "Flydexo <flydexo@gmail.com>")

(license MIT)

(package
 (name cairo_ml)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends 
  ocaml
  zarith
  progress
  (sha (= 1.14)))
 (tags
  (crypto zk stark)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
