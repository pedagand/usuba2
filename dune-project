(lang dune 3.13)

(name usuba2)

(generate_opam_files true)

(using menhir 3.0)

(map_workspace_root false)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name usuba2)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml   
  menhir
  (alcotest :with-test)
  (fmt :with-test)
  )
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
