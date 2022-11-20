(lang dune 2.9)

(using coq 0.3)

(name coq-cypher)
(version dev)

(source
 (github cyphercert/opencypher-coq))

(homepage https://cyphercert.github.io/opencypher-coq)
(documentation https://cyphercert.github.io/opencypher-coq/toc.html)
(bug_reports https://github.com/cyphercert/opencypher-coq/issues)

(implicit_transitive_deps true)

(package
 (name coq-cypher)
 (synopsis "Open Cypher formalization")
 (description "Semantics of Open Cypher Query Language formalized in Coq")
 (depends
  (coq (and (>= 8.13.0) (< 8.16.0)))
  coq-hahn
  (coq-qcert (>= 2.2.0))
  (coq-relation-algebra (>= 1.7.7))
  ))

(generate_opam_files true)