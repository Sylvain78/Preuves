(lang dune 2.2)

(package
 (name Preuves)
  (synopsis "Verification of first order demonstrations")
       (depends
         (ocaml
	    (>= 4.05))
	 (dune
	    (>= 1.9))
         (bisect_ppx	
	    (>= 1.4))
	 (dyp
	    (>= 20120619))))
(using menhir 2.1)
