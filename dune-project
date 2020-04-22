(lang dune 1.9)

(package
 (name Preuves)
  (synopsis "Verification of first order demonstrations")
       (depends
         (ocaml
	    (>= 4.05))
	 (dune
	    (>= 1.9))
         (bisect_ppx	
	    (>= 1.4))))
(using menhir 2.1)
