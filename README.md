# Preuves
Formal verifier for mathematics demonstrations. 
Based on the description of the first order logic WITH schemas by Patrick Dehornoy (https://dehornoy.users.lmno.cnrs.fr/surveys.html, part Logique et théorie des ensembles, in french).

This tool aims to give students, and maybe professionnal mathematicians, a way to formally verify their work.
The novelty of this tool is that its inputs are given in LaTeX syntax (https://en.wikipedia.org/wiki/LaTeX).

## Installation
For now, clone my repo and run "dune build".

## Dependencies
Preuves need :

* an OCaml compiler (http://ocaml.org)
* dune, the builder of big projects in the OCaml ecosystem
* dypgen, a GLR parser generator (see my fork of dypgen on github)
* ounit2, a framework to do unit testing

The usage of opam is recommended, though i don't know what to do with dypgen (unmaintained and inaccurate since ocaml 4.08, 
due to incompatibilities with immutable strings, so i ported it to bytes in my fork)
Once a polished version will be available, i will do an opam package.

## Usage

1. Launch proof_server.exe, with a socket parameter (see the --help option)
2. Launch in parallel an instance of `nc` (netcat), connected to the socket specified as argument to proof_server.exe
3. In `nc`, just type your commands !! But be sure to end your commands with double end-of-line to send them to proof_server.exe.

## HAVE FUN !

## Contact

sylvain_kerjean "@" hotmail.com
I would be really glad to get your appreciation of my work! I did it for fun but i hope some others will try it one day.

Sincerely yours, Sylvain.
