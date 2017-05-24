# Forward Error Correction Case Study for COUNT2017

## Files

* ecc.c: C implementation of replication codes, together with CBMC model
* ecc.v: Coq implementation of CBMC model, together with proof of system spec.

## Prequisites

The case study uses:

* [cbmc 5.7](http://www.cprover.org/cbmc/)
* [Coq 8.5](https://coq.inria.fr/coq-85) (which is now slightly outdated)
* [Ssreflect 1.6](http://math-comp.github.io/math-comp) (an extension to Coq)

## BUILD

* ecc.c: 

`> cbmc ecc.c`

* ecc.v

`> coqc ecc.v`

* or simply type 

`> make`

in the project directory.
