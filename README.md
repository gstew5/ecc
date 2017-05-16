# Forward Error Correction Case Study for COUNT2017

## Files

* ecc.c: C implementation of replication codes, together with CBMC model
* ecc.v: Coq implementation of CBMC model, together with proof of system spec.

## Prequisites

The case study uses:

* cbmc 5.7
* Coq 8.5pl1 (which is now slightly outdated)

## BUILD

* ecc.c: 

`> cbmc ecc.c`

* ecc.v

`> coqc ecc.v`

* or simply type 

`> make`

in the project directory.
