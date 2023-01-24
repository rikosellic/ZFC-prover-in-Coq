# ZFC-prover-in-Coq
This is a ZFC prover embedded in Coq for teaching scenarios. More information can be found in CoqPL 2023. 

## Project Structure
ExplicitName.v : a simple string library.

ZFLib.v: formalization of ZFC and tactics.

Tutorial.v: students may use this tutorial to learn the tactics.

MathematicalInduction.v: a proof of mathematical induction.

Peano.v Peano_plus.v Peano_mult.v: a formalization of Peano arithmetic.


## How to build

This project can be built in Coq 8.15, new versions are not tested.

Run

`coq_makefile -f _CoqProject -o CoqMakefile`

and then

`make -f CoqMakefile`
