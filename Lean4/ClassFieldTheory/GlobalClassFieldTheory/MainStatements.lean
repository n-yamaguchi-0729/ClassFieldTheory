import GlobalClassFieldTheory.Reciprocity
import GlobalClassFieldTheory.GlobalClassFields
import GlobalClassFieldTheory.IdealClassFieldTheory
import KroneckerWeber.RationalCyclotomicArithmeticReciprocity

/-!
# Main statements of global class field theory

This is the compact public entry point for the main global class field
theory chain developed in this library.  It exports the semantic APIs
for:

* the arithmetic cyclotomic product formula and its descent to idèle
  classes;
* the surjective `ZHat`-valued class-formation valuation and its
  concrete valuation data;
* arithmetic global norm residue as a `ContinuousMulEquiv`;
* the finite abelian class-field correspondence, ray class fields,
  conductors, ramification support, and the rational cyclotomic
  realization;
* the big and small Hilbert class fields;
* the norm-defined ideal Artin exact sequence and unramified
  decomposition law; and
* actual integral and fractional ideal principalization in the small
  Hilbert class field.

The declarations themselves retain their semantic owner modules.
This file introduces no aliases and no weakened restatements.
-/
