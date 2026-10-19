/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Residues.RationalSimplePoles
import Nyll.AlgebraicCurves.Places.Rational.RatFuncTraceLocalResiduePlaceInftyXPowEqZero
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
import Nyll.AlgebraicCurves.Differentials.Residues.Basic

/-!
# Rational Function Field trace local Residue finite Place add trace local Residue place
Infty eq zero
-/

section ProofImplementation

open _root_.AlgebraicCurves.Differentials.Residues.Proofs
open RationalSimplePoles.AlgebraicCurve (
  dX)
open RationalSimplePoles.AlgebraicCurve (
  ordDifferentialWellDefined_ratFunc_of_perfectField)
open RationalSimplePoles.AlgebraicCurve (
  kaehlerResidueTermKFam_simplePole_pair_sum)
open RationalSimplePoles.AlgebraicCurve (
  p1PrincipalPartAtom)

namespace AlgebraicCurve.RationalFunctionField

open _root_.Polynomial

theorem trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero
    (K : Type*) [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    {p c : K[X]} (hmon : p.Monic) (hp : Irreducible p) (hc : c.degree < p.degree) :
    Algebra.trace K (AlgebraicCurve.RationalFunctionField.finitePlace K hp).ResidueField
        ((AlgebraicCurve.RationalFunctionField.finitePlace K hp).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.finitePlace K hp).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K))))
      + Algebra.trace K (AlgebraicCurve.RationalFunctionField.placeInfty K).ResidueField
        ((AlgebraicCurve.RationalFunctionField.placeInfty K).localResidue
          (algebraMap K[X] (RatFunc K) c / algebraMap K[X] (RatFunc K) p
            * (AlgebraicCurve.RationalFunctionField.placeInfty K).differentialCoeff
                (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)))) = 0 := by
  let Rfam : ∀ v : AlgebraicCurve.Place K (RatFunc K),
      v.CanonicalLocalResidueDataK :=
    fun v => AlgebraicCurve.HasCanonicalLocalResidueKStar.dataKStar v
  have h :=
    kaehlerResidueTermKFam_simplePole_pair_sum
      Rfam
      (ordDifferentialWellDefined_ratFunc_of_perfectField K)
      hmon hp hc
  simpa only [AlgebraicCurve.kaehlerResidueTermKFam_apply,
    AlgebraicCurve.diagonalHom_apply,
    AlgebraicCurve.Place.localResidue,
    Rfam,
    dX,
    p1PrincipalPartAtom,
    pow_one] using h

end AlgebraicCurve.RationalFunctionField
end ProofImplementation
