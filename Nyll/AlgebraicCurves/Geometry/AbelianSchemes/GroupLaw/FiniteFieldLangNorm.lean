/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLangPoints
import Nyll.GaloisCohomology.Cyclic.LangNormKernel

/-!
# Periodic primitives for actual Frobenius norms

A zero-norm algebraic point has a Frobenius coboundary primitive fixed by the
specified power of Frobenius. No rational-point descent is assumed here.
-/

noncomputable section

open AlgebraicGeometry

namespace GoodReductionJacobian.RelativeGroupLaw

variable (k Ω : Type) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of k))]
    (L : RelativeGroupLaw k (X ↘ Spec (CommRingCat.of k))) (hc : L.IsCommutative)
    (hX : AbelianSchemePropertyBundle k (X ↘ Spec (CommRingCat.of k)))

include hX in
/-- Zero Frobenius norm has a primitive in the actual subgroup of periodic algebraic points. -/
theorem exists_frobenius_periodic_primitive (n : ℕ) (y : L.AlgPoints hc Ω)
    (hy : ∑ i ∈ Finset.range n, (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ i • y = 0) :
    ∃ x : L.AlgPoints hc Ω,
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ n • x = x ∧
        FiniteField.frobeniusAlgEquivOfAlgebraic k Ω • x - x = y :=
  CyclicAction.exists_fixed_primitive_of_surjective_sub _
    (surjective_frobenius_sub k Ω X L hc hX) n y hy

end GoodReductionJacobian.RelativeGroupLaw
