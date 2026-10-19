/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Differentials.Local.Order
import Nyll.AlgebraicCurves.Differentials.Local.Uniformizer
import Nyll.AlgebraicCurves.FunctionFields.Rational.InstIsCurveOverRatFunc
import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry

/-!
# Integral differential coefficients on the rational function field

The general theorem for a smooth function field supplies the integral coefficient.
The rational function field's finite-type presentation is constructed here, so residue
computations do not repeat polynomial differentiation and valuation arguments.
-/

namespace AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K] [PerfectField K]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

/-- Differentiation preserves integral differential coefficients on the rational function field. -/
theorem differentialCoeff_D_mem (v : Place K (RatFunc K)) {g : RatFunc K}
    (hg : g ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) ∈ v.toValuationSubring := by
  let : IsCurveOver K (RatFunc K) := instIsCurveOverRatFunc K
  let : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors (Polynomial K))
  let : Algebra.EssFiniteType K (RatFunc K) :=
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  obtain ⟨c, hc, he⟩ :=
    exists_mem_D_eq_smul_D_of_isCurveOver v (π := v.uniformizer) v.ord_uniformizer (x := g) hg
  have hcoeff : v.differentialCoeff (KaehlerDifferential.D K (RatFunc K) g) = c :=
    v.differentialCoeff_unique (by rw [v.dCoord_eq]; exact he)
  rw [hcoeff]
  exact hc

end AlgebraicCurve.RationalFunctionField
