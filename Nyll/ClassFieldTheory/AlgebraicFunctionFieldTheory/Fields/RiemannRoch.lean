/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The separating-parameter scalar transfer is supplied by
Nyll/AlgebraicCurves/FunctionFields/Rational/SeparatingRationalPresentation.lean,
extracted from the following source, originally Copyright 2026 Anthropic, PBC, Apache 2.0:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.AlgebraicCurves.FunctionFields.Rational.SeparatingRationalPresentation
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Index.RiemannGenusBoundedIndexFinite
import Nyll.AlgebraicCurves.Places.Rational.RatFuncIndexOfSpecialtyFinite

/-!
# Riemann–Roch bounds independent of the chosen rational presentation

The shared genus witness used by strong approximation also controls
bounded Artin–Schreier parameter spaces. Perfectness supplies a separating
presentation internally.
-/

open AlgebraicCurve

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Supply a Riemann–Roch bound from the actual curve function field. -/
theorem exists_genusReached [PerfectField k] [Algebra.EssFiniteType k K]
    [IsCurveOver k K] [Nonempty (Place k K)]
    [FiniteDimensional k (LSpace (0 : Divisor k K))] :
    ∃ (γ : ℤ) (D₀ : Divisor k K), RiemannGenusReachedAt γ D₀ := by
  obtain ⟨ratAlgebra, hTower, hFinite, hSeparable⟩ :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := k) (F := K)
  exact exists_riemannGenusReachedAt_of_bounded
    (riemannGenusBounded_of_indexFinite
      (RationalFunctionField.indexOfSpecialtyFinite_of_ratFunc_tower k K))

end FunctionField
