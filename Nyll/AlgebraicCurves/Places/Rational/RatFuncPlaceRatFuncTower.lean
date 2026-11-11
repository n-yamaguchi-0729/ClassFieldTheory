/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

module

public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Places.Rational.Infinity
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
public import Nyll.AlgebraicCurves.Places.Basic

/-!
# Rational Function Field nonempty place of rat Func tower
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Rational.Proofs.RationalFieldPlaceRatFuncTower

open AlgebraicCurve

theorem _root_.AlgebraicCurve.RationalFunctionField.nonempty_place_of_ratFunc_tower (K : Type*)
  [Field K]
    (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable
      (RatFunc K) F] :
    Nonempty (AlgebraicCurve.Place K F) := open scoped Classical in
  (AlgebraicCurve.Place.exists_restrict_eq (M := F)
    (AlgebraicCurve.RationalFunctionField.placeInfty K)).nonempty
end AlgebraicCurves.Places.Rational.Proofs.RationalFieldPlaceRatFuncTower
end ProofImplementation
