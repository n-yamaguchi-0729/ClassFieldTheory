/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Multiplicative fixed points and additive fixed coefficients

The actual subgroup of fixed points and the fixed subgroup of its additive
representation have the same elements and action, with their group laws
related by the standard additive type tag.
-/

namespace KummerTheory

variable (G M : Type) [Group G] [TopologicalSpace G]
    [CommGroup M] [MulDistribMulAction G M]

/-- Fixed points commute with writing a multiplicative module additively. -/
def multiplicativeFixedPointsEquiv (H : ClosedSubgroup G) :
    Additive (FixedPoints.subgroup H.toSubgroup M) ≃+
      ambientFixedAddSubgroup (Rep.ofMulDistribMulAction G M) H where
  toFun x := ⟨Additive.ofMul x.toMul.1, x.toMul.2⟩
  invFun x := Additive.ofMul ⟨x.1.toMul, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end KummerTheory
