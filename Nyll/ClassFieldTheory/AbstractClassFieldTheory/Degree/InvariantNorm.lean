/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm

/-!
# Invariant homomorphisms on relative norms

A Galois-invariant additive homomorphism sends the actual relative norm
to multiplication by the number of relative cosets. Normality is unnecessary.
-/

namespace ClassFormation

open KummerTheory CyclicCohomology
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    {B : Type*} [AddCommMonoid B]

/-- Invariant additive values turn the actual relative norm sum into its index multiple. -/
theorem invariantHom_relativeNorm (A : Rep ℤ G) (f : A.V →+ B)
    (hf : ∀ (g : G) (x : A.V), f (A.ρ g x) = f x)
    (H J : ClosedSubgroup G) (hJH : J.toSubgroup ≤ H.toSubgroup)
    [Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)]
    (x : ambientFixedAddSubgroup A J) :
    f (relativeNorm A H J hJH x).1 =
      Nat.card (H.toSubgroup ⧸ extensionSubgroup H J hJH) • f x.1 := by
  classical
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let hQ : Fintype Q := Fintype.ofFinite Q
  change f (∑ q : Q, relativeCosetAction A H J hJH x q) = _
  rw [map_sum]
  calc
    ∑ q : Q, f (relativeCosetAction A H J hJH x q) = ∑ _q : Q, f x.1 := by
      apply Finset.sum_congr rfl
      intro q _
      refine Quotient.inductionOn' q ?_
      intro g
      exact hf g.1 x.1
    _ = Nat.card Q • f x.1 := by
      rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

end ClassFormation
