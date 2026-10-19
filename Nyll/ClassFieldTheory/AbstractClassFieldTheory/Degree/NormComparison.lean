/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm

/-!
# Reindexing actual relative norms through coefficient homomorphisms

A proved comparison of individual coset actions determines the entire norm.
The sum is reindexed by an actual equivalence of its finite indexing types.
-/

namespace ClassFormation

open KummerTheory CyclicCohomology
open scoped BigOperators

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
    {B S : Type*} [AddCommMonoid B] [Fintype S]

/-- A coset-action comparison identifies the actual norm with a mapped finite sum. -/
theorem relativeNorm_eq_mapped_sum (A : Rep ℤ G)
    (H J : ClosedSubgroup G) (hJH : J.toSubgroup ≤ H.toSubgroup)
    [Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)]
    (x : ambientFixedAddSubgroup A J) (i : B →+ A.V)
    (e : (H.toSubgroup ⧸ extensionSubgroup H J hJH) ≃ S) (f : S → B)
    (hf : ∀ q, relativeCosetAction A H J hJH x q = i (f (e q))) :
    (relativeNorm A H J hJH x).1 = i (∑ s, f s) := by
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let hQ : Fintype Q := Fintype.ofFinite Q
  change (∑ q : Q, relativeCosetAction A H J hJH x q) = i (∑ s, f s)
  rw [map_sum]
  exact (Finset.sum_congr rfl (fun q _ => hf q)).trans
    (e.sum_comp (fun s => i (f s)))

end ClassFormation
