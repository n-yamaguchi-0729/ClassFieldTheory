/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-! # Compact products inside restricted products -/

open scoped RestrictedProduct

namespace RestrictedProduct

/-- A product of compact distinguished subsets is compact in the restricted product.
This is the same construction for integral adeles and integral ideles. -/
theorem isCompact_forall_mem {ι : Type*} (R : ι → Type*)
    [∀ i, TopologicalSpace (R i)] (A : ∀ i, Set (R i)) (𝓕 : Filter ι)
    (hA : ∀ i, IsCompact (A i)) :
    IsCompact {x : Πʳ i, [R i, A i]_[𝓕] | ∀ i, x i ∈ A i} := by
  have (i : ι) : CompactSpace (A i) := isCompact_iff_compactSpace.mp (hA i)
  have hrange : Set.range (structureMap R A 𝓕) =
      {x : Πʳ i, [R i, A i]_[𝓕] | ∀ i, x i ∈ A i} := range_structureMap R A
  rw [← hrange]
  exact isCompact_range (isEmbedding_structureMap.continuous :
    Continuous (structureMap R A 𝓕))

end RestrictedProduct
