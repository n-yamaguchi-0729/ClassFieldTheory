/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.OpenSubgroup
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Compact
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.DegreeFibers
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Topology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTopology

/-!
# Closed norm images and compact norm kernels

The norm preserves degree measured over the same finite constant field. Its
image in degree zero is therefore the continuous image of the compact
degree-zero subgroup of the source. The image is locally closed at the identity
and hence closed as a subgroup. Its kernel is a closed subset of the same compact
degree-zero subgroup. No reciprocity or norm-index theorem is used.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- The degree-zero part of the norm image comes from degree-zero source classes. -/
theorem norm_image_degreeZero :
    norm (k := k) (K := K) (L := L) ''
        (degreeZero (k := k) (K := L) : Set (IdeleClassGroup k L)) =
      ((norm (k := k) (K := K) (L := L)).range : Set (IdeleClassGroup k K)) ∩
        (degreeZero (k := k) (K := K) : Set (IdeleClassGroup k K)) := by
  ext c
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨MonoidHom.mem_range.mpr ⟨b, rfl⟩, ?_⟩
    change degree (k := k) (K := K) (norm (K := K) (L := L) b) = 1
    rw [degree_norm]
    exact hb
  · rintro ⟨hc, hd⟩
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hc
    refine ⟨b, ?_, rfl⟩
    change degree (k := k) (K := L) b = 1
    rw [← degree_norm (K := K)]
    exact hd

variable [Finite k] [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
    [FunctionField k L]

/-- The norm image inside degree zero is compact. -/
theorem isCompact_norm_range_inter_degreeZero :
    IsCompact (((norm (k := k) (K := K) (L := L)).range : Set (IdeleClassGroup k K)) ∩
      (degreeZero (k := k) (K := K) : Set (IdeleClassGroup k K))) := by
  rw [← norm_image_degreeZero]
  exact (isCompact_degreeZero (k := k) (K := L)).image continuous_norm

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- Preservation of degree makes the continuous class norm a proper map. -/
theorem isProperMap_norm : IsProperMap (norm (k := k) (K := K) (L := L)) := by
  have : T2Space (IdeleClassGroup k K) := t2Space
  apply isProperMap_of_comp_of_t2 continuous_norm continuous_degree
  have hcomp : degree (k := k) (K := K) ∘ norm (k := k) (K := K) (L := L) =
      degree (k := k) (K := L) := by
    funext c
    exact degree_norm c
  rw [hcomp]
  exact isProperMap_degree

/-- The actual class norm has closed image, including extensions of degree divisible
by the characteristic. -/
theorem isClosed_norm_range :
    IsClosed ((norm (k := k) (K := K) (L := L)).range : Set (IdeleClassGroup k K)) := by
  have : T2Space (IdeleClassGroup k K) := t2Space
  let N := (norm (k := k) (K := K) (L := L)).range
  let U := (degreeZero (k := k) (K := K) : Set (IdeleClassGroup k K))
  have hclosed : IsClosed ((N : Set (IdeleClassGroup k K)) ∩ U) :=
    (isCompact_norm_range_inter_degreeZero (k := k) (K := K) (L := L)).isClosed
  apply N.isClosed_of_isLocallyClosedAt N.one_mem
  refine ⟨U, isOpen_degreeZero.mem_nhds (degreeZero (k := k) (K := K)).one_mem,
    (N : Set (IdeleClassGroup k K)) ∩ U, hclosed, ?_⟩
  ext c
  exact ⟨fun h => ⟨h.1, h.2, h.1⟩, fun h => ⟨h.1, h.2.1⟩⟩

/-- Norm-one idele classes form a compact subgroup. -/
theorem isCompact_norm_ker :
    IsCompact ((norm (k := k) (K := K) (L := L)).ker : Set (IdeleClassGroup k L)) := by
  have : T2Space (IdeleClassGroup k K) := t2Space
  apply (isCompact_degreeZero (k := k) (K := L)).of_isClosed_subset
    (isClosed_singleton.preimage continuous_norm)
  intro c hc
  change degree (k := k) (K := L) c = 1
  rw [← degree_norm (K := K), hc, map_one]

/-- The topological quotient by actual norms is Hausdorff. -/
theorem normQuotient_t2Space :
    T2Space (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) := by
  have : IsClosed ((norm (k := k) (K := K) (L := L)).range : Set (IdeleClassGroup k K)) :=
    isClosed_norm_range
  have : (norm (k := k) (K := K) (L := L)).range.Normal :=
    ⟨fun a ha g => by
      simpa only [mul_comm g a, mul_assoc, mul_inv_cancel, mul_one] using ha⟩
  have : T3Space (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) :=
    QuotientGroup.instT3Space _
  exact T25Space.t2Space

end FunctionField.IdeleClassGroup
