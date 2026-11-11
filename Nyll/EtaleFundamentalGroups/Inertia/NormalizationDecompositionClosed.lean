/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
public import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationGaloisInvariant
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.MulAction

/-!
# Closed images of original normalization decomposition groups

The stabilizer of an actual normalization prime is closed for the original
Krull topology. This follows from openness of the coefficient stabilizers:
preserving the prime is the intersection of the closed coefficient-membership
conditions. Compactness of the Galois group then makes its image under every
continuous homomorphism closed in a Hausdorff target.

The resulting closed subgroup retains the literal range of the original
normalization-decomposition inclusion. In particular, it applies to the actual
field-source fundamental-group map and its arithmetic quotient compositions.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w z

private theorem idealStabilizer_isClosed_of_openFixedSets
    {B : Type u} {G : Type v} [CommRing B] [Group G] [MulSemiringAction G B]
    [TopologicalSpace G] [IsTopologicalGroup G] (Q : Ideal B)
    (hopen : ∀ b : B, IsOpen (fun g : G => g • b = b)) :
    IsClosed (MulAction.stabilizer G Q : Set G) := by
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : ContinuousSMul G B := continuousSMul_iff_stabilizer_isOpen.mpr hopen
  have hset : (MulAction.stabilizer G Q : Set G) =
      ⋂ b : B, {g : G | g • b ∈ Q ↔ b ∈ Q} := by
    ext g
    rw [Set.mem_iInter]
    change (g • Q = Q) ↔ ∀ b : B, g • b ∈ Q ↔ b ∈ Q
    constructor
    · intro hg b
      have h : g • b ∈ g • Q ↔ b ∈ Q := Ideal.smul_mem_pointwise_smul_iff
      rwa [hg] at h
    · intro hg
      ext b
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
      have h : b ∈ Q ↔ g⁻¹ • b ∈ Q := by
        simpa only [smul_inv_smul] using hg (g⁻¹ • b)
      exact h.symm
  rw [hset]
  apply isClosed_iInter
  intro b
  have hcont : Continuous (fun g : G => g • b) :=
    continuous_id.smul continuous_const
  exact (isClosed_discrete {c : B | c ∈ Q ↔ b ∈ Q}).preimage hcont

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L]

/-- The original normalization-prime stabilizer is closed in the Krull topology. -/
theorem normalizationDecomposition_isClosed [Algebra.IsAlgebraic K L]
    (Q : Ideal (normalizationCommAlgCat A L)) :
    IsClosed (MulAction.stabilizer Gal(L/K) Q : Set Gal(L/K)) :=
  idealStabilizer_isClosed_of_openFixedSets Q
    (normalizationCommAlg_fixedSet_isOpen_krull A K L)

variable [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L))
  {P : Type z} [Group P] [TopologicalSpace P] (q : Gal(L/K) →ₜ* P)

/-- The literal original decomposition image is compact under any continuous group map. -/
theorem normalizationDecompositionImage_isCompact :
    IsCompact (((q.toMonoidHom.comp
      (normalizationDecompositionInclusion A K L Q)).range : Subgroup P) : Set P) := by
  have hset : (((q.toMonoidHom.comp
        (normalizationDecompositionInclusion A K L Q)).range : Subgroup P) : Set P) =
      q '' (MulAction.stabilizer Gal(L/K) Q : Set Gal(L/K)) := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d.val, d.property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  rw [hset]
  exact (normalizationDecomposition_isClosed A K L Q).isCompact.image q.continuous_toFun

/-- The closed subgroup is the exact image of the native decomposition inclusion. -/
def normalizationDecompositionImageClosedSubgroup [T2Space P] : ClosedSubgroup P where
  toSubgroup := (q.toMonoidHom.comp (normalizationDecompositionInclusion A K L Q)).range
  isClosed' := (normalizationDecompositionImage_isCompact A K L Q q).isClosed

end EtaleFundamentalGroups.Inertia
