/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.StandardNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.CharacterNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Characters
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.LocalConductor
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.NormLift
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorInfinitePart
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLocalComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassRelativeKernel
public import Lean.Elab.Tactic.Omega

/-!
# Conductors of continuous discrete-valued characters

The conductor is the existing full conductor of the actual character kernel.
Its finite exponents use the same higher-unit groups as ray class theory.
The conductor of a product divides the join of the conductors; at a finite
place, unequal exponents give equality with their maximum. No unconditional
equality is asserted for a product of characters.
-/

@[expose] public section

open scoped NumberField Topology

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

open NumberField IsDedekindDomain

variable {K : Type*} {A : Type*} [Field K] [NumberField K]
    [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [DiscreteTopology A]

/-- The kernel of a discrete-valued continuous character has a defining modulus. -/
noncomputable def characterConductorialSubgroup
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) : ConductorialSubgroup K :=
  ⟨χ.toMonoidHom.ker,
    RayClass.exists_congruenceSubgroup_le_of_isOpen χ.toMonoidHom.ker
      ((isOpen_discrete ({1} : Set A)).preimage χ.continuous_toFun)⟩

/-- The full kernel conductor of a continuous discrete-valued character. -/
noncomputable def characterConductor
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) : RayClass.Modulus K :=
  (characterConductorialSubgroup χ).fullConductor

/-- The local kernel conductor, with depth zero equal to the integral units. -/
noncomputable def characterLocalConductor
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (characterConductorialSubgroup χ).narrowFiniteLocalConductorExponent v

omit [IsTopologicalGroup A] in
/-- The global finite exponent is the local higher-unit kernel conductor. -/
theorem characterConductor_finitePart
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) (v : HeightOneSpectrum (𝓞 K)) :
    (characterConductor χ).finitePart v = characterLocalConductor χ v :=
  ConductorialSubgroup.narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent
    (characterConductorialSubgroup χ) v

omit [IsTopologicalGroup A] in
/-- A full modulus bounds the character conductor exactly when its congruence
subgroup is killed by the character. -/
theorem characterConductor_le_iff
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) (m : RayClass.Modulus K) :
    characterConductor χ ≤ m ↔ m.congruenceSubgroup ≤ χ.toMonoidHom.ker :=
  ((characterConductorialSubgroup χ).isDefiningModulus_iff_fullConductor_le m).symm

omit [IsTopologicalGroup A] in
/-- Ray factorization is unique and is equivalent to the full conductor bound. -/
theorem existsUnique_rayClassCharacter_iff_conductor_le
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) (m : RayClass.Modulus K) :
    (∃! ψ : RayClass.RayClassGroup m →ₜ* A,
      ∀ c : NumberField.IdeleClassGroup (𝓞 K) K,
        ψ (QuotientGroup.mk' m.congruenceSubgroup c) = χ c) ↔
      characterConductor χ ≤ m :=
  (RayClass.existsUnique_rayClassCharacter_iff m χ).trans
    (characterConductor_le_iff χ m).symm

omit [IsTopologicalGroup A] in
/-- A character presented on the larger ray group has conductor dividing
`m` precisely when it kills the relative kernel of `Cl_n → Cl_m`. -/
theorem characterConductor_le_iff_relativeRayKernel
    {m n : RayClass.Modulus K} (hmn : m ≤ n) (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A)
    (ψ : RayClass.RayClassGroup n →ₜ* A)
    (hψ : ∀ c : NumberField.IdeleClassGroup (𝓞 K) K,
      ψ (QuotientGroup.mk' n.congruenceSubgroup c) = χ c) :
    characterConductor χ ≤ m ↔
      (ClassFieldTheory.originalRayClassModulusProjection K hmn).ker ≤ ψ.toMonoidHom.ker := by
  rw [characterConductor_le_iff, ClassFieldTheory.originalRayClassModulusProjection_ker]
  constructor
  · intro h q hq
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hq
    change ψ (QuotientGroup.mk' n.congruenceSubgroup c) = 1
    rw [hψ c]
    exact h hc
  · intro h c hc
    change χ c = 1
    rw [← hψ c]
    exact h (Subgroup.mem_map_of_mem (QuotientGroup.mk' n.congruenceSubgroup) hc)

section Norm

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] [IsTopologicalGroup A] in
/-- Pullback along the actual norm has conductor bounded by any compatible
full modulus above a bound for the base character. -/
theorem characterConductor_norm_le
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A)
    {n : RayClass.Modulus L} {m : RayClass.Modulus K}
    (h : n.NormCompatible m) (hχ : characterConductor χ ≤ m) :
    characterConductor (χ.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L)) ≤ n :=
  (characterConductor_le_iff _ n).mpr
    (h.rayClassCharacter_pullback_ker χ ((characterConductor_le_iff χ m).mp hχ))

omit [IsTopologicalGroup A] in
/-- The explicit full norm lift of the base conductor bounds the conductor
of the pullback character. -/
theorem characterConductor_norm_le_liftedModulus (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) :
    characterConductor (χ.comp (NumberField.IdeleClassGroup.normContinuousMonoidHom K L)) ≤
      RayClass.normLiftedModulus (L := L) (characterConductor χ) :=
  characterConductor_norm_le χ (RayClass.normLiftedModulus_normCompatible _) le_rfl

end Norm

omit [IsTopologicalGroup A] in
/-- A local conductor bound is equivalent to killing every higher unit at that
depth under the actual one-place insertion into the idele class group. -/
theorem characterLocalConductor_le_iff
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    characterLocalConductor χ v ≤ n ↔
      ∀ x ∈ ClassFieldTheory.rayLocalHigherUnitGroup v n,
        χ (IdeleGroup.finitePlaceIdeleClass v x) = 1 := by
  constructor
  · intro h x hx
    apply (characterConductorialSubgroup χ).narrowFiniteLocalConductorExponent_spec v
    exact ⟨x, ClassFieldTheory.rayLocalHigherUnitGroup_antitone v h hx, rfl⟩
  · intro h
    apply (characterConductorialSubgroup χ).narrowFiniteLocalConductorExponent_le v
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx

/-- The full conductor of a product divides the join of its two conductors. -/
theorem characterConductor_mul_le_sup
    (χ ψ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) :
    characterConductor (χ * ψ) ≤ characterConductor χ ⊔ characterConductor ψ := by
  apply (characterConductor_le_iff (χ * ψ) _).mpr
  intro c hc
  have hχ : χ c = 1 :=
    (characterConductor_le_iff χ _).mp le_sup_left hc
  have hψ : ψ c = 1 :=
    (characterConductor_le_iff ψ _).mp le_sup_right hc
  change χ c * ψ c = 1
  rw [hχ, hψ, one_mul]

/-- The local conductor of a product is at most the larger local conductor. -/
theorem characterLocalConductor_mul_le_max
    (χ ψ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) (v : HeightOneSpectrum (𝓞 K)) :
    characterLocalConductor (χ * ψ) v ≤
      max (characterLocalConductor χ v) (characterLocalConductor ψ v) := by
  apply (characterLocalConductor_le_iff (χ * ψ) v _).mpr
  intro x hx
  have hχ := (characterLocalConductor_le_iff χ v _).mp (le_max_left _ _) x hx
  have hψ := (characterLocalConductor_le_iff ψ v _).mp (le_max_right _ _) x hx
  change χ (IdeleGroup.finitePlaceIdeleClass v x) *
    ψ (IdeleGroup.finitePlaceIdeleClass v x) = 1
  rw [hχ, hψ, one_mul]

/-- A character of smaller local conductor cannot cancel the last nontrivial
higher-unit value of one with larger conductor. -/
theorem characterLocalConductor_mul_eq_right_of_lt
    (χ ψ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) (v : HeightOneSpectrum (𝓞 K))
    (h : characterLocalConductor χ v < characterLocalConductor ψ v) :
    characterLocalConductor (χ * ψ) v = characterLocalConductor ψ v := by
  apply le_antisymm
  · exact (characterLocalConductor_mul_le_max χ ψ v).trans_eq (max_eq_right h.le)
  · have hbound : characterLocalConductor ψ v ≤
        max (characterLocalConductor χ v) (characterLocalConductor (χ * ψ) v) := by
      apply (characterLocalConductor_le_iff ψ v _).mpr
      intro x hx
      have hχ := (characterLocalConductor_le_iff χ v _).mp (le_max_left _ _) x hx
      have hprod :=
        (characterLocalConductor_le_iff (χ * ψ) v _).mp (le_max_right _ _) x hx
      change χ (IdeleGroup.finitePlaceIdeleClass v x) *
        ψ (IdeleGroup.finitePlaceIdeleClass v x) = 1 at hprod
      rw [hχ, one_mul] at hprod
      exact hprod
    omega

/-- For unequal local conductors, the conductor of the product is their maximum. -/
theorem characterLocalConductor_mul_eq_max_of_ne
    (χ ψ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) (v : HeightOneSpectrum (𝓞 K))
    (h : characterLocalConductor χ v ≠ characterLocalConductor ψ v) :
    characterLocalConductor (χ * ψ) v =
      max (characterLocalConductor χ v) (characterLocalConductor ψ v) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [max_eq_right hlt.le]
    exact characterLocalConductor_mul_eq_right_of_lt χ ψ v hlt
  · rw [mul_comm χ ψ, max_eq_left hgt.le]
    exact characterLocalConductor_mul_eq_right_of_lt ψ χ v hgt

omit [IsTopologicalGroup A] in
/-- Postcomposition may lower the conductor, and always preserves this upper bound. -/
theorem characterConductor_postcompose_le
    {B : Type*} [CommGroup B] [TopologicalSpace B]
    [IsTopologicalGroup B] [DiscreteTopology B]
    (f : A →ₜ* B) (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) :
    characterConductor (f.comp χ) ≤ characterConductor χ := by
  apply (characterConductor_le_iff (f.comp χ) _).mpr
  intro c hc
  have hχ : χ c = 1 := (characterConductor_le_iff χ _).mp le_rfl hc
  change f (χ c) = 1
  rw [hχ, map_one]

end GlobalClassFieldTheory.GlobalClassFields
