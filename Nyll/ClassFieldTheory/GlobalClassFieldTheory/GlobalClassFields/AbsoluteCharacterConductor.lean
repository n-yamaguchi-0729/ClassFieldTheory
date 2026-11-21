/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.EmbeddedAbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteAbelianization
public import Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianCharacterConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldConstruction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibGlobalArtinNorm
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# Conductors of absolute global characters

A discrete-valued character of the absolute Galois abelianization pulls
back along the actual global Artin map. The class field of its ordinary
kernel provides a finite conjugation-free restriction coordinate and
computes the same local and full conductors.
-/

@[expose] public section

open scoped IsMulCommutative NumberField
open ClassFieldTheory FunctionField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

open Reciprocity

universe u v w

variable (K : Type u) [Field K] [NumberField K]
  {A : Type v} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [DiscreteTopology A]

/-- A geometric Artin character in the ordinary idèle-class coordinates
used to define its kernel conductor. -/
def absoluteGlobalCharacterOnIdeleClasses
    (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* A) :
    NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A :=
  χ.comp (mathlibGlobalArtin K)

/-- The full conductor of the character on the absolute Galois
abelianization is the conductor of its actual Artin pullback. -/
def absoluteGlobalCharacterConductor
    (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* A) : RayClass.Modulus K :=
  characterConductor (absoluteGlobalCharacterOnIdeleClasses K χ)

omit [IsTopologicalGroup A] in
/-- A finite-place conductor bound says that the absolute character kills
the Artin image of the one-place higher-unit group. -/
theorem absoluteGlobalCharacterConductor_finitePart_le_iff
    (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* A)
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (absoluteGlobalCharacterConductor K χ).finitePart v ≤ n ↔
      ∀ x ∈ ClassFieldTheory.rayLocalHigherUnitGroup v n,
        χ (mathlibGlobalArtin K (IdeleGroup.finitePlaceIdeleClass v x)) = 1 := by
  rw [absoluteGlobalCharacterConductor, characterConductor_finitePart]
  exact characterLocalConductor_le_iff (absoluteGlobalCharacterOnIdeleClasses K χ) v n

/-- An absolute character with a given finite restriction coordinate has
the same full conductor as that finite Galois character. -/
theorem absoluteGlobalCharacterConductor_eq_finiteStage
    (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* A)
    (E : Type w) [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (i : E →ₐ[K] SeparableClosure K) (ψ : Gal(E/K) →ₜ* A)
    (h : ∀ σ, χ σ = ψ (absoluteRestrictionOfEmbedding K E i
      (absoluteGaloisGroupAbelianizationEquivSeparable K σ))) :
    absoluteGlobalCharacterConductor K χ = abelianCharacterConductor K E ψ.toMonoidHom := by
  have hChar : absoluteGlobalCharacterOnIdeleClasses K χ =
      ψ.comp (globalNormResidueContinuousMonoidHom K E) := by
    apply ContinuousMonoidHom.ext
    intro c
    change χ (mathlibGlobalArtin K c) =
      ψ (globalNormResidueMonoidHom K E c)
    rw [h, mathlibGlobalArtin_restrictionOfEmbedding K E i c]
  rw [absoluteGlobalCharacterConductor, hChar]
  exact (abelianCharacterConductor_eq_characterConductor K E ψ).symm

/-- The class field of the actual Artin kernel furnishes a finite stage of
every discrete-valued absolute character. Restriction to this stage
recovers the character, and its determinant-norm range is exactly the
ordinary character kernel. -/
theorem exists_absoluteGlobalCharacter_finiteStage
    (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* A) :
    ∃ E : FiniteAbelianExtension K, ∃ ψ : Gal(E/K) →ₜ* A,
      (∀ σ, χ σ = ψ (absoluteRestrictionOfEmbedding K E E.1.val
        (absoluteGaloisGroupAbelianizationEquivSeparable K σ))) ∧
      Function.Injective ψ ∧
      (_root_.ideleClassNorm K E).range =
        (absoluteGlobalCharacterOnIdeleClasses K χ).toMonoidHom.ker ∧
      absoluteGlobalCharacterConductor K χ = abelianCharacterConductor K E ψ.toMonoidHom := by
  let θ := absoluteGlobalCharacterOnIdeleClasses K χ
  have hOpen : IsOpen (θ.toMonoidHom.ker : Set (NumberField.IdeleClassGroup (𝓞 K) K)) :=
    (isOpen_discrete ({1} : Set A)).preimage θ.continuous
  obtain ⟨F, hF, hAb, hNorm⟩ := exists_openSubgroupClassField_original θ.toMonoidHom.ker hOpen
  let E : FiniteAbelianExtension K := ⟨F, hF, hAb⟩
  let n := (_root_.ideleClassNorm K E).range
  have hn : n = θ.toMonoidHom.ker := hNorm
  let ψ₀ := ProCGroups.QuotientGroup.liftₜ n θ hn.le
  let e := standardNumberFieldNormResidueContinuousMulEquiv K E
  let ψ : Gal(E/K) →ₜ* A := ψ₀.comp (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
  let i : E →ₐ[K] SeparableClosure K := E.1.val
  have hψ₀ : Function.Injective ψ₀ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective n a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective n b
    have hx := ProCGroups.QuotientGroup.liftₜ_apply_mk n θ hn.le x
    have hy := ProCGroups.QuotientGroup.liftₜ_apply_mk n θ hn.le y
    change ψ₀ (QuotientGroup.mk' n x) = ψ₀ (QuotientGroup.mk' n y) at hab
    rw [hx, hy] at hab
    apply QuotientGroup.eq_iff_div_mem.mpr
    rw [hn]
    change θ (x / y) = 1
    rw [map_div, hab, div_self']
  have hψe (a : NumberField.IdeleClassGroup (𝓞 K) K ⧸ n) : ψ (e a) = ψ₀ a :=
    congrArg ψ₀ (e.symm_apply_apply a)
  have hψ (c : NumberField.IdeleClassGroup (𝓞 K) K) :
      ψ (globalNormResidueMonoidHom K E c) = θ c := by
    have hArtin : globalNormResidueMonoidHom K E c = e (QuotientGroup.mk' n c) := rfl
    exact (congrArg ψ hArtin).trans ((hψe _).trans
      (ProCGroups.QuotientGroup.liftₜ_apply_mk n θ hn.le c))
  have hStage (σ : Field.absoluteGaloisGroupAbelianization K) :
      χ σ = ψ (absoluteRestrictionOfEmbedding K E i
        (absoluteGaloisGroupAbelianizationEquivSeparable K σ)) := by
    obtain ⟨c, rfl⟩ := mathlibGlobalArtin_surjective K σ
    rw [mathlibGlobalArtin_restrictionOfEmbedding K E i c]
    exact (hψ c).symm
  exact ⟨E, ψ, hStage, hψ₀.comp e.symm.injective, hn,
    absoluteGlobalCharacterConductor_eq_finiteStage K χ E i ψ hStage⟩

section FiniteImage

variable {B : Type v} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]

/-- A finite-image character with a Hausdorff target uses the conductor of
its actual finite range, with the induced discrete topology. -/
def finiteImageAbsoluteGlobalCharacterConductor
    (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* B) (hχ : Finite χ.toMonoidHom.range) :
    RayClass.Modulus K := by
  let : Finite χ.toMonoidHom.range := hχ
  let : DiscreteTopology χ.toMonoidHom.range := Finite.instDiscreteTopology
  exact absoluteGlobalCharacterConductor K (ProCGroups.ContinuousMonoidHom.rangeRestrict χ)

/-- A continuous finite-image character, including a finite-order complex
character, factors through the finite abelian field of its Artin kernel.
Its conductor is the conductor of the actual character on that stage. -/
theorem exists_finiteImageAbsoluteGlobalCharacter_finiteStage
    (χ : Field.absoluteGaloisGroupAbelianization K →ₜ* B) (hχ : Finite χ.toMonoidHom.range) :
    ∃ E : FiniteAbelianExtension K, ∃ ψ : Gal(E/K) →ₜ* B,
      (∀ σ, χ σ = ψ (absoluteRestrictionOfEmbedding K E E.1.val
        (absoluteGaloisGroupAbelianizationEquivSeparable K σ))) ∧
      Function.Injective ψ ∧
      finiteImageAbsoluteGlobalCharacterConductor K χ hχ =
        abelianCharacterConductor K E ψ.toMonoidHom := by
  let : Finite χ.toMonoidHom.range := hχ
  let : DiscreteTopology χ.toMonoidHom.range := Finite.instDiscreteTopology
  let χ₀ := ProCGroups.ContinuousMonoidHom.rangeRestrict χ
  obtain ⟨E, ψ₀, hψ, hInj, _, hCond⟩ := exists_absoluteGlobalCharacter_finiteStage K χ₀
  let i : χ.toMonoidHom.range →ₜ* B :=
    { χ.toMonoidHom.range.subtype with continuous_toFun := continuous_subtype_val }
  let ψ := i.comp ψ₀
  refine ⟨E, ψ, fun σ => congrArg Subtype.val (hψ σ),
    Subtype.val_injective.comp hInj, hCond.trans ?_⟩
  have hKer : (abelianCharacterConductorialSubgroup K E ψ₀.toMonoidHom).1 =
      (abelianCharacterConductorialSubgroup K E ψ.toMonoidHom).1 := by
    ext c
    change ψ₀ (globalNormResidueMonoidHom K E c) = 1 ↔
      (ψ₀ (globalNormResidueMonoidHom K E c) : B) = 1
    exact ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩
  exact congrArg ConductorialSubgroup.fullConductor (Subtype.ext hKer)

omit [NumberField K] [IsTopologicalGroup B] in
/-- A finite-image absolute Galois character has finite image after
descending through the topological abelianization. -/
theorem finite_range_absoluteGaloisCharacter_abDescend
    (ρ : Field.absoluteGaloisGroup K →ₜ* B) (hρ : Finite ρ.toMonoidHom.range) :
    Finite (ProCGroups.Abelian.TopologicalAbelianization.lift ρ).toMonoidHom.range := by
  have hRange : (ProCGroups.Abelian.TopologicalAbelianization.lift ρ).toMonoidHom.range =
      ρ.toMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨σ, rfl⟩ := ProCGroups.Abelian.TopologicalAbelianization.surjective_mk
        (Field.absoluteGaloisGroup K) a
      exact ⟨σ, (ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk ρ σ).symm⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨ProCGroups.Abelian.TopologicalAbelianization.mk (Field.absoluteGaloisGroup K) σ,
        ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk ρ σ⟩
  rwa [hRange]

/-- The conductor of a finite-image absolute Galois character obtained by
descending it to the target of the actual global Artin map. -/
def finiteImageAbsoluteGaloisCharacterConductor
    (ρ : Field.absoluteGaloisGroup K →ₜ* B) (hρ : Finite ρ.toMonoidHom.range) :
    RayClass.Modulus K :=
  finiteImageAbsoluteGlobalCharacterConductor K
    (ProCGroups.Abelian.TopologicalAbelianization.lift ρ)
    (finite_range_absoluteGaloisCharacter_abDescend K ρ hρ)

/-- Restriction of absolute automorphisms to the field of the Artin kernel
gives a faithful finite stage with the same conductor. -/
theorem exists_finiteImageAbsoluteGaloisCharacter_finiteStage
    (ρ : Field.absoluteGaloisGroup K →ₜ* B) (hρ : Finite ρ.toMonoidHom.range) :
    ∃ E : FiniteAbelianExtension K, ∃ ψ : Gal(E/K) →ₜ* B,
      (∀ σ, ρ σ = ψ (absoluteRestrictionOfEmbedding K E E.1.val
        (QuotientGroup.mk (AlgEquiv.separableClosure σ)))) ∧
      Function.Injective ψ ∧
      finiteImageAbsoluteGaloisCharacterConductor K ρ hρ =
        abelianCharacterConductor K E ψ.toMonoidHom := by
  let χ := ProCGroups.Abelian.TopologicalAbelianization.lift ρ
  obtain ⟨E, ψ, hψ, hInj, hCond⟩ := exists_finiteImageAbsoluteGlobalCharacter_finiteStage K χ
    (finite_range_absoluteGaloisCharacter_abDescend K ρ hρ)
  refine ⟨E, ψ, ?_, hInj, hCond⟩
  intro σ
  have h := hψ (ProCGroups.Abelian.TopologicalAbelianization.mk (Field.absoluteGaloisGroup K) σ)
  change ρ σ = ψ (absoluteRestrictionOfEmbedding K E E.1.val
    (absoluteGaloisGroupAbelianizationEquivSeparable K (QuotientGroup.mk σ))) at h
  rw [absoluteGaloisGroupAbelianizationEquivSeparable_mk] at h
  exact h

end FiniteImage

end GlobalClassFieldTheory.GlobalClassFields
