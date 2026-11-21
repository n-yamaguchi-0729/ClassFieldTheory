/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiltered

/-!
# Conductors of finite-image local characters

The same principal-unit threshold defines the conductor of an open norm
subgroup, a finite-image character, and a character carried by the local
Weil reciprocity equivalence.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFieldTower.Martinet.Shafarevich LocalFieldTheory ProCGroups.Abelian
open RamificationTheory.LocalField

universe u v w

/-- A continuous character with finite image in a T₁ target has open kernel. -/
theorem isOpen_ker_of_finite_range
    {G : Type w} {A : Type v} [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]
    [T1Space A] (χ : G →ₜ* A) (hχ : (Set.range χ).Finite) :
    IsOpen (χ.toMonoidHom.ker : Set G) := by
  let S := Set.range χ \ {1}
  have hS : IsClosed S := (hχ.subset Set.sdiff_subset).isClosed
  have heq : (χ.toMonoidHom.ker : Set G) = χ ⁻¹' Sᶜ := by
    ext x
    change χ x = 1 ↔ ¬ (χ x ∈ Set.range χ ∧ χ x ≠ 1)
    simp only [Set.mem_range_self, true_and, not_not]
  rw [heq]
  exact hS.isOpen_compl.preimage χ.continuous

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable {A : Type v} [CommGroup A] [TopologicalSpace A] [T1Space A]

/-- The conductor of an actual continuous character with finite image. -/
def finiteImageLocalCharacterConductorExponent
    (χ : Kˣ →ₜ* A) (hχ : (Set.range χ).Finite) : ℕ :=
  localConductorExponentOfOpenSubgroup K χ.toMonoidHom.ker (isOpen_ker_of_finite_range χ hχ)

/-- A finite-image character is trivial on a principal-unit step exactly
from its conductor onward. -/
theorem finiteImageLocalCharacterConductorExponent_le_iff
    (χ : Kˣ →ₜ* A) (hχ : (Set.range χ).Finite) (n : ℕ) :
    finiteImageLocalCharacterConductorExponent K χ hχ ≤ n ↔
      fieldPrincipalUnits K n ≤ χ.toMonoidHom.ker :=
  localConductorExponentOfOpenSubgroup_le_iff K χ.toMonoidHom.ker
    (isOpen_ker_of_finite_range χ hχ) n

/-- The actual kernel of a finite-image absolute character is open normal. -/
def absoluteLocalCharacterKernel
    (ψ : localAbsoluteAbelianProfinite K →ₜ* A) (hψ : (Set.range ψ).Finite) :
    OpenNormalSubgroup (localAbsoluteAbelianProfinite K) where
  toSubgroup := ψ.toMonoidHom.ker
  isOpen' := isOpen_ker_of_finite_range ψ hψ
  isNormal' := inferInstance

omit [T1Space A] in
/-- Pullback along the absolute Artin map preserves finiteness of the image. -/
theorem absoluteLocalCharacter_comp_artin_finite
    (ψ : localAbsoluteAbelianProfinite K →ₜ* A) (hψ : (Set.range ψ).Finite) :
    (Set.range (ψ.comp (separableAbsoluteLocalArtinMap K))).Finite := by
  apply hψ.subset
  rintro _ ⟨x, rfl⟩
  exact ⟨separableAbsoluteLocalArtinMap K x, rfl⟩

/-- The Artin pullback of a finite-image absolute character has the same
conductor as the finite field cut out by the actual kernel. -/
theorem absoluteLocalCharacter_conductor_eq_localConductorExponent
    (ψ : localAbsoluteAbelianProfinite K →ₜ* A) (hψ : (Set.range ψ).Finite) :
    finiteImageLocalCharacterConductorExponent K (ψ.comp (separableAbsoluteLocalArtinMap K))
        (absoluteLocalCharacter_comp_artin_finite K ψ hψ) =
      localConductorExponent K
        (absoluteFiniteQuotientField K (absoluteLocalCharacterKernel K ψ hψ)) := by
  let N := absoluteLocalCharacterKernel K ψ hψ
  let E := absoluteFiniteQuotientField K N
  let χ := ψ.comp (separableAbsoluteLocalArtinMap K)
  have hχ : χ.toMonoidHom.ker = localNormSubgroup K E := by
    rw [← absoluteFiniteArtinMap_ker K N]
    ext x
    change ψ (separableAbsoluteLocalArtinMap K x) = 1 ↔ absoluteFiniteArtinMap K N x = 1
    rw [← separableAbsoluteLocalArtinMap_finiteProjection K N x]
    exact (QuotientGroup.eq_one_iff (N := N.toSubgroup) _).symm
  apply le_antisymm
  · apply (finiteImageLocalCharacterConductorExponent_le_iff K χ _ _).mpr
    rw [hχ]
    exact localConductorExponent_spec K E
  · apply (localConductorExponent_le_iff K E _).mpr
    rw [← hχ]
    exact (finiteImageLocalCharacterConductorExponent_le_iff K χ _ _).mp le_rfl

/-- Pull a continuous Weil character back through the ordinary Artin isomorphism. -/
def localWeilCharacterOnFieldUnits (ψ : localWeilGroup K →ₜ* A) : Kˣ →ₜ* A :=
  (TopologicalAbelianization.lift ψ).comp
    (ContinuousMonoidHom.toContinuousMonoidHom (localWeilReciprocity K))

/-- Pullback through Weil reciprocity preserves finite image. -/
theorem localWeilCharacterOnFieldUnits_finite
    (ψ : localWeilGroup K →ₜ* A) (hψ : (Set.range ψ).Finite) :
    (Set.range (localWeilCharacterOnFieldUnits K ψ)).Finite := by
  apply hψ.subset
  rintro _ ⟨x, rfl⟩
  obtain ⟨w, hw⟩ := TopologicalAbelianization.surjective_mk (localWeilGroup K)
    (localWeilReciprocity K x)
  exact ⟨w, congrArg (TopologicalAbelianization.lift ψ) hw⟩

/-- The conductor of the actual Weil character uses the same unit threshold. -/
def localWeilCharacterConductorExponent (ψ : localWeilGroup K →ₜ* A)
    (hψ : (Set.range ψ).Finite) : ℕ :=
  finiteImageLocalCharacterConductorExponent K (localWeilCharacterOnFieldUnits K ψ)
    (localWeilCharacterOnFieldUnits_finite K ψ hψ)

/-- The Weil character is trivial on the classes of the absolute upper step
exactly when its conductor is at most the corresponding principal-unit depth. -/
theorem localWeilCharacterConductorExponent_le_iff
    (ψ : localWeilGroup K →ₜ* A) (hψ : (Set.range ψ).Finite) (t : ℝ) (ht : 0 ≤ t) :
    localWeilCharacterConductorExponent K ψ hψ ≤ ⌈t⌉₊ ↔
      ((separableLocalUpperRamificationGroup K t).map
        (localAbsoluteAbelianizationQuotientMap K)).comap
        (localWeilAbelianizationToAbsolute K).toMonoidHom ≤
        (TopologicalAbelianization.lift ψ).toMonoidHom.ker := by
  rw [localWeilCharacterConductorExponent, finiteImageLocalCharacterConductorExponent_le_iff,
    ← separableAbsoluteLocalArtinMap_fieldPrincipalUnits K t ht]
  constructor
  · intro h w hw
    obtain ⟨x, hx, he⟩ := hw
    have heq : localWeilReciprocity K x = w :=
      localWeilAbelianizationToAbsolute_injective K
        ((localWeilAbelianizationToAbsolute_localWeilReciprocity K x).trans he)
    rw [← heq]
    exact h hx
  · intro h x hx
    change localWeilReciprocity K x ∈ (TopologicalAbelianization.lift ψ).toMonoidHom.ker
    apply h
    change localWeilAbelianizationToAbsolute K (localWeilReciprocity K x) ∈
      (fieldPrincipalUnits K ⌈t⌉₊).map (separableAbsoluteLocalArtinMap K).toMonoidHom
    rw [localWeilAbelianizationToAbsolute_localWeilReciprocity K]
    exact ⟨x, hx, rfl⟩

end LocalClassFieldTheory
