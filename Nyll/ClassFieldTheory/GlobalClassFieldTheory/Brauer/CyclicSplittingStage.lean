/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldConstruction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

/-! # Local degrees in the class field of a cyclic idele class character -/

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations HilbertRamification
open GlobalClassFieldTheory.GlobalClassFields GlobalClassFieldTheory.Reciprocity
open scoped NumberField

namespace ClassFieldTheory.Brauer

/-- A discrete cyclic idele class character factors faithfully through arithmetic
reciprocity for its actual finite Galois class field. In particular, the order of
any finite one-place character value divides the actual completed degree. -/
theorem exists_cyclicStage_of_ideleClassCharacter
    (K : Type*) [Field K] [NumberField K] {A : Type*}
    [Group A] [IsCyclic A] [TopologicalSpace A] [DiscreteTopology A]
    (χ : NumberField.IdeleClassGroup (𝓞 K) K →ₜ* A) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
      ∃ hab : IsAbelianGalois K E,
      letI : NumberField E := NumberField.of_module_finite K E
      letI := hab
      IsCyclic Gal(E/K) ∧ ∃ ψ : Gal(E/K) →* A,
        Function.Injective ψ ∧ (∀ c, ψ (arithmeticGlobalNormResidueMonoidHom K E c) = χ c) ∧
        ∀ (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ),
          orderOf (χ (IdeleGroup.finitePlaceIdeleClass v a)) ∣
            Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) v)
              (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v) := by
  have hOpen : IsOpen (χ.toMonoidHom.ker : Set (NumberField.IdeleClassGroup (𝓞 K) K)) := by
    rw [MonoidHom.coe_ker]
    exact (isOpen_discrete ({1} : Set A)).preimage χ.continuous
  obtain ⟨F, hF, hAb, hNorm⟩ := exists_openSubgroupClassField_original χ.toMonoidHom.ker hOpen
  let : FiniteDimensional K F := hF
  let : IsAbelianGalois K F := hAb
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) := { toIntermediateField := F }
  let : NumberField E := NumberField.of_module_finite K E
  let hab : IsAbelianGalois K E := hAb
  let : IsAbelianGalois K E := hab
  let e : Gal(E/K) ≃* χ.toMonoidHom.range :=
    (arithmeticGlobalReciprocityContinuousMulEquiv K E).toMulEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq hNorm).trans
        (QuotientGroup.quotientKerEquivRange χ.toMonoidHom))
  let ψ : Gal(E/K) →* A := χ.toMonoidHom.range.subtype.comp e.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have heval (c : NumberField.IdeleClassGroup (𝓞 K) K) :
      ψ (arithmeticGlobalNormResidueMonoidHom K E c) = χ c := by
    change ((QuotientGroup.quotientKerEquivRange χ.toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hNorm
        (arithmeticGlobalReciprocityContinuousMulEquiv K E
          (arithmeticGlobalNormResidueMonoidHom K E c)))) : A) = χ c
    rw [arithmeticGlobalReciprocityContinuousMulEquiv_globalNormResidue]; rfl
  refine ⟨E, hab, isCyclic_of_injective ψ hψ, ψ, hψ, heval, ?_⟩
  intro v a
  rw [← heval, orderOf_injective ψ hψ]
  have hlocal := DFunLike.congr_fun
    (arithmeticGlobalNormResidueMonoidHom_comp_finitePlaceIdeleClass K E v) a
  rw [MonoidHom.comp_apply] at hlocal
  rw [hlocal, arithmeticChosenFinitePlaceArtinMonoidHom_apply, orderOf_inv]
  let g := chosenFinitePlaceArtinMonoidHom (K := K) (L := E) v a
  have hg : g ∈ finitePlaceDecompositionGroup (K := K) (L := E) v := by
    rw [← chosenFinitePlaceArtinMonoidHom_range]
    exact ⟨a, rfl⟩
  let σ : finitePlaceDecompositionGroup (K := K) (L := E) v := ⟨g, hg⟩
  let eD := decompositionGroupEquivAlgebraicLocalizationAut (HeightOneSpectrum.adicAbv K v)
    (RayClass.adicAbv_isNontrivial v) (chosenFinitePlaceExtension (L := E) v)
  change orderOf g ∣ _
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr eD.toEquiv,
    show orderOf g = orderOf σ from Subgroup.orderOf_coe σ]
  exact orderOf_dvd_natCard σ

end ClassFieldTheory.Brauer
