/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.MathlibFieldClassification
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue
import Nyll.GaloisCohomology.ArtinSchreier.CharacterClasses
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Realizing local prime cyclic characters by Artin–Schreier generators

The actual local existence theorem supplies the field with a prescribed
character kernel as norm group. Local reciprocity transports the character
to its faithful Galois character. Additive Hilbert 90 then supplies an actual
Artin–Schreier generator with the prescribed root differences.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory ArtinSchreierTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- Every continuous order-p-valued local character is realized by an actual
Artin–Schreier generator, with its original character kernel as norm group. -/
theorem exists_artinSchreier_extension_of_character (p : ℕ) [Fact p.Prime] [CharP K p]
    (χ : Kˣ →ₜ* Multiplicative (ZMod p)) :
    ∃ (E : ClassFieldTheory.FiniteAbelianLocalExtension K) (a : K) (β : E.val),
      β ^ p - β = algebraMap K E.val a ∧ Algebra.adjoin K {β} = ⊤ ∧
      (∀ u : Kˣ, abelianLocalArtinMonoidHom K E.val u β - β = ((χ u).toAdd.val : E.val)) ∧
      localNormSubgroup K E.val = χ.toMonoidHom.ker := by
  have hopen : IsOpen (χ.toMonoidHom.ker : Set Kˣ) :=
    (isOpen_discrete ({1} : Set (Multiplicative (ZMod p)))).preimage χ.continuous
  let H : ClassFieldTheory.OpenFiniteIndexSubgroup K :=
    ⟨χ.toMonoidHom.ker, hopen, inferInstance⟩
  let classFields := finiteAbelianFieldNormSubgroupOrderIso K
  let E : ClassFieldTheory.FiniteAbelianLocalExtension K := classFields.symm H
  have hNorm : localNormSubgroup K E.val = χ.toMonoidHom.ker := by
    change E.normSubgroup = H.val
    rw [← finiteAbelianFieldNormSubgroupOrderIso_apply K E]
    exact congrArg Subtype.val (classFields.apply_symm_apply H)
  let π : Kˣ →* Gal(E.val/K) := abelianLocalArtinMonoidHom K E.val
  have hπ : Function.Surjective π := abelianLocalArtinMonoidHom_surjective K E.val
  have hker : π.ker = χ.toMonoidHom.ker :=
    (abelianLocalArtinMonoidHom_ker K E.val).trans hNorm
  let q : Kˣ ⧸ π.ker →* Multiplicative (ZMod p) :=
    QuotientGroup.lift π.ker χ.toMonoidHom hker.le
  let e : Kˣ ⧸ π.ker ≃* Gal(E.val/K) :=
    QuotientGroup.quotientKerEquivOfSurjective π hπ
  let ψ : Gal(E.val/K) →* Multiplicative (ZMod p) := q.comp e.symm.toMonoidHom
  have hψπ (u : Kˣ) : ψ (π u) = χ u := by
    have he : e (QuotientGroup.mk' π.ker u) = π u := rfl
    change q (e.symm (π u)) = χ u
    rw [← he, e.symm_apply_apply]
    rfl
  have hψinj : Function.Injective ψ := by
    apply (injective_iff_map_eq_one ψ).mpr
    intro σ hσ
    obtain ⟨u, rfl⟩ := hπ σ
    have hu : u ∈ χ.toMonoidHom.ker := (hψπ u).symm.trans hσ
    exact hker.ge hu
  let ψc : Gal(E.val/K) →ₜ* Multiplicative (ZMod p) :=
    { ψ with continuous_toFun := continuous_of_discreteTopology }
  have hEchar : CharP E.val p := (Algebra.charP_iff K E.val p).mp inferInstance
  obtain ⟨a, β, hβ, hchar⟩ := exists_rootCharacter_eq p ψc
  have hgen : Algebra.adjoin K {β} = ⊤ := by
    let M : IntermediateField K E.val := IntermediateField.adjoin K {β}
    have hfix : M.fixingSubgroup = ⊥ := by
      apply eq_bot_iff.mpr
      intro σ hσ
      apply hψinj
      rw [map_one]
      have hβfixed : σ β = β :=
        (IntermediateField.mem_fixingSubgroup_iff M σ).mp hσ β
          (IntermediateField.subset_adjoin K {β} (Set.mem_singleton β))
      change ψc σ = 1
      rw [← hchar]
      change (rootCharacter p E.val a β hβ σ).toAdd = (0 : ZMod p)
      apply (ZMod.castHom (dvd_refl p) E.val).injective
      rw [rootCharacter_cast, hβfixed, sub_self, map_zero]
    have hM : M = ⊤ := by
      rw [← IsGalois.fixedField_fixingSubgroup M, hfix, IntermediateField.fixedField_bot]
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := K) β)]
    exact congrArg IntermediateField.toSubalgebra hM
  refine ⟨E, a, β, hβ, hgen, ?_, hNorm⟩
  intro u
  have h := rootCharacter_cast p E.val a β hβ (π u)
  rw [hchar] at h
  change (ZMod.castHom (dvd_refl p) E.val) (ψ (π u)).toAdd = _ at h
  rw [hψπ] at h
  simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using h.symm

end LocalClassFieldTheory
