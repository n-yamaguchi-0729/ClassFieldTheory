/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkLocalClassification
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin

/-! # The arithmetic finite stage of a prime-order local unit character -/

@[expose] public section

noncomputable section

open LocalFieldTheory
open scoped ValuativeRel

namespace LocalClassFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Finite local existence realizes the actual kernel of a unit character in
the original separable closure. The character is evaluated via the existing
geometric Artin map and the faithful map on its finite Galois group. -/
theorem exists_finiteLocalArtinCharacterStage {A : Type*} [CommGroup A] [Finite A]
    (χ : Kˣ →* A) (hker : IsOpen (χ.ker : Set Kˣ)) :
    ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (hE : IsAbelianGalois K E),
      let : IsAbelianGalois K E := hE
      ∃ ψ : Gal(E/K) →* A, Function.Injective ψ ∧
        ∀ a, ψ (abelianLocalArtinMap K E a) = χ a := by
  let H : ClassFieldTheory.OpenFiniteIndexSubgroup K := ⟨⟨χ.ker, hker⟩, inferInstance⟩
  let fields := shrinkFiniteAbelianFieldNormSubgroupOrderIso K
  let L : ClassFieldTheory.FiniteAbelianLocalExtension K := fields.symm H
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := L.1
      finiteDimensional := L.2.1
      isGalois := L.2.2.toIsGalois }
  let hE : IsAbelianGalois K E := L.2.2
  let : IsAbelianGalois K E := hE
  have hn : localNormSubgroup K E = χ.ker := by
    change L.normSubgroup = χ.ker
    rw [← shrinkFiniteAbelianFieldNormSubgroupOrderIso_apply K L]
    exact congrArg
      (fun J : (ClassFieldTheory.OpenFiniteIndexSubgroup K)ᵒᵈ => (OrderDual.ofDual J).1.toSubgroup)
      (fields.apply_symm_apply H)
  let π := abelianLocalArtinMonoidHom K E
  have hπ : Function.Surjective π := abelianLocalArtinMonoidHom_surjective K E
  have heng : π.ker = χ.ker := (abelianLocalArtinMonoidHom_ker K E).trans hn
  let q := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let ψ : Gal(E/K) →* A := (QuotientGroup.lift π.ker χ heng.le).comp q.symm.toMonoidHom
  have hψ (a : Kˣ) : ψ (π a) = χ a := by
    change QuotientGroup.lift π.ker χ heng.le (q.symm (q (QuotientGroup.mk' π.ker a))) = _
    rw [q.symm_apply_apply]
    rfl
  refine ⟨E, hE, ψ, (injective_iff_map_eq_one ψ).mpr ?_, ?_⟩
  · intro σ hσ
    obtain ⟨a, rfl⟩ := hπ σ
    have ha : a ∈ χ.ker := (hψ a).symm.trans hσ
    exact heng.ge ha
  · intro a
    exact (congrArg ψ (DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom K E) a)).trans (hψ a)

end LocalClassFieldTheory
