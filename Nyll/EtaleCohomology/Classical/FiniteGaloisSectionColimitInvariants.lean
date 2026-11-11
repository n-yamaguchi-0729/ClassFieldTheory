/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitAction
public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitFaithful
public import Mathlib.RepresentationTheory.Invariants
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient

/-!
# Actual global sections as absolute Galois invariants

Finite-stage sections embed in the geometric section colimit. An
absolute-Galois-invariant section is therefore already invariant at
its finite Galois stage and descends by actual sheaf descent.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

variable (K : Type u) [Field K]
variable (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})

/-- The actual map from base sections into geometric sections. -/
def finiteGaloisBaseToColimit :
    (F.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) : AddCommGrpCat.{u}) ⟶
      (finiteGaloisSectionColimit K F : AddCommGrpCat.{u}) :=
  F.obj.map (finiteEtaleCoverBaseMap (Spec (.of K))
    (FiniteEtale.mk (ξ K (⊥ : FiniteGaloisIntermediateField K (AlgebraicClosure K))))).op ≫
      finiteGaloisSectionColimitι K F ⊥

/-- The geometric-section map is actual restriction followed by inclusion at any stage. -/
theorem finiteGaloisBaseToColimit_eq_stage
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    finiteGaloisBaseToColimit K F =
      F.obj.map (finiteEtaleCoverBaseMap (Spec (.of K))
        (FiniteEtale.mk (ξ K E))).op ≫ finiteGaloisSectionColimitι K F E := by
  let h : (⊥ : FiniteGaloisIntermediateField K (AlgebraicClosure K)) ⟶ E :=
    homOfLE bot_le
  have hb : (finiteGaloisEtaleDiagram K).map h.op ≫
      finiteEtaleCoverBaseMap (Spec (.of K)) (FiniteEtale.mk
        (ξ K (⊥ : FiniteGaloisIntermediateField K (AlgebraicClosure K)))) =
      finiteEtaleCoverBaseMap (Spec (.of K)) (FiniteEtale.mk (ξ K E)) := by
    apply MorphismProperty.Over.Hom.ext
    exact ((finiteGaloisEtaleDiagram K).map h.op).w
  let b := finiteEtaleCoverBaseMap (Spec (.of K)) (FiniteEtale.mk
    (ξ K (⊥ : FiniteGaloisIntermediateField K (AlgebraicClosure K))))
  let e := finiteEtaleCoverBaseMap (Spec (.of K)) (FiniteEtale.mk (ξ K E))
  let f := (finiteGaloisEtaleDiagram K).map h.op
  have hm : F.obj.map e.op = F.obj.map b.op ≫ F.obj.map f.op :=
    (congrArg (fun g : finiteGaloisEtaleObject K E ⟶
      Scheme.Etale.mk (𝟙 (Spec (.of K))) => F.obj.map g.op) hb.symm).trans
        (F.obj.map_comp b.op f.op)
  exact ((congrArg (fun g => g ≫ finiteGaloisSectionColimitι K F E) hm).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun g => F.obj.map b.op ≫ g)
        (finiteGaloisSectionColimitι_transition K F h)))).symm

/-- Base sections inject into the actual geometric-section colimit. -/
theorem finiteGaloisBaseToColimit_injective :
    Function.Injective (finiteGaloisBaseToColimit K F) := by
  let E : FiniteGaloisIntermediateField K (AlgebraicClosure K) := ⊥
  let F₀ := (sheafCompose (Spec (.of K)).smallEtaleTopology
    (forget AddCommGrpCat.{u})).obj F
  have hi : Function.Injective
      (F.obj.map (finiteEtaleCoverBaseMap (Spec (.of K))
        (FiniteEtale.mk (ξ K E))).op) := by
    apply etaleSheaf_map_injective_of_surjective (Spec (.of K)) F₀
    change Function.Surjective (ξ K E)
    intro x
    exact ⟨default, Subsingleton.elim _ _⟩
  exact (finiteGaloisSectionColimitι_injective K F E).comp hi

/-- Actual base sections are fixed by the absolute Galois action. -/
theorem finiteGaloisBaseToColimit_invariant
    (s : F.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))))
    (σ : Gal(AlgebraicClosure K/K)) :
    (finiteGaloisSectionColimitAction K F σ).asIso.hom
      (finiteGaloisBaseToColimit K F s) = finiteGaloisBaseToColimit K F s := by
  let E : FiniteGaloisIntermediateField K (AlgebraicClosure K) := ⊥
  let t := F.obj.map (finiteEtaleCoverBaseMap (Spec (.of K))
    (FiniteEtale.mk (ξ K E))).op s
  have ht : (fieldGaloisSheafAction K E F (AlgEquiv.restrictNormalHom E σ)).asIso.hom t = t :=
    finiteEtaleSheaf_restrict_invariant (Spec (.of K))
      ((sheafCompose (Spec (.of K)).smallEtaleTopology (forget AddCommGrpCat.{u})).obj F)
      (FiniteEtale.mk (ξ K E)) s
      (MulOpposite.unop
        (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K E
          (AlgEquiv.restrictNormalHom E σ)))
  exact (ConcreteCategory.congr_hom
    (finiteGaloisSectionColimitAction_ι K F σ E) t).trans
      (congrArg (finiteGaloisSectionColimitι K F E) ht)

/-- Every invariant geometric section descends to an actual base section. -/
theorem exists_base_section_of_finiteGaloisColimit_invariant
    (x : finiteGaloisSectionColimit K F)
    (hx : ∀ σ : Gal(AlgebraicClosure K/K),
      (finiteGaloisSectionColimitAction K F σ).asIso.hom x = x) :
    ∃ s : F.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))),
      finiteGaloisBaseToColimit K F s = x := by
  obtain ⟨E, t, rfl⟩ := finiteGaloisSectionColimit_exists_stage K F x
  have ht (τ : Gal(E/K)) : (fieldGaloisSheafAction K E F τ).asIso.hom t = t := by
    obtain ⟨σ, rfl⟩ :=
      (AlgEquiv.restrictNormalHom_surjective (F := K) (E := AlgebraicClosure K)
        (K₁ := E)) τ
    apply finiteGaloisSectionColimitι_injective K F E
    exact (ConcreteCategory.congr_hom
      (finiteGaloisSectionColimitAction_ι K F σ E) t).symm.trans (hx σ)
  let Y : FiniteEtale (Spec (.of K)) := FiniteEtale.mk (ξ K E)
  let F₀ := (sheafCompose (Spec (.of K)).smallEtaleTopology
    (forget AddCommGrpCat.{u})).obj F
  have hinv (τ : Aut Y) :
      F₀.obj.map ((finiteEtaleInclusion (Spec (.of K))).map τ.asIso.hom).op t = t := by
    obtain ⟨σ, hσ⟩ :=
      (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K E).surjective
        (MulOpposite.op τ)
    have hh := ht σ
    change F.obj.map ((finiteEtaleInclusion (Spec (.of K))).map
      (MulOpposite.unop
        (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K E σ)).asIso.hom).op
        t = t at hh
    rw [hσ] at hh
    exact hh
  have : PreGaloisCategory.IsGalois Y :=
    EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois K E
  obtain ⟨s, hs, _⟩ := existsUnique_section_of_galois_invariant
    (Spec (.of K)) F₀ Y t hinv
  refine ⟨s, ?_⟩
  rw [finiteGaloisBaseToColimit_eq_stage K F E]
  exact congrArg (finiteGaloisSectionColimitι K F E) hs

/-- The actual restriction map from global sections to absolute Galois invariants. -/
def finiteGaloisBaseToInvariants :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) →+
      (finiteGaloisSectionColimitRep K F).ρ.invariants where
  toFun s := ⟨finiteGaloisBaseToColimit K F s,
    finiteGaloisBaseToColimit_invariant K F s⟩
  map_zero' := Subtype.ext ((finiteGaloisBaseToColimit K F).hom.map_zero)
  map_add' s t := Subtype.ext ((finiteGaloisBaseToColimit K F).hom.map_add s t)

/-- Actual global sections are precisely the absolute Galois invariants
of actual geometric sections. -/
def finiteGaloisBaseInvariantsAddEquiv :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) ≃+
      (finiteGaloisSectionColimitRep K F).ρ.invariants :=
  AddEquiv.ofBijective (finiteGaloisBaseToInvariants K F) ⟨
    fun _ _ h => finiteGaloisBaseToColimit_injective K F (congrArg Subtype.val h),
    fun x => by
      obtain ⟨s, hs⟩ := exists_base_section_of_finiteGaloisColimit_invariant K F x.val
        x.property
      exact ⟨s, Subtype.ext hs⟩⟩

end EtaleCohomology
