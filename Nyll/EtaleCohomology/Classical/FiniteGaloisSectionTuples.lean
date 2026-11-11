/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitFaithful
public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitAction
public import Nyll.GaloisCohomology.Topology.GaloisFiniteStageTuples

/-!
# Finite-stage realization of geometric-section-valued functions

Both the arguments and the actual section values of a continuous
cochain are realized over one finite Galois field. The coefficient
transition is actual restriction, not an assumed comparison.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]
variable (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
variable [TopologicalSpace (finiteGaloisSectionColimit K F)]
  [DiscreteTopology (finiteGaloisSectionColimit K F)]

/-- A continuous function on a finite Galois-group power, with actual geometric
section values, is realized over a single actual finite Galois extension. -/
theorem exists_finiteGalois_section_tuple
    {ι : Type v} [Finite ι]
    (z : (ι → Gal(AlgebraicClosure K/K)) → finiteGaloisSectionColimit K F)
    (hz : Continuous z) :
    ∃ (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (s : (ι → Gal(M/K)) → F.obj.obj (op (finiteGaloisEtaleObject K M))),
      ∀ a : ι → Gal(AlgebraicClosure K/K),
        finiteGaloisSectionColimitι K F M
          (s (fun i => AlgEquiv.restrictNormalHom M (a i))) = z a := by
  classical
  obtain ⟨L, zL, hL⟩ :=
    GaloisCohomology.exists_finiteGalois_factor_absolute_tuple_discrete K z hz
  have : Fintype Gal(L/K) := AlgEquiv.fintype K L
  obtain ⟨E, sE, hE⟩ := finiteGaloisSectionColimit_exists_common_stage K F zL
  obtain ⟨M, hM⟩ := IsFiltered.sup_objs_exists ({E, L} :
    Finset (FiniteGaloisIntermediateField K (AlgebraicClosure K)))
  let iE : E ⟶ M := (hM (Finset.mem_insert_self E {L})).some
  let iL : L ⟶ M :=
    (hM (Finset.mem_insert_of_mem (Finset.mem_singleton_self L))).some
  let : Algebra L M := (IntermediateField.inclusion iL.le).toRingHom.toAlgebra
  have : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IntermediateField.inclusion iL.le).commutes x).symm)
  have : IsScalarTower L M (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let s (a : ι → Gal(M/K)) :=
    (finiteGaloisSectionDiagram K F).map iE
      (sE (fun i => AlgEquiv.restrictNormalHom L (a i)))
  refine ⟨M, s, ?_⟩
  intro a
  have hr : (fun i => AlgEquiv.restrictNormalHom L
      (AlgEquiv.restrictNormalHom M (a i))) =
      (fun i => AlgEquiv.restrictNormalHom L (a i)) := by
    funext i
    exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L M (a i)).symm
  have ht := ConcreteCategory.congr_hom
    (finiteGaloisSectionColimitι_transition K F iE)
      (sE (fun i => AlgEquiv.restrictNormalHom L
        (AlgEquiv.restrictNormalHom M (a i))))
  change finiteGaloisSectionColimitι K F M
      (s (fun i => AlgEquiv.restrictNormalHom M (a i))) =
    finiteGaloisSectionColimitι K F E
      (sE (fun i => AlgEquiv.restrictNormalHom L
        (AlgEquiv.restrictNormalHom M (a i)))) at ht
  exact ht.trans ((congrArg (fun b => finiteGaloisSectionColimitι K F E (sE b)) hr).trans
    ((hE _).trans (hL a)))


omit [TopologicalSpace (finiteGaloisSectionColimit K F)]
  [DiscreteTopology (finiteGaloisSectionColimit K F)] in
/-- An actual finite-stage realization of an equivariant geometric-section-valued
function is equivariant for the actual finite Galois action. -/
theorem finiteGalois_section_tuple_equivariant
    {ι : Type v}
    (z : (ι → Gal(AlgebraicClosure K/K)) → finiteGaloisSectionColimit K F)
    (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (s : (ι → Gal(M/K)) → F.obj.obj (op (finiteGaloisEtaleObject K M)))
    (hs : ∀ a : ι → Gal(AlgebraicClosure K/K),
      finiteGaloisSectionColimitι K F M
        (s (fun i => AlgEquiv.restrictNormalHom M (a i))) = z a)
    (hz : ∀ (σ : Gal(AlgebraicClosure K/K)) (a : ι → Gal(AlgebraicClosure K/K)),
      z (fun i => σ * a i) = (finiteGaloisSectionColimitAction K F σ).asIso.hom (z a))
    (τ : Gal(M/K)) (b : ι → Gal(M/K)) :
    s (fun i => τ * b i) = (fieldGaloisSheafAction K M F τ).asIso.hom (s b) := by
  classical
  let r : Gal(AlgebraicClosure K/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective _
  obtain ⟨σ, hσ⟩ := hr τ
  let a : ι → Gal(AlgebraicClosure K/K) := fun i => (hr (b i)).choose
  have ha : (fun i => r (a i)) = b := funext (fun i => (hr (b i)).choose_spec)
  have hσa : (fun i => r (σ * a i)) = (fun i => τ * b i) := by
    funext i
    exact (map_mul r σ (a i)).trans
      (congrArg₂ (· * ·) hσ (congrFun ha i))
  have hsa : finiteGaloisSectionColimitι K F M (s b) = z a :=
    (congrArg (fun c => finiteGaloisSectionColimitι K F M (s c)) ha).symm.trans (hs a)
  have hsσa : finiteGaloisSectionColimitι K F M (s (fun i => τ * b i)) =
      z (fun i => σ * a i) :=
    (congrArg (fun c => finiteGaloisSectionColimitι K F M (s c)) hσa).symm.trans
      (hs (fun i => σ * a i))
  apply finiteGaloisSectionColimitι_injective K F M
  have hact := ConcreteCategory.congr_hom
    (finiteGaloisSectionColimitAction_ι K F σ M) (s b)
  have hact' : (finiteGaloisSectionColimitAction K F σ).asIso.hom
      (finiteGaloisSectionColimitι K F M (s b)) =
      finiteGaloisSectionColimitι K F M ((fieldGaloisSheafAction K M F τ).asIso.hom (s b)) :=
    hact.trans (congrArg (fun g => finiteGaloisSectionColimitι K F M
      ((fieldGaloisSheafAction K M F g).asIso.hom (s b))) hσ)
  exact hsσa.trans ((hz σ a).trans
    ((congrArg (fun x => (finiteGaloisSectionColimitAction K F σ).asIso.hom x) hsa).symm.trans
      hact'))

end EtaleCohomology
