/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement

/-!
# Subgroup index annihilates H² when restricted H² vanishes

The coefficient trace is the existing finite-index coinduction-induction isomorphism
followed by the induction counit. Its composite with the coinduction unit is the index.
Shapiro then supplies the vanishing intermediate cohomology object.
-/

open CategoryTheory
open scoped BigOperators

namespace ClassFieldTower.Cohomology

noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (H : Subgroup G) [H.FiniteIndex]

/-- The actual coefficient trace from the coinduced restricted representation. -/
def finiteIndexCoefficientTrace :
    Rep.coind H.subtype (Rep.res H.subtype A) ⟶ A := by
  classical
  exact (Rep.indCoindIso (Rep.res H.subtype A)).inv ≫
    (Rep.indResHomEquiv H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)

/-- The existing coefficient trace commutes with morphisms of representations. -/
theorem finiteIndexCoefficientTrace_natural {B : Rep R G} (f : A ⟶ B) :
    (Rep.coindFunctor R H.subtype).map ((Rep.resFunctor H.subtype).map f) ≫
        finiteIndexCoefficientTrace B H =
      finiteIndexCoefficientTrace A H ≫ f := by
  classical
  exact (Rep.coindResAdjunction R H).counit.naturality f

omit [H.FiniteIndex] in
private theorem inductionCounit_mk (g : G) (a : A) :
    ((Rep.indResHomEquiv H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)).hom
      (Representation.IndV.mk H.subtype (Rep.res H.subtype A).ρ g a) =
        A.ρ g⁻¹ a := by
  let : Module R (Rep.res H.subtype A).V := (Rep.res H.subtype A).hV2
  let f := (Rep.indResHomEquiv H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)
  have h1 : f.hom (Representation.IndV.mk H.subtype (Rep.res H.subtype A).ρ 1 a) = a :=
    congrArg (fun u => u.hom a)
      ((Rep.indResHomEquiv H.subtype (Rep.res H.subtype A) A).apply_symm_apply (𝟙 _))
  have h := Rep.hom_comm_apply f g⁻¹
    (Representation.IndV.mk H.subtype (Rep.res H.subtype A).ρ 1 a)
  rw [Representation.ind_mk, inv_inv, one_mul, h1] at h
  exact h

/-- Coinduction followed by the coefficient trace is multiplication by the subgroup index. -/
theorem coinductionUnit_comp_finiteIndexCoefficientTrace :
    Rep.resCoindToHom H.subtype A (Rep.res H.subtype A) (𝟙 _) ≫
      finiteIndexCoefficientTrace A H = H.index • 𝟙 A := by
  classical
  let : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  let : Module R (Rep.res H.subtype A).V := (Rep.res H.subtype A).hV2
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  change ((Rep.indResHomEquiv H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)).hom
    (Rep.coindToInd (Rep.res H.subtype A)
      ((Rep.resCoindToHom H.subtype A (Rep.res H.subtype A) (𝟙 _)).hom a)) =
        H.index • a
  rw [Rep.coindToInd_apply, map_sum]
  trans ∑ _ : Quotient (QuotientGroup.rightRel H), a
  · apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with
    | h g =>
      change ((Rep.indResHomEquiv H.subtype (Rep.res H.subtype A) A).symm (𝟙 _)).hom
        (Representation.IndV.mk H.subtype (Rep.res H.subtype A).ρ g (A.ρ g a)) = a
      rw [inductionCounit_mk]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
  · rw [Finset.sum_const, Finset.card_univ, QuotientGroup.card_quotient_rightRel,
      ← Nat.card_eq_fintype_card, ← H.index_eq_card]

/-- Trace of a morphism defined after restriction to a finite-index subgroup. -/
def finiteIndexHomTrace (T : Rep R G)
    (f : Rep.res H.subtype T ⟶ Rep.res H.subtype A) : T ⟶ A :=
  Rep.resCoindToHom H.subtype T (Rep.res H.subtype A) f ≫
    finiteIndexCoefficientTrace A H

/-- Tracing a restricted morphism commutes with its target morphisms. -/
theorem finiteIndexHomTrace_comp {B : Rep R G} (T : Rep R G)
    (f : Rep.res H.subtype T ⟶ Rep.res H.subtype A) (g : A ⟶ B) :
    finiteIndexHomTrace A H T f ≫ g =
      finiteIndexHomTrace B H T (f ≫ (Rep.resFunctor H.subtype).map g) := by
  unfold finiteIndexHomTrace
  rw [Category.assoc, ← finiteIndexCoefficientTrace_natural, ← Category.assoc]
  congr 1

/-- The trace of an ambient morphism restricted to the subgroup is its
index multiple. -/
theorem finiteIndexHomTrace_restriction (T : Rep R G) (f : T ⟶ A) :
    finiteIndexHomTrace A H T ((Rep.resFunctor H.subtype).map f) =
      H.index • f := by
  have hu :
      Rep.resCoindToHom H.subtype T (Rep.res H.subtype A)
          ((Rep.resFunctor H.subtype).map f) =
        f ≫ Rep.resCoindToHom H.subtype A (Rep.res H.subtype A) (𝟙 _) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext h
    exact Rep.hom_comm_apply f h x
  unfold finiteIndexHomTrace
  rw [hu, Category.assoc, coinductionUnit_comp_finiteIndexCoefficientTrace]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- An invariant image with a subgroup-invariant preimage has an ambient
invariant preimage after multiplication by the subgroup index. -/
theorem exists_invariant_index_preimage (A : Rep.{0} R G)
    {B : Rep.{0} R G} (d : A ⟶ B)
    (v : A) (hv : ∀ h : H, A.ρ (h : G) v = v)
    (hdv : ∀ g : G, B.ρ g (d.hom v) = d.hom v) :
    ∃ w : A, (∀ g : G, A.ρ g w = w) ∧
      d.hom w = H.index • d.hom v := by
  let T := Rep.trivial R G R
  let f : Rep.res H.subtype T ⟶ Rep.res H.subtype A :=
    Rep.ofHom ⟨LinearMap.toSpanSingleton R A v, by
      intro h
      apply LinearMap.ext
      intro r
      change r • v = A.ρ (h : G) (r • v)
      rw [map_smul, hv]⟩
  let g : T ⟶ B :=
    Rep.ofHom ⟨LinearMap.toSpanSingleton R B (d.hom v), by
      intro t
      apply LinearMap.ext
      intro r
      change r • d.hom v = B.ρ t (r • d.hom v)
      rw [map_smul, hdv]⟩
  have hfg : f ≫ (Rep.resFunctor H.subtype).map d =
      (Rep.resFunctor H.subtype).map g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    exact map_smul d.hom r v
  let t := finiteIndexHomTrace A H T f
  refine ⟨t.hom 1, ?_, ?_⟩
  · intro a
    exact (Rep.hom_comm_apply t a (1 : R)).symm
  · have ht : t ≫ d = H.index • g := by
      change finiteIndexHomTrace A H T f ≫ d = _
      rw [finiteIndexHomTrace_comp, hfg, finiteIndexHomTrace_restriction]
    have ht₁ := CategoryTheory.ConcreteCategory.congr_hom ht (1 : R)
    change d.hom (t.hom 1) = H.index • ((1 : R) • d.hom v) at ht₁
    simpa only [one_smul] using ht₁

private theorem H2_map_nsmul_id (m : ℕ)
    (c : groupCohomology A 2) :
    groupCohomology.map (MonoidHom.id G) (m • 𝟙 A) 2 c = m • c := by
  induction c using groupCohomology.H2_induction_on with
  | h z =>
    rw [groupCohomology.H2π_comp_map_apply]
    have hz : groupCohomology.mapCocycles₂ (MonoidHom.id G) (m • 𝟙 A) z = m • z := by
      apply Subtype.ext
      funext st
      rfl
    rw [hz, map_nsmul]

/-- If actual H² on a finite-index subgroup vanishes, its index kills every ambient H² class. -/
theorem index_nsmul_H2_eq_zero_of_restricted_isZero
    (hH : Limits.IsZero (groupCohomology (Rep.res H.subtype A) 2))
    (c : groupCohomology A 2) : H.index • c = 0 := by
  classical
  have hCoind : Limits.IsZero
      (groupCohomology (Rep.coind H.subtype (Rep.res H.subtype A)) 2) :=
    hH.of_iso (groupCohomology.coindIso (Rep.res H.subtype A) 2)
  let : Subsingleton
      (groupCohomology (Rep.coind H.subtype (Rep.res H.subtype A)) 2) :=
    ModuleCat.isZero_iff_subsingleton.mp hCoind
  rw [← H2_map_nsmul_id, ← coinductionUnit_comp_finiteIndexCoefficientTrace,
    groupCohomology.map_id_comp]
  change groupCohomology.map (MonoidHom.id G) (finiteIndexCoefficientTrace A H) 2
    (groupCohomology.map (MonoidHom.id G)
      (Rep.resCoindToHom H.subtype A (Rep.res H.subtype A) (𝟙 _)) 2 c) = 0
  rw [Subsingleton.elim
    (groupCohomology.map (MonoidHom.id G)
      (Rep.resCoindToHom H.subtype A (Rep.res H.subtype A) (𝟙 _)) 2 c) 0, map_zero]

/-- Vanishing on every Sylow subgroup detects vanishing of actual H². -/
theorem H2_eq_zero_of_sylow_restrictions_isZero [Finite G]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Limits.IsZero (groupCohomology (Rep.res (P : Subgroup G).subtype A) 2))
    (c : groupCohomology A 2) : c = 0 := by
  classical
  by_contra hc
  have ho : addOrderOf c ≠ 1 := fun h1 => hc (AddMonoid.addOrderOf_eq_one_iff.mp h1)
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd ho
  have : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice inferInstance
  have hkill : P.index • c = 0 :=
    index_nsmul_H2_eq_zero_of_restricted_isZero A P (h p P) c
  exact P.not_dvd_index (hpc.trans (addOrderOf_dvd_of_nsmul_eq_zero hkill))


end
end ClassFieldTower.Cohomology
