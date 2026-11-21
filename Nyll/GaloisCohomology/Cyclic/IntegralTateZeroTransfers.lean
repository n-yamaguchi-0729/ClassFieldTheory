/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RepresentationTheory.Rep.Res
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorNorm

/-!
# Restriction and corestriction in integral Tate degree zero

Restriction keeps the original invariant vector and corestriction takes its
relative norm. Two coset decompositions identify the actual norm boundaries,
so the maps descend to the original Tate cohomology in independent universes.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped RepTensor BigOperators TensorProduct

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] (H : Subgroup G)

private def cosetProduct : (G ⧸ H) × H ≃ G where
  toFun z := z.1.out * (z.2 : G)
  invFun g := ((g : G ⧸ H), ⟨(g : G ⧸ H).out⁻¹ * g,
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ H))⟩)
  left_inv := by
    rintro ⟨q, h⟩
    have hq : ((q.out * (h : G) : G) : G ⧸ H) = q :=
      (QuotientGroup.mk_mul_of_mem q.out h.property).trans (QuotientGroup.out_eq' q)
    apply Prod.ext hq
    apply Subtype.ext
    change ((q.out * (h : G) : G) : G ⧸ H).out⁻¹ * (q.out * (h : G)) = h.val
    rw [hq, inv_mul_cancel_left]
  right_inv g := mul_inv_cancel_left _ _

variable [Fintype G] [Fintype H] [Fintype (G ⧸ H)]

/-- The actual relative coset sum on the original module. -/
def relativeNorm (A : Rep.{v} ℤ G) : A →ₗ[ℤ] A := ∑ q : G ⧸ H, A.ρ q.out

omit [Fintype G] [Fintype H] in
/-- Evaluation of the original relative norm is the coset sum of the original action. -/
theorem relativeNorm_apply (A : Rep.{v} ℤ G) (x : A) :
    relativeNorm H A x = ∑ q : G ⧸ H, A.ρ q.out x :=
  LinearMap.sum_apply Finset.univ (fun q : G ⧸ H => A.ρ q.out) x

/-- The relative norm after the subgroup norm is exactly the original group norm. -/
theorem relativeNorm_subgroupNorm (A : Rep.{v} ℤ G) (x : A) :
    relativeNorm H A ((Rep.res H.subtype A).ρ.norm x) = A.ρ.norm x := by
  unfold relativeNorm
  simp only [Representation.norm, LinearMap.sum_apply]
  change (∑ q : G ⧸ H, A.ρ q.out (∑ h : H, A.ρ (h : G) x)) = ∑ g : G, A.ρ g x
  simp only [map_sum, ← mul_apply_eq_comp, ← map_mul]
  rw [← Fintype.sum_prod_type (f := fun z : (G ⧸ H) × H => A.ρ (z.1.out * (z.2 : G)) x)]
  exact Fintype.sum_equiv (cosetProduct H) _ _ (fun _ => rfl)

/-- The original group norm also factors through the subgroup norm, by
summing the actions of the inverses of the same chosen coset representatives. -/
theorem subgroupNorm_relativeTransfer (A : Rep.{v} ℤ G) (x : A) :
    (Rep.res H.subtype A).ρ.norm (∑ q : G ⧸ H, A.ρ q.out⁻¹ x) = A.ρ.norm x := by
  simp only [Representation.norm, LinearMap.sum_apply]
  change (∑ h : H, A.ρ (h : G) (∑ q : G ⧸ H, A.ρ q.out⁻¹ x)) = ∑ g : G, A.ρ g x
  simp only [map_sum, ← mul_apply_eq_comp, ← map_mul]
  rw [Finset.sum_comm,
    ← Fintype.sum_prod_type (f := fun z : (G ⧸ H) × H => A.ρ ((z.2 : G) * z.1.out⁻¹) x)]
  let e := (Equiv.prodCongr (Equiv.refl (G ⧸ H)) (Equiv.inv H)).trans
    ((cosetProduct H).trans (Equiv.inv G))
  refine Fintype.sum_equiv e _ _ (fun z => ?_)
  change A.ρ ((z.2 : G) * z.1.out⁻¹) x = A.ρ ((z.1.out * (z.2 : G)⁻¹)⁻¹) x
  rw [mul_inv_rev, inv_inv]

omit [Fintype G] [Fintype H] in
/-- A subgroup-fixed original vector has group-fixed relative norm. -/
theorem relativeNorm_mem_invariants (A : Rep.{v} ℤ G)
    (x : (Rep.res H.subtype A).ρ.invariants) : relativeNorm H A x ∈ A.ρ.invariants := by
  intro g
  unfold relativeNorm
  simp only [LinearMap.sum_apply, map_sum]
  refine Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ (fun q => ?_)
  rw [← mul_apply_eq_comp, ← map_mul]
  have hc : ((g • q).out : G ⧸ H) = (g * q.out : G) := by
    rw [QuotientGroup.out_eq']
    change g • q = g • (q.out : G ⧸ H)
    rw [QuotientGroup.out_eq']
  let h : H := ⟨(g • q).out⁻¹ * (g * q.out), QuotientGroup.eq.mp hc⟩
  have hr : (g • q).out * (h : G) = g * q.out := mul_inv_cancel_left _ _
  rw [← hr, map_mul, mul_apply_eq_comp]
  exact congrArg (A.ρ (g • q).out) (x.property h)

/-- The underlying invariant-vector inclusion used for restriction. -/
def restrictInvariants (A : Rep.{v} ℤ G) :
    A.ρ.invariants →ₗ[ℤ] (Rep.res H.subtype A).ρ.invariants := by
  let f : A.ρ.invariants →+ (Rep.res H.subtype A).ρ.invariants := {
    toFun := fun x => ⟨x.val, fun h => x.property h.val⟩
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun n x => map_intCast_smul f ℤ ℤ n x }

/-- The relative norm on invariant vectors used for corestriction. -/
def corestrictInvariants (A : Rep.{v} ℤ G) :
    (Rep.res H.subtype A).ρ.invariants →ₗ[ℤ] A.ρ.invariants := by
  let f : (Rep.res H.subtype A).ρ.invariants →+ A.ρ.invariants := {
    toFun := fun x => ⟨relativeNorm H A x, relativeNorm_mem_invariants H A x⟩
    map_zero' := Subtype.ext (map_zero (relativeNorm H A))
    map_add' := fun x y => Subtype.ext (map_add (relativeNorm H A) x.val y.val) }
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun n x => map_intCast_smul f ℤ ℤ n x }

/-- Restriction in degree zero, descended through the original norm quotient. -/
def tateZeroRestrict (A : Rep.{v} ℤ G) : tate A 0 →ₗ[ℤ] tate (Rep.res H.subtype A) 0 := by
  let B := Rep.res H.subtype A
  let eA : tate A 0 ≃ₗ[ℤ] (A.ρ.invariants ⧸ fixedNormSubmodule A) :=
    (tateZeroEquivFixedQuotient A).toIntLinearEquiv
  let eB : tate B 0 ≃ₗ[ℤ] (B.ρ.invariants ⧸ fixedNormSubmodule B) :=
    (tateZeroEquivFixedQuotient B).toIntLinearEquiv
  let q := (fixedNormSubmodule B).mkQ.comp (restrictInvariants H A)
  have hq : fixedNormSubmodule A ≤ LinearMap.ker q := by
    intro x hx
    change (x : A) ∈ LinearMap.range A.ρ.norm at hx
    obtain ⟨a, ha⟩ := hx
    change (fixedNormSubmodule B).mkQ (restrictInvariants H A x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨∑ c : G ⧸ H, A.ρ c.out⁻¹ a, (subgroupNorm_relativeTransfer H A a).trans ha⟩
  exact eB.symm.toLinearMap.comp (((fixedNormSubmodule A).liftQ q hq).comp eA.toLinearMap)

/-- Corestriction in degree zero, descended through the original norm quotient. -/
def tateZeroCorestrict (A : Rep.{v} ℤ G) : tate (Rep.res H.subtype A) 0 →ₗ[ℤ] tate A 0 := by
  let B := Rep.res H.subtype A
  let eB : tate B 0 ≃ₗ[ℤ] (B.ρ.invariants ⧸ fixedNormSubmodule B) :=
    (tateZeroEquivFixedQuotient B).toIntLinearEquiv
  let eA : tate A 0 ≃ₗ[ℤ] (A.ρ.invariants ⧸ fixedNormSubmodule A) :=
    (tateZeroEquivFixedQuotient A).toIntLinearEquiv
  let q := (fixedNormSubmodule A).mkQ.comp (corestrictInvariants H A)
  have hq : fixedNormSubmodule B ≤ LinearMap.ker q := by
    intro x hx
    change (x : B) ∈ LinearMap.range B.ρ.norm at hx
    obtain ⟨a, ha⟩ := hx
    change (fixedNormSubmodule A).mkQ (corestrictInvariants H A x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, (relativeNorm_subgroupNorm H A a).symm.trans
      (congrArg (relativeNorm H A) ha)⟩
  exact eA.symm.toLinearMap.comp (((fixedNormSubmodule B).liftQ q hq).comp eB.toLinearMap)

/-- Restricting a fixed class keeps its original representative. -/
theorem tateZeroRestrict_fixedClass (A : Rep.{v} ℤ G) (x : A.ρ.invariants) :
    tateZeroRestrict H A (fixedClass A x) =
      fixedClass (Rep.res H.subtype A) (restrictInvariants H A x) := by
  let B := Rep.res H.subtype A
  apply (tateZeroEquivFixedQuotient B).injective
  rw [tateZeroEquivFixedQuotient_fixedClass]
  unfold tateZeroRestrict
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv,
    AddEquiv.coe_symm_toIntLinearEquiv,
    tateZeroEquivFixedQuotient_fixedClass, Submodule.mkQ_apply, Submodule.liftQ_apply]
  exact (tateZeroEquivFixedQuotient (Rep.res H.subtype A)).apply_symm_apply _

/-- Corestricting a fixed class takes the actual relative norm of its representative. -/
theorem tateZeroCorestrict_fixedClass (A : Rep.{v} ℤ G)
    (x : (Rep.res H.subtype A).ρ.invariants) :
    tateZeroCorestrict H A (fixedClass (Rep.res H.subtype A) x) =
      fixedClass A (corestrictInvariants H A x) := by
  apply (tateZeroEquivFixedQuotient A).injective
  rw [tateZeroEquivFixedQuotient_fixedClass]
  unfold tateZeroCorestrict
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv,
    AddEquiv.coe_symm_toIntLinearEquiv, AddEquiv.apply_symm_apply,
    Submodule.mkQ_apply]
  have hx := tateZeroEquivFixedQuotient_fixedClass (Rep.res H.subtype A) x
  rw [hx]; rfl

/-- The degree-zero restriction commutes with actual coefficient maps. -/
theorem tateZeroRestrict_naturality {A B : Rep.{v} ℤ G} (f : A ⟶ B) (x : tate A 0) :
    (tateFunctor H 0).map ((Rep.resFunctor H.subtype).map f) (tateZeroRestrict H A x) =
      tateZeroRestrict H B ((tateFunctor G 0).map f x) := by
  obtain ⟨a, rfl⟩ := fixedClass_surjective A x
  rw [tateZeroRestrict_fixedClass, fixedClass_map, fixedClass_map,
    tateZeroRestrict_fixedClass]; rfl

/-- The degree-zero corestriction commutes with actual coefficient maps. -/
theorem tateZeroCorestrict_naturality {A B : Rep.{v} ℤ G} (f : A ⟶ B)
    (x : tate (Rep.res H.subtype A) 0) :
    (tateFunctor G 0).map f (tateZeroCorestrict H A x) =
      tateZeroCorestrict H B ((tateFunctor H 0).map ((Rep.resFunctor H.subtype).map f) x) := by
  obtain ⟨a, rfl⟩ := fixedClass_surjective (Rep.res H.subtype A) x
  rw [tateZeroCorestrict_fixedClass, fixedClass_map, fixedClass_map]
  let b : (Rep.res H.subtype B).ρ.invariants := ⟨f a.val, fun g => by
    change B.ρ g.val (f a.val) = f a.val
    rw [← Rep.hom_comm_apply, show A.ρ g.val a.val = a.val from a.property g]⟩
  change _ = tateZeroCorestrict H B (fixedClass (Rep.res H.subtype B) b)
  rw [tateZeroCorestrict_fixedClass]
  apply congrArg (fixedClass B)
  apply Subtype.ext
  change f.hom (relativeNorm H A a) = relativeNorm H B (f.hom a)
  unfold relativeNorm
  simp only [LinearMap.sum_apply, map_sum, Rep.hom_comm_apply]

/-- Corestriction after restriction multiplies a Tate class by the subgroup index. -/
theorem tateZeroCorestrict_restrict (A : Rep.{v} ℤ G) (x : tate A 0) :
    tateZeroCorestrict H A (tateZeroRestrict H A x) = H.index • x := by
  obtain ⟨a, rfl⟩ := fixedClass_surjective A x
  rw [tateZeroRestrict_fixedClass, tateZeroCorestrict_fixedClass]
  have hcard : Fintype.card (G ⧸ H) = H.index := Nat.card_eq_fintype_card.symm
  have h : corestrictInvariants H A (restrictInvariants H A a) = H.index • a := by
    apply Subtype.ext
    change relativeNorm H A a = ((H.index • a : A.ρ.invariants) : A)
    rw [show ((H.index • a : A.ρ.invariants) : A) = H.index • (a : A) from
      map_nsmul A.ρ.invariants.toAddSubgroup.subtype H.index a]
    rw [relativeNorm_apply H A]
    calc
      ∑ q : G ⧸ H, A.ρ q.out a = ∑ _ : G ⧸ H, (a : A) :=
        Finset.sum_congr rfl (fun q _ => a.property q.out)
      _ = H.index • (a : A) := by rw [Finset.sum_const, Finset.card_univ, hcard]
  apply (tateZeroEquivFixedQuotient A).injective
  rw [map_nsmul, tateZeroEquivFixedQuotient_fixedClass, tateZeroEquivFixedQuotient_fixedClass,
    h, map_nsmul]

/-- Restriction preserves the cup product in degree zero on both inputs. -/
theorem tateZeroRestrict_cup (A B : Rep.{u} ℤ G) (x : tate A 0) (y : tate B 0) :
    tateZeroRestrict H (A ⊗ᵣ B) (tensorCupZeroRight A B 0 x y) =
      tensorCupZeroRight (Rep.res H.subtype A) (Rep.res H.subtype B) 0
        (tateZeroRestrict H A x) (tateZeroRestrict H B y) := by
  obtain ⟨a, rfl⟩ := fixedClass_surjective A x
  obtain ⟨b, rfl⟩ := fixedClass_surjective B y
  rw [tensorCupZeroRight_fixedClasses, tateZeroRestrict_fixedClass,
    tateZeroRestrict_fixedClass, tateZeroRestrict_fixedClass, tensorCupZeroRight_fixedClasses]; rfl

/-- The degree-zero projection formula uses the same relative norm and tensor
on the original fixed representatives. -/
theorem tateZeroCorestrict_cup (A B : Rep.{u} ℤ G) (x : tate A 0)
    (y : tate (Rep.res H.subtype B) 0) :
    tateZeroCorestrict H (A ⊗ᵣ B)
        (tensorCupZeroRight (Rep.res H.subtype A) (Rep.res H.subtype B) 0
          (tateZeroRestrict H A x) y) =
      tensorCupZeroRight A B 0 x (tateZeroCorestrict H B y) := by
  obtain ⟨a, rfl⟩ := fixedClass_surjective A x
  obtain ⟨b, rfl⟩ := fixedClass_surjective (Rep.res H.subtype B) y
  simp only [tateZeroRestrict_fixedClass, tensorCupZeroRight_fixedClasses,
    tateZeroCorestrict_fixedClass]
  let c : (Rep.res H.subtype (A ⊗ᵣ B)).ρ.invariants :=
    ⟨(a : A) ⊗ₜ[ℤ] (b : B), fun h => by
      change (A.ρ.tprod B.ρ) h.val ((a : A) ⊗ₜ[ℤ] (b : B)) = _
      rw [Representation.tprod_apply, TensorProduct.map_tmul, a.property h.val,
        show B.ρ h.val b.val = b.val from b.property h]⟩
  change tateZeroCorestrict H (A ⊗ᵣ B) (fixedClass (Rep.res H.subtype (A ⊗ᵣ B)) c) = _
  rw [tateZeroCorestrict_fixedClass]
  apply congrArg (fixedClass (A ⊗ᵣ B))
  apply Subtype.ext
  let T := A ⊗ᵣ B
  let t : T := (a : A) ⊗ₜ[ℤ] (b : B)
  let b₀ : B := b.val
  change relativeNorm H T t = (a : A) ⊗ₜ[ℤ] relativeNorm H B b₀
  rw [relativeNorm_apply H T t, relativeNorm_apply H B b₀, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  change (A.ρ.tprod B.ρ) q.out ((a : A) ⊗ₜ[ℤ] (b : B)) = _
  rw [Representation.tprod_apply, TensorProduct.map_tmul, a.property q.out]

end IntegralGroupCohomology.Universe
