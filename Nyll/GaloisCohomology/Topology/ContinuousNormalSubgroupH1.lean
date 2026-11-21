/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Mathlib.Data.Int.GCD
public import Mathlib.GroupTheory.OrderOfElement
public import Nyll.GaloisCohomology.Topology.ContinuousCupCorestriction
public import Nyll.GaloisCohomology.Topology.ContinuousH1CocycleSurjectivity

/-! # Continuous first cohomology and a prime-to-index normal open subgroup -/

@[expose] public section

open CategoryTheory ContRepresentation TopRep ReidemeisterSchreier.Profinite
open scoped BigOperators Topology

noncomputable section

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : TopRep.{u} ℤ G) (H : OpenSubgroup G) [(H : Subgroup G).Normal]

/-- Conjugation in the ambient group preserves the original normal subgroup. -/
def normalOpenConjugate (g : G) (h : (↥H.toSubgroup)) : (↥H.toSubgroup) :=
  ⟨g * (h : G) * g⁻¹, Subgroup.Normal.conj_mem (h : G) h.property g⟩

/-- The invariant continuous additive characters on the normal subgroup,
with the ambient action on both the subgroup and the coefficient. -/
def normalOpenInvariantCharacters :
    AddSubgroup (Additive ((↥H.toSubgroup) →ₜ* Multiplicative A)) where
  carrier := {χ | ∀ (g : G) (h : ↥H.toSubgroup),
    (χ.toMul (normalOpenConjugate H g h)).toAdd = A.ρ g (χ.toMul h).toAdd}
  zero_mem' := by
    intro g h
    change (0 : A) = A.ρ g 0
    exact (map_zero (A.ρ g)).symm
  add_mem' := by
    intro χ ψ hχ hψ g h
    let h' := normalOpenConjugate H g h
    change (χ.toMul h').toAdd + (ψ.toMul h').toAdd =
      A.ρ g ((χ.toMul h).toAdd + (ψ.toMul h).toAdd)
    rw [hχ g h, hψ g h, map_add]
  neg_mem' := by
    intro χ hχ g h
    change -(χ.toMul (normalOpenConjugate H g h)).toAdd = A.ρ g (-(χ.toMul h).toAdd)
    rw [hχ g h, map_neg]

/-- Evaluation at the same subgroup element is an additive map on invariant characters. -/
def normalOpenInvariantCharacterEval (h : ↥H.toSubgroup) :
    ↥(normalOpenInvariantCharacters A H) →+ A where
  toFun χ := (χ.val.toMul h).toAdd
  map_zero' := rfl
  map_add' _ _ := rfl

omit [IsTopologicalGroup G] in
/-- Evaluation at every subgroup element determines the invariant character. -/
theorem normalOpenInvariantCharacterEval_injective
    {χ ψ : ↥(normalOpenInvariantCharacters A H)}
    (h : ∀ a : ↥H.toSubgroup,
      normalOpenInvariantCharacterEval A H a χ = normalOpenInvariantCharacterEval A H a ψ) :
    χ = ψ := by
  apply Subtype.ext
  change χ.val.toMul = ψ.val.toMul
  apply ContinuousMonoidHom.ext
  intro a
  exact Multiplicative.toAdd.injective (h a)

variable (htriv : ∀ (h : ↥H.toSubgroup) (a : A), A.ρ (h : G) a = a)

include htriv

/-- Restriction of an original crossed homomorphism to invariant normal-subgroup characters. -/
def crossedRestrictionNormal (c : CrossedHom A) : ↥(normalOpenInvariantCharacters A H) := by
  let χ : (↥H.toSubgroup) →ₜ* Multiplicative A :=
    ⟨{ toFun := fun h => Multiplicative.ofAdd (c.toFun h)
       map_one' := congrArg Multiplicative.ofAdd c.map_one
       map_mul' := fun a b => congrArg Multiplicative.ofAdd (by
         change c.toFun ((a : G) * (b : G)) = c.toFun a + c.toFun b
         rw [c.map_mul, htriv a]) },
     c.continuous_toFun.comp continuous_subtype_val⟩
  refine ⟨Additive.ofMul χ, ?_⟩
  intro g h
  let j := normalOpenConjugate H g h
  have hj : (j : G) * g = g * (h : G) := by
    change (g * (h : G) * g⁻¹) * g = g * (h : G)
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have h₁ := c.map_mul g (h : G)
  have h₂ := c.map_mul (j : G) g
  rw [hj, htriv j] at h₂
  change c.toFun j = A.ρ g (c.toFun h)
  exact add_right_cancel (h₂.symm.trans (h₁.trans (add_comm _ _)))

/-- Restriction of homogeneous one-cocycles to their invariant characters. -/
def normalRestrictionCocycleHom : cocycles A 1 →+ ↥(normalOpenInvariantCharacters A H) where
  toFun z := crossedRestrictionNormal A H htriv (crossedHomOfCocycle A z)
  map_zero' := by
    apply normalOpenInvariantCharacterEval_injective A H
    intro h
    change ((homogeneousCochains A).iCycles 1 (0 : cocycles A 1)).val 1 (h : G) = 0
    rw [map_zero]
    rfl
  map_add' z w := by
    apply normalOpenInvariantCharacterEval_injective A H
    intro h
    change ((homogeneousCochains A).iCycles 1 (z + w)).val 1 (h : G) =
      ((homogeneousCochains A).iCycles 1 z).val 1 (h : G) +
        ((homogeneousCochains A).iCycles 1 w).val 1 (h : G)
    rw [map_add]
    rfl

/-- A degree-one boundary restricts to zero on the trivialized subgroup. -/
theorem normalRestrictionCocycleHom_kernel :
    (π A 1).hom.toLinearMap.toAddMonoidHom.ker ≤ (normalRestrictionCocycleHom A H htriv).ker := by
  intro z hz
  obtain ⟨w, hw⟩ := exists_boundary_of_π_eq_zero A 0 z hz
  apply normalOpenInvariantCharacterEval_injective A H
  intro h
  let C := homogeneousCochains A
  have hw' := congrArg (fun v : C.X 1 => v.val 1 (h : G)) hw
  change ((C.d 0 1) w).val 1 (h : G) = (C.iCycles 1 z).val 1 (h : G) at hw'
  rw [congrArg (fun f => f 1 (h : G)) (homogeneousCochains.d_apply A 0 w)] at hw'
  change w.val (h : G) - w.val 1 = (C.iCycles 1 z).val 1 (h : G) at hw'
  have hfix := congrArg (fun f => f (h : G)) (w.property (h : G))
  change A.ρ (h : G) (w.val ((h : G)⁻¹ * (h : G))) = w.val (h : G) at hfix
  rw [inv_mul_cancel, htriv h] at hfix
  change (C.iCycles 1 z).val 1 (h : G) = 0
  rw [← hw', ← hfix, sub_self]

/-- Restriction of a degree-one class to the trivialized normal subgroup,
given by the same original crossed homomorphism. -/
def normalOpenH1Restriction : continuousCohomology 1 A →+ ↥(normalOpenInvariantCharacters A H) :=
  let q := (π A 1).hom.toLinearMap.toAddMonoidHom
  q.liftOfSurjective (π_surjective A 1)
    ⟨normalRestrictionCocycleHom A H htriv, normalRestrictionCocycleHom_kernel A H htriv⟩

/-- A restricted class evaluates on the same normalized cocycle representative. -/
theorem normalOpenH1Restriction_π_apply (z : cocycles A 1) (h : (↥H.toSubgroup)) :
    normalOpenInvariantCharacterEval A H h (normalOpenH1Restriction A H htriv (π A 1 z)) =
      (crossedHomOfCocycle A z).toFun h := by
  let q := (π A 1).hom.toLinearMap.toAddMonoidHom
  let v := normalRestrictionCocycleHom A H htriv
  let k := normalRestrictionCocycleHom_kernel A H htriv
  have hcomp : (normalOpenH1Restriction A H htriv).comp q = v :=
    q.liftOfRightInverse_comp (Function.surjInv (π_surjective A 1))
      (Function.rightInverse_surjInv (π_surjective A 1)) ⟨v, k⟩
  exact congrArg (normalOpenInvariantCharacterEval A H h) (DFunLike.congr_fun hcomp z)

variable [CompactSpace G]

/-- If all normal-subgroup evaluations vanish, ordinary restriction also vanishes. -/
theorem openRestriction_one_eq_zero_of_normalRestriction_eq_zero
    (x : continuousCohomology 1 A)
    (hx : normalOpenH1Restriction A H htriv x = 0) : openRestriction A H 1 x = 0 := by
  obtain ⟨z, rfl⟩ := π_surjective A 1 x
  let ι : H.toSubgroup →ₜ* G := ProCGroups.ContinuousMonoidHom.subtype H.toSubgroup
  let R := TopRep.res H.toSubgroup.subtype A
  let w := cocyclesMap ι (𝟙 R) 1 z
  have hπ : openRestriction A H 1 (π A 1 z) = π R 1 w :=
    ConcreteCategory.congr_hom (π_map ι (𝟙 R) 1) z
  have hz (h : (↥H.toSubgroup)) : (crossedHomOfCocycle A z).toFun h = 0 := by
    rw [← normalOpenH1Restriction_π_apply A H htriv z h, hx, map_zero]
  have hw (h : (↥H.toSubgroup)) : (crossedHomOfCocycle R w).toFun h = 0 := by
    have he := resolutionTupleHomeomorph_cochainsMap G A R ι (𝟙 R) 1
      ((homogeneousCochains A).iCycles 1 z) ![1, h]
    have hn : (crossedHomOfCocycle R w).toFun h = (crossedHomOfCocycle A z).toFun h := by
      change ((homogeneousCochains R).iCycles 1 w).val 1 h = _
      exact (congrArg (fun v : (homogeneousCochains R).X 1 => v.val 1 h)
        (cochainOfMappedCocycle ι (𝟙 R) 1 z)).trans he
    exact hn.trans (hz h)
  have hzero : w = 0 := by
    let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
    let i := F.map ((homogeneousCochains R).iCycles 1)
    apply (ModuleCat.mono_iff_injective i).mp inferInstance
    change (homogeneousCochains R).iCycles 1 w = (homogeneousCochains R).iCycles 1 0
    rw [map_zero]
    apply Subtype.ext
    ext a b
    rw [homogeneous_oneCocycle_eq_difference, hw b, hw a, sub_zero]
    rfl
  rw [hπ, hzero, map_zero]

/-- The same invariant character as a crossed homomorphism for the trivialized action. -/
def subgroupCharacterCrossedHom (χ : ↥(normalOpenInvariantCharacters A H)) :
    CrossedHom (TopRep.res H.toSubgroup.subtype A) where
  toFun h := normalOpenInvariantCharacterEval A H h χ
  continuous_toFun := χ.val.toMul.continuous
  map_mul a b := by
    change (χ.val.toMul (a * b)).toAdd = (χ.val.toMul a).toAdd + A.ρ (a : G) (χ.val.toMul b).toAdd
    rw [htriv a]
    exact congrArg Multiplicative.toAdd (map_mul χ.val.toMul a b)

/-- Corestriction followed by normal-subgroup restriction scales evaluations by the index. -/
theorem normalOpenH1Restriction_corestrict_apply
    (χ : ↥(normalOpenInvariantCharacters A H)) (h : ↥H.toSubgroup) :
    normalOpenInvariantCharacterEval A H h
      (normalOpenH1Restriction A H htriv
        (corestrict A H 1 (π (TopRep.res H.toSubgroup.subtype A) 1
          (subgroupCharacterCrossedHom A H htriv χ).toCocycle))) =
      H.toSubgroup.index • normalOpenInvariantCharacterEval A H h χ := by
  let c := subgroupCharacterCrossedHom A H htriv χ
  let z := c.toCocycle
  let R := TopRep.res H.toSubgroup.subtype A
  let b := (homogeneousCochains R).iCycles 1 z
  let r := openSubgroupRetraction H
  let Q := G ⧸ (H : Subgroup G)
  let : Fintype Q := openSubgroupQuotientFintype H
  let v : Fin 2 → G := ![1, (h : G)]
  have hc : corestrict A H 1 (π R 1 z) = π A 1 (corestrictCocycle H A 1 z) :=
    corestrict_π H A 1 z
  rw [hc, normalOpenH1Restriction_π_apply A H htriv]
  change resolutionTupleHomeomorph G A 2 ((homogeneousCochains A).iCycles 1
    (corestrictCocycle H A 1 z)).val v = _
  rw [corestrictCocycle_iCycles H, corestrictCochain_tuple]
  have hq (q : Q) :
      tupleTranslateOnCoset A H 1 b q v = normalOpenInvariantCharacterEval A H h χ := by
    induction q using Quotient.inductionOn with
    | h g =>
      let j := normalOpenConjugate H g⁻¹ h
      have hj : g⁻¹ * (h : G) = (j : G) * g⁻¹ := by
        change g⁻¹ * (h : G) = (g⁻¹ * (h : G) * (g⁻¹)⁻¹) * g⁻¹
        rw [mul_assoc, inv_mul_cancel, mul_one]
      change tupleTranslateOnCoset A H 1 b (QuotientGroup.mk g) v = _
      rw [tupleTranslateOnCoset_mk]
      change A.ρ g (b.val (r (g⁻¹ * 1)) (r (g⁻¹ * (h : G)))) = _
      rw [mul_one, hj, openSubgroupRetraction_subgroup_mul H j]
      have hval : b.val (r g⁻¹) (j * r g⁻¹) = c.toFun j := by
        change ((homogeneousCochains R).iCycles 1 c.toCocycle).val
          (r g⁻¹) (j * r g⁻¹) = c.toFun j
        rw [c.iCycles_toCocycle, CrossedHom.homogeneous_apply, c.map_mul]
        change c.toFun j + A.ρ (j : G) (c.toFun (r g⁻¹)) - c.toFun (r g⁻¹) = c.toFun j
        rw [htriv j, add_sub_cancel_right]
      rw [hval]
      have hχ := χ.property g⁻¹ h
      change c.toFun j = A.ρ g⁻¹ (normalOpenInvariantCharacterEval A H h χ) at hχ
      rw [hχ]
      have he := DFunLike.congr_fun (map_mul A.ρ g g⁻¹) (normalOpenInvariantCharacterEval A H h χ)
      rw [mul_inv_cancel, map_one] at he
      exact he.symm
  have hs : (∑ q : Q, tupleTranslateOnCoset A H 1 b q v) =
      ∑ _ : Q, normalOpenInvariantCharacterEval A H h χ := Finset.sum_congr rfl (fun q _ => hq q)
  rw [hs, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← H.toSubgroup.index_eq_card]

/-- If the normal open subgroup acts trivially and has index prime to `p`,
restriction identifies degree-one continuous cohomology with the invariant
continuous characters of that subgroup. Corestriction supplies the extension. -/
def normalOpenH1RestrictionEquiv (p : ℕ) [Fact p.Prime]
    (hpA : ∀ a : A, p • a = 0) (hindex : ¬ p ∣ H.toSubgroup.index) :
    continuousCohomology 1 A ≃+ ↥(normalOpenInvariantCharacters A H) := by
  apply AddEquiv.ofBijective (normalOpenH1Restriction A H htriv)
  constructor
  · apply (injective_iff_map_eq_zero (normalOpenH1Restriction A H htriv)).mpr
    intro x hx
    have hx' := openRestriction_one_eq_zero_of_normalRestriction_eq_zero A H htriv x hx
    have hmul : H.toSubgroup.index • x = 0 := by
      rw [← corestrict_openRestriction_one H A, hx', map_zero]
    by_contra hne
    have hp := nsmul_continuousCohomology_eq_zero_of_coefficients A p hpA 1 x
    have horder : addOrderOf x = p := addOrderOf_eq_prime hp hne
    exact hindex (horder ▸ addOrderOf_dvd_of_nsmul_eq_zero hmul)
  · intro χ
    let d := H.toSubgroup.index
    let k := Nat.gcdA d p
    let j := Nat.gcdB d p
    have hdp : d.Coprime p := ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hindex).symm
    have hgcd : ((Nat.gcd d p : ℕ) : ℤ) = 1 := congrArg Int.ofNat hdp.gcd_eq_one
    have hbez : (d : ℤ) * k + (p : ℤ) * j = 1 := (Nat.gcd_eq_gcd_ab d p).symm.trans hgcd
    let c := subgroupCharacterCrossedHom A H htriv χ
    let x := corestrict A H 1 (π (TopRep.res H.toSubgroup.subtype A) 1 c.toCocycle)
    refine ⟨k • x, normalOpenInvariantCharacterEval_injective A H (fun h => ?_)⟩
    rw [map_zsmul, map_zsmul]
    have hx : normalOpenInvariantCharacterEval A H h (normalOpenH1Restriction A H htriv x) =
        d • normalOpenInvariantCharacterEval A H h χ :=
      normalOpenH1Restriction_corestrict_apply A H htriv χ h
    rw [hx]
    let a := normalOpenInvariantCharacterEval A H h χ
    have hp : (p : ℤ) • a = 0 := by simpa only [natCast_zsmul] using hpA a
    calc
      k • (d • a) = ((d : ℤ) * k) • a := by rw [mul_comm (d : ℤ) k, mul_smul, natCast_zsmul]
      _ = ((d : ℤ) * k + (p : ℤ) * j) • a := by
        rw [add_smul, mul_comm (p : ℤ) j, mul_smul j (p : ℤ) a, hp, smul_zero, add_zero]
      _ = a := by rw [hbez, one_zsmul]

/-- The equivalence evaluates the same normalized representative as ordinary restriction. -/
theorem normalOpenH1RestrictionEquiv_π_apply (p : ℕ) [Fact p.Prime]
    (hpA : ∀ a : A, p • a = 0) (hindex : ¬ p ∣ H.toSubgroup.index)
    (z : cocycles A 1) (h : (↥H.toSubgroup)) :
    normalOpenInvariantCharacterEval A H h
      (normalOpenH1RestrictionEquiv A H htriv p hpA hindex (π A 1 z)) =
      (crossedHomOfCocycle A z).toFun h :=
  normalOpenH1Restriction_π_apply A H htriv z h

end ContinuousCohomology
