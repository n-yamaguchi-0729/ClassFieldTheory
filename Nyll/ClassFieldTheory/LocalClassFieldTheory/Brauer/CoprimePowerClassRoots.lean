/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimePowerClasses
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # The Galois action on coprime local unit power classes -/

@[expose] public section

noncomputable section

open CategoryTheory LocalClassFieldTheory LocalFieldTheory
open ValuationTheory.DiscreteValuationField
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

local notation "G" => Gal(L/K)

/-- Actual field roots of unity, with their original Galois action. -/
def localFieldRootsRep (n : ℕ) : Rep.{u} ℤ G :=
  Rep.of (X := Additive (rootsOfUnity n L))
    { toFun := fun g => (restrictRootsOfUnity g.toRingHom n).toAdditive.toIntLinearMap
      map_one' := by
        apply LinearMap.ext
        intro z
        apply Additive.toMul.injective
        apply rootsOfUnity.coe_injective
        rfl
      map_mul' g h := by
        apply LinearMap.ext
        intro z
        apply Additive.toMul.injective
        apply rootsOfUnity.coe_injective
        rfl }

variable [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

/-- Reduce the actual field roots of unity of order prime to the residue characteristic. -/
def localFieldRootsReduction (n : ℕ) [NeZero (n : 𝓀[L])] :
    rootsOfUnity n L ≃* rootsOfUnity n 𝓀[L] := by
  let D := (localCompleteDVF L).toHenselianDVF
  let : NeZero (n : D.residueField) := inferInstanceAs (NeZero (n : 𝓀[L]))
  exact D.fieldRootsOfUnityReductionEquiv n

variable [ValuativeRel K]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- Reducing a conjugated root gives the conjugate of its residue. -/
theorem localFieldRootsReduction_galois (n : ℕ) [NeZero (n : 𝓀[L])]
    (g : G) (z : rootsOfUnity n L) :
    localFieldRootsReduction L n (restrictRootsOfUnity g.toRingHom n z) =
      restrictRootsOfUnity (galoisGroupResidueFieldEquivOfIsIntegralClosure K L g).toRingHom
        n (localFieldRootsReduction L n z) := by
  let D := (localCompleteDVF L).toHenselianDVF
  let : NeZero (n : D.residueField) := inferInstanceAs (NeZero (n : 𝓀[L]))
  let : NeZero n := NeZero.of_neZero_natCast 𝓀[L]
  let e := HenselianDVF.rootsOfUnityFieldEquiv D.toDVF n
  obtain ⟨a, rfl⟩ := e.surjective z
  let gO := galoisGroupIntegerRingEquivOfIsIntegralClosure K L g
  have h : restrictRootsOfUnity g.toRingHom n (e a) =
      e (restrictRootsOfUnity gO.toRingHom n a) := by
    apply rootsOfUnity.coe_injective
    exact (galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L g a.val.val).symm
  rw [h]
  change D.fieldRootsOfUnityReductionEquiv n
      (restrictRootsOfUnity (algebraMap D.valuationSubring L) n
        (restrictRootsOfUnity gO.toRingHom n a)) =
    restrictRootsOfUnity (galoisGroupResidueFieldEquivOfIsIntegralClosure K L g).toRingHom n
      (D.fieldRootsOfUnityReductionEquiv n
        (restrictRootsOfUnity (algebraMap D.valuationSubring L) n a))
  let r := galoisGroupResidueFieldEquivOfIsIntegralClosure K L g
  have hL := HenselianDVF.fieldRootsOfUnityReductionEquiv_toField D n
    (restrictRootsOfUnity gO.toRingHom n a)
  have hR := HenselianDVF.fieldRootsOfUnityReductionEquiv_toField D n a
  have hEq : D.rootsOfUnityReduction n (restrictRootsOfUnity gO.toRingHom n a) =
      restrictRootsOfUnity r.toRingHom n (D.rootsOfUnityReduction n a) := by
    apply rootsOfUnity.coe_injective
    exact (galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L g a.val.val).symm
  exact hL.trans (hEq.trans (congrArg (restrictRootsOfUnity r.toRingHom n) hR.symm))

section Primitive

variable [Fintype 𝓀[L]] (n : ℕ+) [NeZero ((n : ℕ) : 𝓀[L])]

/-- A primitive root in the original field has the same order in the residue field. -/
theorem localFieldRootOrder_dvd_residueUnits (prim : ∃ z : L, IsPrimitiveRoot z (n : ℕ)) :
    (n : ℕ) ∣ Fintype.card 𝓀[L] - 1 := by
  classical
  obtain ⟨z, hz⟩ := prim
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let a : rootsOfUnity (n : ℕ) L := rootsOfUnity.mkOfPowEq z hz.pow_eq_one
  let r := localFieldRootsReduction L (n : ℕ) a
  have ha : orderOf a = (n : ℕ) := by
    rw [← Subgroup.orderOf_coe a, ← orderOf_units]
    exact hz.eq_orderOf.symm
  have hr : orderOf r.val = (n : ℕ) :=
    (Subgroup.orderOf_coe r).trans (((localFieldRootsReduction L (n : ℕ)).orderOf_eq a).trans ha)
  rw [← hr, ← Fintype.card_units]
  exact orderOf_dvd_card

local notation "O" => localIntegerUnitRep K L
local notation "RootRep" => localFieldRootsRep K L (n : ℕ)
local notation "Q" => Rep.powerReduction O (n : ℕ)
local notation "N" => LinearMap.range (LinearMap.nsmulLinear (R := ℤ) (n : ℕ) O)

/-- The original integer-unit power quotient identifies equivariantly with the original
field roots of unity by reduction and the finite-field power residue symbol. -/
def localIntegerPowerClassRootsIso (hn : (n : ℕ) ∣ Fintype.card 𝓀[L] - 1) :
    Q ≅ RootRep := by
  let d := localFieldRootsReduction L (n : ℕ)
  let s := integerUnitResiduePowerSymbol L n hn
  let f : O →ₗ[ℤ] RootRep := (d.symm.toMonoidHom.comp s).toAdditive.toIntLinearMap
  have hker (a : O) : f a = 0 ↔ a ∈ N := by
    let u : 𝒪[L]ˣ := Additive.toMul a
    change d.symm (s u) = 1 ↔ _
    have hd : d.symm (s u) = 1 ↔ s u = 1 := d.symm.map_eq_one_iff
    refine hd.trans ((integerUnitResiduePowerSymbol_eq_one_iff L n hn u).trans ?_)
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
    · rintro ⟨b, hb⟩
      exact ⟨Additive.toMul b, congrArg Additive.toMul hb⟩
  let fQ : Q →ₗ[ℤ] RootRep := (N).liftQ f (fun a ha => (hker a).mpr ha)
  have hfi : Function.Injective fQ := by
    apply (injective_iff_map_eq_zero fQ).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := (N).mkQ_surjective x
    have ha : f a = 0 := hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((hker a).mp ha)
  have hfs : Function.Surjective fQ := by
    intro z
    let e := integerUnitPowerClassesResidueEquiv L n hn
    let zu : rootsOfUnity (n : ℕ) L := Additive.toMul z
    obtain ⟨q, hq⟩ := e.surjective (d zu)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (n : ℕ) : 𝒪[L]ˣ →* 𝒪[L]ˣ).range q
    refine ⟨(N).mkQ (Additive.ofMul a), ?_⟩
    apply Additive.toMul.injective
    apply d.injective
    change d (d.symm (s a)) = d zu
    rw [d.apply_symm_apply]
    exact hq
  let e := LinearEquiv.ofBijective fQ ⟨hfi, hfs⟩
  refine Rep.mkIso (Representation.Equiv.mk e ?_)
  intro g
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (N).mkQ_surjective x
  apply Additive.toMul.injective
  apply d.injective
  let u : 𝒪[L]ˣ := Additive.toMul a
  change d (d.symm (s (Units.mapEquiv
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K L g).toMulEquiv u))) =
    d (restrictRootsOfUnity g.toRingHom (n : ℕ) (d.symm (s u)))
  rw [localFieldRootsReduction_galois K L, d.apply_symm_apply, d.apply_symm_apply]
  exact integerUnitResiduePowerSymbol_galois K L n hn g u

/-- Insert the field roots by the inverse of the integer-unit power-class comparison. -/
def localRootsPowerClassInclusion (hn : (n : ℕ) ∣ Fintype.card 𝓀[L] - 1) :
    RootRep ⟶ Rep.powerReduction (Rep.ofAlgebraAutOnUnits K L) (n : ℕ) :=
  (localIntegerPowerClassRootsIso K L n hn).inv ≫
    localIntegerUnitPowerClassInclusion K L (n : ℕ)

/-- The original valuation on field power classes has the field roots of unity as its
equivariant kernel under the residue comparison. -/
theorem localRootsPowerClassValuation_exact (hn : (n : ℕ) ∣ Fintype.card 𝓀[L] - 1) :
    Function.Injective (localRootsPowerClassInclusion K L n hn) ∧
      Function.Exact (localRootsPowerClassInclusion K L n hn) (localPowerClassValuation K L n) ∧
      Function.Surjective (localPowerClassValuation K L n) := by
  let e := localIntegerPowerClassRootsIso K L n hn
  let i := localIntegerUnitPowerClassInclusion K L n
  let q := localPowerClassValuation K L n
  obtain ⟨hi, hex, hq⟩ := localPowerClassValuation_exact K L n n.pos
  have he : Function.Injective e.inv := by
    intro x y h
    exact (Iso.inv_hom_id_apply e x).symm.trans
      ((congrArg e.hom h).trans (Iso.inv_hom_id_apply e y))
  change Function.Injective (fun x => i (e.inv x)) ∧
    Function.Exact (fun x => i (e.inv x)) q ∧ Function.Surjective q
  refine ⟨hi.comp he, ?_, hq⟩
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (hex x).mp hx
    exact ⟨e.hom a, (congrArg i (Iso.hom_inv_id_apply e a)).trans ha⟩
  · rintro ⟨a, ha⟩
    exact (hex x).mpr ⟨e.inv a, ha⟩

end Primitive

end ClassFieldTheory.Brauer
