/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeRegularTerm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePerfectness
public import Mathlib.RepresentationTheory.Invariants

/-! # The valuation contribution in the coprime Euler calculation -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep
open scoped Ring ValuativeRel MonoidAlgebra

noncomputable section

namespace Representation

universe u

variable {k G V W : Type*} [Field k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V)

/-- Restrict an invariant linear map to the invariant vectors. The inverse
is the actual averaging projection. -/
def invariantLinearMapEquiv :
    { f : V →ₗ[k] W // ∀ g x, f (ρ g x) = f x } ≃ (ρ.invariants →ₗ[k] W) := by
  let a := (averageMap ρ).codRestrict ρ.invariants (averageMap_invariant ρ)
  have hac (g : G) (x : V) : a (ρ g x) = a x := by
    apply Subtype.ext
    change averageMap ρ (ρ g x) = averageMap ρ x
    rw [averageMap, ← asAlgebraHom_single_one, ← mul_apply_eq_comp,
      ← map_mul, GroupAlgebra.mul_average_right]
  refine
    { toFun := fun f => f.val.comp ρ.invariants.subtype
      invFun := fun f => ⟨f.comp a, fun g x => congrArg f (hac g x)⟩
      left_inv := ?_, right_inv := ?_ }
  · intro f
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change f.val (averageMap ρ x) = f.val x
    simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, LinearMap.smul_apply,
      LinearMap.sum_apply, MonoidAlgebra.of_apply, asAlgebraHom_single_one, f.property,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul,
      invOf_mul_self, one_smul]
  · intro f
    apply LinearMap.ext
    intro x
    apply congrArg f
    exact Subtype.ext (averageMap_id ρ x.val x.property)

/-- Retain the action on a coefficient group equipped with scalar multiplication by `ZMod p`. -/
def overZMod {J V : Type*} [Group J] [AddCommGroup V] [Module ℤ V]
    (p : ℕ) [Module (ZMod p) V] (r : Representation ℤ J V) :
    Representation (ZMod p) J V := by
  let act (g : J) : Module.End (ZMod p) V := (r g).toAddMonoidHom.toZModLinearMap p
  let mulOne : MulOne (Module.End (ZMod p) V) := Module.End.instMonoid.toMulOne
  exact @MonoidHom.mk J (Module.End (ZMod p) V) inferInstance mulOne
    ⟨act, LinearMap.ext fun x => DFunLike.congr_fun (map_one r) x⟩
    (fun g h => LinearMap.ext fun x => DFunLike.congr_fun (map_mul r g h) x)

private def invariantsEquivOfSurjectiveRestriction
    {G Q V : Type u} [Group G] [Group Q] [TopologicalSpace G] [IsTopologicalGroup G]
    {k : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    (r : G →* Q) (hr : Function.Surjective r) (C : TopRep.{u} ℤ G) (ρ : Representation k Q V)
    (e : C ≃+ V) (he : ∀ g x, e (C.ρ g x) = ρ (r g) (e x)) :
    C.invariants ≃+ ↥(ρ.invariants) where
  toFun x := ⟨e x.val, fun q => by
    obtain ⟨g, rfl⟩ := hr q
    exact (he g x.val).symm.trans (congrArg e (x.property g))⟩
  invFun x := ⟨e.symm x.val, fun g => by
    apply e.injective
    exact (he g (e.symm x.val)).trans
      ((congrArg (ρ (r g)) (e.apply_symm_apply x.val)).trans
        ((x.property (r g)).trans (e.apply_symm_apply x.val).symm))⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)

private theorem natCard_equivariant_to_trivialPrime
    {Q V H : Type u} [Group Q] [Fintype Q] [AddCommGroup V] [mV : Module ℤ V]
    [AddCommGroup H] (p : ℕ) [Fact p.Prime] [Module (ZMod p) V]
    (r : Representation ℤ Q V) (hQ : (Fintype.card Q : ZMod p) ≠ 0)
    (e : H ≃+ ↥(r.invariants)) :
    Nat.card { f : V →ₗ[ℤ] ULift.{u} (ZMod p) // ∀ g : Q, ∀ v, f (r g v) = f v } =
      Nat.card (H →+ ZMod p) := by
  let ρ := overZMod p r
  let T := ULift.{u} (ZMod p)
  let lift (f : V →ₗ[ZMod p] ZMod p) : V →ₗ[ℤ] T :=
    let a : V →+ T :=
      (AddEquiv.ulift : T ≃+ ZMod p).symm.toAddMonoidHom.comp f.toAddMonoidHom
    { toFun := a
      map_add' := a.map_add
      map_smul' := fun n x =>
        (congrArg a (int_smul_eq_zsmul mV n x)).trans
          ((map_zsmul a n x).trans (int_smul_eq_zsmul (inferInstance : Module ℤ T) n (a x)).symm) }
  let e₁ : { f : V →ₗ[ℤ] T // ∀ g : Q, ∀ v, f (r g v) = f v } ≃
      { f : V →ₗ[ZMod p] ZMod p // ∀ g : Q, ∀ v, f (ρ g v) = f v } :=
    { toFun := fun f => ⟨((ULift.moduleEquiv : T ≃ₗ[ℤ] ZMod p).toLinearMap.comp
          f.val).toAddMonoidHom.toZModLinearMap p, fun g v => congrArg ULift.down (f.property g v)⟩
      invFun := fun f => ⟨lift f.val, fun g v => congrArg ULift.up (f.property g v)⟩
      left_inv := fun f => Subtype.ext (LinearMap.ext fun _ => rfl)
      right_inv := fun f => Subtype.ext (LinearMap.ext fun _ => rfl) }
  let e₂ : ↥(r.invariants) ≃+ ↥(ρ.invariants) :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let e₀ := e.trans e₂
  let e₃ : (ρ.invariants →ₗ[ZMod p] ZMod p) ≃ (H →+ ZMod p) :=
    { toFun := fun f => f.toAddMonoidHom.comp e₀.toAddMonoidHom
      invFun := fun f => (f.comp e₀.symm.toAddMonoidHom).toZModLinearMap p
      left_inv := fun f => LinearMap.ext fun x => congrArg f (e₀.apply_symm_apply x)
      right_inv := fun f => AddMonoidHom.ext fun x => congrArg f (e₀.symm_apply_apply x) }
  let : Invertible (Fintype.card Q : ZMod p) := invertibleOfNonzero hQ
  exact Nat.card_congr (e₁.trans ((invariantLinearMapEquiv ρ).trans e₃))

end Representation

namespace ClassFieldTheory.Brauer

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

local notation "Q" => Gal(L/K)
local notation "V" => localValueRep K L

/-- Reduction of the actual value group gives the trivial prime coefficient. -/
def localValuePowerReductionIso (p : ℕ) :
    Rep.powerReduction V p ≅ Rep.trivial (k := ℤ) (G := Q) (ULift.{u} (ZMod p)) := by
  let f : V →ₗ[ℤ] ULift.{u} (ZMod p) :=
    (ULift.moduleEquiv.symm : ZMod p ≃ₗ[ℤ] ULift.{u} (ZMod p)).toLinearMap.comp
      ((Int.castRingHom (ZMod p)).toAddMonoidHom.toIntLinearMap.comp
        (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).toLinearMap)
  have hf : Function.Surjective f :=
    ULift.moduleEquiv.symm.surjective.comp
      (ZMod.intCast_surjective.comp ULift.moduleEquiv.surjective)
  let T := LinearMap.range (LinearMap.nsmulLinear (R := ℤ) p V)
  have hker : T = LinearMap.ker f := by
    ext x
    change (∃ y : ULift.{u} ℤ, p • y = x) ↔
      (ULift.up ((x.down : ℤ) : ZMod p) : ULift.{u} (ZMod p)) = ULift.up 0
    rw [ULift.up.injEq, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.down, (natCast_zsmul y.down p).symm.trans (Int.zsmul_eq_mul _ _)⟩
    · rintro ⟨a, ha⟩
      exact ⟨ULift.up a, ULift.ext ((natCast_zsmul a p).symm.trans
        ((Int.zsmul_eq_mul _ _).trans ha.symm))⟩
  let e := (Submodule.quotEquivOfEq T _ hker).trans (f.quotKerEquivOfSurjective hf)
  refine Rep.mkIso (Representation.Equiv.mk e ?_)
  intro g
  apply LinearMap.ext
  intro x
  change e (LinearMap.powerReductionMap p LinearMap.id x) = e x
  rw [LinearMap.powerReductionMap_id, LinearMap.id_apply]

end ClassFieldTheory.Brauer

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (p : ℕ) [Fact p.Prime]

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Q" => Gal(E/K)
local notation "F" => localGaloisGroupAlgebraFunctor K E
local notation "W" => localValueRep K E
local notation "X" =>
  (ModuleCat.carrier (Functor.obj F W)) ⧸
    LinearMap.range (LinearMap.nsmulLinear (R := ℤ[Q]) p (ModuleCat.carrier (Functor.obj F W)))
local notation "Mu" => separableMuTopRep K p
local notation "n" => (Subtype.mk p (Nat.Prime.pos (Fact.out : p.Prime)) : ℕ+)

variable (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [Finite A] [DiscreteTopology A]
    (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ (h : ↥(stageOpenFixingSubgroup K E.toIntermediateField).toSubgroup) (a : A),
      A.ρ (h : Gal(SeparableClosure K/K)) a = a)

local notation "D" => discreteLinearDual (R := ℤ) (G := Γabs) A Mu
local notation "V" => coprimeStageDualRep K E p ζ hζ A hfix

/-- The actual valuation term is the degree-two group detected by the
original local Tate pairing with invariant dual coefficients. -/
theorem coprimeStageEulerValueHom_card
    (hdeg : ¬p ∣ Module.finrank K E) (hA : ∀ a : A, p • a = 0)
    (hAc : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2)) :
    Nat.card (((F).obj V) →ₗ[ℤ[Q]] X) = Nat.card (continuousCohomology 2 A) := by
  let T := Rep.trivial (k := ℤ) (G := Q) (ULift.{u} (ZMod p))
  let ep := Rep.powerReductionModuleEquiv W p
  let j := (F).mapIso (localValuePowerReductionIso K E p)
  let η : X ≃ₗ[ℤ[Q]] (F).obj T := ep.trans
    (LinearEquiv.ofBijective j.hom.hom (ConcreteCategory.bijective_of_isIso j.hom))
  let e₀ : (((F).obj V) →ₗ[ℤ[Q]] X) ≃ (((F).obj V) →ₗ[ℤ[Q]] (F).obj T) :=
    { toFun := fun f => η.toLinearMap.comp f
      invFun := fun f => η.symm.toLinearMap.comp f
      left_inv := fun f => LinearMap.ext fun x => η.symm_apply_apply (f x)
      right_inv := fun f => LinearMap.ext fun x => η.apply_symm_apply (f x) }
  have hpD (l : V) : p • l = 0 := by
    let : Module ℤ A := A.hV2
    let : Module ℤ Mu := (Mu).hV2
    let f : A →ₗ[ℤ] Mu := discreteLinearDualMap A Mu l
    have hf : p • f = 0 := LinearMap.ext fun a =>
      separableMuTopRep_nsmul_eq_zero K p (f a)
    exact hf
  let : Fintype Q := Fintype.ofFinite Q
  have hQ : (Fintype.card Q : ZMod p) ≠ 0 := by
    intro hzero
    have hcard : Fintype.card Q = Module.finrank K E :=
      Nat.card_eq_fintype_card.symm.trans (IsGalois.card_aut_eq_finrank K E)
    exact hdeg (hcard ▸ (ZMod.natCast_eq_zero_iff (Fintype.card Q) p).mp hzero)
  let r := (finiteGaloisRestriction E).toMonoidHom
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective (SeparableClosure K)
  let D₀ : TopRep.{u} ℤ Γabs := D
  let e₂ := Representation.invariantsEquivOfSurjectiveRestriction r hr D₀ (V).ρ (AddEquiv.refl _)
    (fun g x => (coprimeStageDualRep_ρ K E p ζ hζ A hfix g x).symm)
  let c : continuousCohomology.{0,u,u} 0 D₀ ≅ D₀.invariants :=
    ContinuousCohomology.zeroIso.{0,u,u} D₀
  let c₀ : continuousCohomology.{0,u,u} 0 D₀ ≃+ D₀.invariants :=
    AddEquiv.ofBijective c.hom.hom.toLinearMap.toAddMonoidHom
      (ConcreteCategory.bijective_of_isIso c.hom)
  let scalar : Module (ZMod p) V := AddCommGroup.zmodModule hpD
  let : Module (ZMod p) V := scalar
  have hcard : Nat.card { f : V →ₗ[ℤ] T // ∀ g : Q, ∀ l, f ((V).ρ g l) = f l } =
      Nat.card (continuousCohomology.{0,u,u} 0 D₀ →+ ZMod p) :=
    Representation.natCard_equivariant_to_trivialPrime p (V).ρ hQ (c₀.trans e₂)
  let a := localTatePairingTwoAdjoint K n A (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have ha : Function.Bijective a := (localTatePairingAdjoints_bijective K n A
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hAc hA).2.2
  let e₄ := (equivariantMapGroupAlgebraEquiv K E V T).symm
  exact (Nat.card_congr (e₀.trans e₄)).trans
    (hcard.trans (Nat.card_congr (Equiv.ofBijective a ha).symm))

end ClassFieldTheory.Brauer
