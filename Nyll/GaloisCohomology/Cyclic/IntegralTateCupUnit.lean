/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupConnecting

/-!
# The unit class of the integral Tate cup product

The class represented by `1` in trivial integer coefficients acts as the
unit on the original Tate groups in all integer degrees. The right unit
formula holds on fixed representatives. The left unit formula follows by
the canonical upward and downward shifts and the left tensor unitor.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped RepTensor BigOperators TensorProduct

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- The original trivial integral representation in the group's carrier universe. -/
abbrev integralCupUnitRep (G : Type u) [Group G] : Rep.{u} ℤ G :=
  integralTrivialInteger.{u, u} G

local notation "I" => integralCupUnitRep G

/-- The original degree-zero Tate class of the integer `1`. -/
def tateCupUnit (G : Type u) [Group G] [Fintype G] : tate (integralTrivialInteger.{u, u} G) 0 :=
  fixedClass _ ⟨integralTrivialIntegerOne G, fun _ => rfl⟩

/-- The degree-zero unit acts on the right in every integer degree. -/
theorem tateCup_right_unit (A : Rep.{u} ℤ G) (n : ℤ) (x : tate A n) :
    (tateFunctor G n).map (integerTensorRightUnitIso A).hom
      (tateCup A I n 0 n (add_zero n) x (tateCupUnit G)) = x := by
  let one : (I).ρ.invariants := ⟨integralTrivialIntegerOne G, fun _ => rfl⟩
  change (tateFunctor G n).map (integerTensorRightUnitIso A).hom
    (tateCup A I n 0 n (add_zero n) x (fixedClass I one)) = x
  rw [tateCup_zero_right, tensorCupZeroRight_fixedClass]
  have h : Rep.tensorInvariant A I one ≫ (integerTensorRightUnitIso A).hom = 𝟙 A := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro a
    change (integerTensorRightUnitIso A).hom (a ⊗ₜ[ℤ] (one : I)) = a
    exact (integerTensorRightUnitIso_tmul A a (one : I)).trans (one_smul ℤ a)
  change ((tateFunctor G n).map (Rep.tensorInvariant A I one) ≫
    (tateFunctor G n).map (integerTensorRightUnitIso A).hom) x = x
  have h₁ := (Functor.map_comp (tateFunctor G n) _ _).symm.trans
    ((congrArg (tateFunctor G n).map h).trans ((tateFunctor G n).map_id A))
  exact ConcreteCategory.congr_hom h₁ x

/-- Cup with the unit on the left, followed by the original left tensor unitor. -/
def tateCupUnitLeft (A : Rep.{u} ℤ G) (n : ℤ) (x : tate A n) : tate A n :=
  (tateFunctor G n).map (integerTensorLeftUnitIso A).hom
    (tateCup I A 0 n n (zero_add n) (tateCupUnit G) x)

private theorem tateCupUnitLeft_zero (A : Rep.{u} ℤ G) (x : tate A 0) :
    tateCupUnitLeft A 0 x = x := by
  obtain ⟨a, rfl⟩ := fixedClass_surjective A x
  unfold tateCupUnitLeft tateCupUnit
  rw [tateCup_zero_right, tensorCupZeroRight_fixedClasses, fixedClass_map]
  apply congrArg (fixedClass A)
  apply Subtype.ext
  change (integerTensorLeftUnitIso A).hom (integralTrivialIntegerOne G ⊗ₜ[ℤ] (a : A)) = (a : A)
  exact (integerTensorLeftUnitIso_tmul A (integralTrivialIntegerOne G) a).trans (one_smul ℤ (a : A))

private theorem tateCupUnitLeft_connecting {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (n : ℤ) (x : tate S.X₃ n) :
    tateCupUnitLeft S.X₁ (n + 1) (tateδ hS n x) = tateδ hS n (tateCupUnitLeft S.X₃ n x) := by
  let hT := Rep.tensorLeft_shortExact_of_forget_splitting I s
  let f := S.mapNatTrans (integerTensorLeftUnitNatTrans G)
  let c := tateCup I S.X₃ 0 n n (zero_add n) (tateCupUnit G) x
  unfold tateCupUnitLeft
  rw [tateCup_connecting_right I hS s (zero_add n), Int.negOnePow_zero, one_smul]
  exact congrArg (fun m : tate (I ⊗ᵣ S.X₃) n ⟶ tate S.X₁ (n + 1) => m c)
    (tateδ_naturality hT hS f n)

private theorem tateCupUnitLeft_indShift (A : Rep.{u} ℤ G) (n : ℤ) (x : tate A n) :
    tateCupUnitLeft (Rep.indShiftDown A) (n + 1) (indShiftDownEquiv A n x) =
      indShiftDownEquiv A n (tateCupUnitLeft A n x) :=
  tateCupUnitLeft_connecting (S := Rep.indShiftSequence A)
    (Rep.indShiftSequence_shortExact A) (Rep.indShiftSequence_forget_splitting A) n x

private theorem tateCupUnitLeft_eq_of_indShift (A : Rep.{u} ℤ G) (n : ℤ) (x : tate A n)
    (he : tateCupUnitLeft (Rep.indShiftDown A) (n + 1) (indShiftDownEquiv A n x) =
      indShiftDownEquiv A n x) : tateCupUnitLeft A n x = x :=
  (indShiftDownEquiv A n).injective ((tateCupUnitLeft_indShift A n x).symm.trans he)

private theorem tateCupUnitLeft_ofNat (i : ℕ) (A : Rep.{u} ℤ G) (x : tate A i) :
    tateCupUnitLeft A i x = x := by
  induction i generalizing A with
  | zero => exact tateCupUnitLeft_zero A x
  | succ i ih =>
    obtain ⟨y, rfl⟩ := (coindShiftUpEquiv A i).surjective x
    have h := tateCupUnitLeft_connecting (Rep.coindShiftSequence_shortExact A)
      (Rep.coindShiftSequence_forget_splitting A) i y
    change tateCupUnitLeft A (i + 1 : ℕ) (coindShiftUpEquiv A i y) =
      coindShiftUpEquiv A i (tateCupUnitLeft (Rep.coindShiftUp A) i y) at h
    exact h.trans (congrArg (coindShiftUpEquiv A i) (ih (Rep.coindShiftUp A) y))

private theorem tateCupUnitLeft_negSucc (i : ℕ) (A : Rep.{u} ℤ G) (x : tate A (Int.negSucc i)) :
    tateCupUnitLeft A (Int.negSucc i) x = x := by
  induction i generalizing A with
  | zero =>
    exact tateCupUnitLeft_eq_of_indShift A (Int.negSucc 0) x
      (tateCupUnitLeft_zero (Rep.indShiftDown A) (indShiftDownEquiv A (Int.negSucc 0) x))
  | succ i ih =>
    let n := Int.negSucc (i + 1)
    exact tateCupUnitLeft_eq_of_indShift A n x
      (ih (Rep.indShiftDown A) (indShiftDownEquiv A n x))

/-- The degree-zero unit acts on the left in every integer degree. -/
theorem tateCup_left_unit (A : Rep.{u} ℤ G) (n : ℤ) (x : tate A n) : tateCupUnitLeft A n x = x := by
  cases n with
  | ofNat i => exact tateCupUnitLeft_ofNat i A x
  | negSucc i => exact tateCupUnitLeft_negSucc i A x

/-- The original norm on the trivial integer representation multiplies by the group order. -/
theorem tateTrivialInteger_norm (z : I) : ((I).ρ.norm z).down = (Fintype.card G : ℤ) * z.down := by
  change ((∑ g : G, (I).ρ g) z : I).down = _
  rw [LinearMap.sum_apply]
  have hρ (g : G) : (I).ρ g z = z := rfl
  simp only [hρ, Finset.sum_const, Finset.card_univ]
  change (Fintype.card G : ℕ) • z.down = _
  exact nsmul_eq_mul _ _

/-- Degree-zero Tate with the original trivial integer coefficients is reduction
modulo the actual order of the acting group. -/
def tateTrivialZeroEquivZMod : tate I 0 ≃+ ZMod (Fintype.card G) := by
  let down : (I).ρ.invariants →ₗ[ℤ] ℤ :=
    (ULift.moduleEquiv : I ≃ₗ[ℤ] ℤ).toLinearMap.comp (I).ρ.invariants.subtype
  let f : (I).ρ.invariants →ₗ[ℤ] ZMod (Fintype.card G) :=
    (Int.castAddHom (ZMod (Fintype.card G))).toIntLinearMap.comp down
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective x
    exact ⟨⟨ULift.up z, fun _ => rfl⟩, hz⟩
  have hker : fixedNormSubmodule I = LinearMap.ker f := by
    ext x
    change (∃ z : I, (I).ρ.norm z = (x : I)) ↔ (((x : I).down) : ZMod (Fintype.card G)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z.down, (congrArg ULift.down hz).symm.trans (tateTrivialInteger_norm z)⟩
    · rintro ⟨z, hz⟩
      refine ⟨ULift.up z, ?_⟩
      apply ULift.ext
      exact (tateTrivialInteger_norm (ULift.up z : I)).trans hz.symm
  exact (tateZeroEquivFixedQuotient I).trans
    (((Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hf)).toAddEquiv)

/-- A map from trivial degree-zero Tate coefficients is bijective when the
image of the unit generates a target of the correct order. -/
theorem tateTrivialZero_map_bijective {B : ModuleCat.{u} ℤ} (f : tate I 0 →ₗ[ℤ] B)
    (hgen : ∀ z : B, ∃ m : ℤ, m • f (tateCupUnit G) = z) (hcard : Nat.card B = Nat.card G) :
    Function.Bijective f := by
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨m, hm⟩ := hgen z
    refine ⟨m • tateCupUnit G, ?_⟩
    rw [map_zsmul, hm]
  have hsource : Nat.card (tate I 0) = Nat.card G := by
    rw [Nat.card_congr (tateTrivialZeroEquivZMod (G := G)).toEquiv, Nat.card_zmod,
      Nat.card_eq_fintype_card]
  have : Finite (tate I 0) := Nat.finite_of_card_ne_zero (hsource.trans_ne Nat.card_pos.ne')
  have : Finite B := Nat.finite_of_card_ne_zero (hcard.trans_ne Nat.card_pos.ne')
  exact (Nat.bijective_iff_surjective_and_card f).2 ⟨hs, hsource.trans hcard.symm⟩

/-- The degree-zero cup map is bijective when the class generates its target
and the target has the order of the finite group. The map is the original
bilinear cup product evaluated against that class. -/
theorem tateCup_class_bijective_zero (A : Rep.{u} ℤ G) (y : tate A 2)
    (hgen : ∀ z : tate A 2, ∃ m : ℤ, m • y = z)
    (hcard : Nat.card (tate A 2) = Nat.card G) :
    Function.Bijective (fun x : tate I 0 =>
      (tateFunctor G 2).map (integerTensorLeftUnitIso A).hom
        (tateCup I A 0 2 2 (by decide) x y)) := by
  let cup := tateCup I A 0 2 2 (by decide)
  let C := tate I 0
  let D := tate (I ⊗ᵣ A) 2
  let eval : C →+ D :=
    { toFun := fun x => cup x y
      map_zero' := congrArg (fun m => m y) cup.map_zero
      map_add' := fun x z => congrArg (fun m => m y) (cup.map_add x z) }
  let ev : C →ₗ[ℤ] D :=
    { toFun := eval
      map_add' := eval.map_add
      map_smul' := fun a x => by
        rw [RingHom.id_apply]
        exact (congrArg eval (int_smul_eq_zsmul C.isModule a x)).trans
          ((eval.map_zsmul a x).trans (int_smul_eq_zsmul D.isModule a (eval x)).symm) }
  let f := ((tateFunctor G 2).map (integerTensorLeftUnitIso A).hom).hom.comp ev
  have hf : f (tateCupUnit G) = y := tateCup_left_unit A 2 y
  exact tateTrivialZero_map_bijective f (by rw [hf]; exact hgen) hcard

end IntegralGroupCohomology.Universe
