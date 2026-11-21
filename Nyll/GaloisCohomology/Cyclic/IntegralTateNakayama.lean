/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupClass
public import Nyll.GaloisCohomology.Cyclic.IntegralTateIsoCriterion
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorUnit

/-!
# Tate's cup-product isomorphism criterion for finite groups

A degree-two class lifts from the twice shifted coefficients. If its
restriction generates the Tate degree-two group of order `|H|` on each
prime-power subgroup `H`, and Tate degree one vanishes there, the original
cup product with the class is an isomorphism in every integer degree.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped RepTensor TensorProduct

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance (H : Subgroup G) : Fintype H := Fintype.ofFinite H

private theorem doubleShift_fixedClass_restriction
    (H : Subgroup G) [Fintype (G ⧸ H)] (B : Rep.{u} ℤ G)
    (b : (Rep.coindShiftUp (Rep.coindShiftUp B)).ρ.invariants) :
    tateRestrict H B 2 (tateClassOfDoubleShift B b) =
      subgroupCoindShiftEquiv H B 1
        (subgroupCoindShiftEquiv H (Rep.coindShiftUp B) 0
          (fixedClass (Rep.res H.subtype (Rep.coindShiftUp (Rep.coindShiftUp B)))
            (restrictInvariants H (Rep.coindShiftUp (Rep.coindShiftUp B)) b))) := by
  let C := Rep.coindShiftUp B
  let D := Rep.coindShiftUp C
  let z := fixedClass D b
  have hZero := tateRestrict_zero_fixedClass H D b
  have h₀ := tateRestrict_coindShift H C 0 z
  have h₁ := tateRestrict_coindShift H B 1 (coindShiftUpEquiv C 0 z)
  exact h₁.trans (congrArg (subgroupCoindShiftEquiv H B 1)
    (h₀.trans (congrArg (subgroupCoindShiftEquiv H C 0) hZero)))

private theorem tateCup_fixedRight_bijective_of_leftIso
    {A A' B : Rep.{u} ℤ G} (e : A ≅ A') (n : ℤ) (y : tate B 2)
    (h : Function.Bijective (fun x : tate A' n => tateCup A' B n 2 (n + 2) rfl x y)) :
    Function.Bijective (fun x : tate A n => tateCup A B n 2 (n + 2) rfl x y) := by
  let f (x : tate A n) := tateCup A B n 2 (n + 2) rfl x y
  let g (x : tate A' n) := tateCup A' B n 2 (n + 2) rfl x y
  let a := (tateFunctor G n).mapIso e
  let b := (tateFunctor G (n + 2)).mapIso ((Rep.diagonalTensorRight B).mapIso e)
  have hid : (tateFunctor G 2).map (𝟙 B) y = y :=
    ConcreteCategory.congr_hom ((tateFunctor G 2).map_id B) y
  have hfun : b.hom ∘ f = g ∘ a.hom := by
    funext x
    let q (z : tate B 2) := tateCup A' B n 2 (n + 2) rfl (a.hom x) z
    exact (tateCup_naturality e.hom (𝟙 B) n 2 (n + 2) rfl x y).trans (congrArg q hid)
  have he : Function.Bijective (b.hom ∘ f) := hfun.symm ▸ h.comp a.toLinearEquiv.bijective
  exact ⟨he.injective.of_comp, fun z => by
    obtain ⟨x, hx⟩ := he.surjective (b.hom z)
    exact ⟨x, b.toLinearEquiv.injective hx⟩⟩

private theorem tate_fixed_tensor_unitor_restriction
    (H : Subgroup G) (C : Rep.{u} ℤ G) (b : C.ρ.invariants) :
    let I := integralTrivialInteger.{u, u} G
    let f := Rep.tensorInvariant I C b ≫ (integerTensorLeftUnitIso C).hom
    (tateFunctor H 0).map ((Rep.resFunctor H.subtype).map f) (tateCupUnit H) =
      fixedClass (Rep.res H.subtype C) (restrictInvariants H C b) := by
  let I := integralTrivialInteger.{u, u} G
  let f := Rep.tensorInvariant I C b ≫ (integerTensorLeftUnitIso C).hom
  change (tateFunctor H 0).map ((Rep.resFunctor H.subtype).map f)
    (fixedClass (Rep.res H.subtype I) ⟨integralTrivialIntegerOne G, fun _ => rfl⟩) = _
  rw [fixedClass_map]
  apply congrArg (fixedClass (Rep.res H.subtype C))
  apply Subtype.ext
  let a : I := integralTrivialIntegerOne G
  change (integerTensorLeftUnitIso C).hom (a ⊗ₜ[ℤ] b.val) = b.val
  exact (integerTensorLeftUnitIso_tmul C a b.val).trans (one_smul ℤ b.val)

private theorem tateMap_integer_fixed_bijective {C : Rep.{u} ℤ G}
    (f : integralTrivialInteger.{u, u} G ⟶ C)
    (hzero : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      IsZero (tate (Rep.res H.subtype C) (-1)))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      Nat.card (tate (Rep.res H.subtype C) 0) = Nat.card H)
    (hgen : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      ∀ z : tate (Rep.res H.subtype C) 0, ∃ m : ℤ,
        m • ((tateFunctor H 0).map ((Rep.resFunctor H.subtype).map f) (tateCupUnit H)) = z)
    (n : ℤ) : Function.Bijective ((tateFunctor G n).map f) := by
  let I := integralTrivialInteger.{u, u} G
  refine tateMap_bijective_of_pSubgroups f 0 ?_ ?_ ?_ n
  · intro p _ H hH
    have : Subsingleton (tate (Rep.res H.subtype C) (-1)) := ModuleCat.subsingleton_of_isZero
      (hzero p H hH)
    let fH := (tateFunctor H (-1)).map ((Rep.resFunctor H.subtype).map f)
    have hF : Function.Surjective fH := Function.surjective_to_subsingleton fH
    let P (m : ℤ) := Function.Surjective ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map f))
    have hm : (0 : ℤ) - 1 = -1 := by decide
    exact Eq.mp (congrArg P hm.symm) hF
  · intro p _ H hH
    let fH := (tateFunctor H 0).map ((Rep.resFunctor H.subtype).map f)
    exact tateTrivialZero_map_bijective fH.hom (hgen p H hH) (hcard p H hH)
  · intro p _ H hH
    have hz : IsZero (tate (Rep.res H.subtype I) 1) := tateTrivialInteger_one_isZero (G := H)
    have : Subsingleton (tate (Rep.res H.subtype I) 1) := ModuleCat.subsingleton_of_isZero hz
    let fH := (tateFunctor H 1).map ((Rep.resFunctor H.subtype).map f)
    have hF : Function.Injective fH := Function.injective_of_subsingleton fH
    let P (m : ℤ) := Function.Injective ((tateFunctor H m).map ((Rep.resFunctor H.subtype).map f))
    have hm : (0 : ℤ) + 1 = 1 := by decide
    exact Eq.mp (congrArg P hm.symm) hF

/-- The actual cup map with a degree-two class is bijective in all degrees
once the three Tate–Nakayama conditions hold on its original restrictions. -/
theorem tateCup_degreeTwo_bijective (B : Rep.{u} ℤ G) (y : tate B 2)
    (h₁ : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      IsZero (tate (Rep.res H.subtype B) 1))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      Nat.card (tate (Rep.res H.subtype B) 2) = Nat.card H)
    (hgen : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G) [Fintype (G ⧸ H)], IsPGroup p H →
      ∀ z : tate (Rep.res H.subtype B) 2, ∃ m : ℤ, m • tateRestrict H B 2 y = z)
    (n : ℤ) : Function.Bijective (fun x : tate (integralTrivialInteger.{u, u} G) n =>
      (tateFunctor G (n + 2)).map (integerTensorLeftUnitIso B).hom
        (tateCup (integralTrivialInteger.{u, u} G) B n 2 (n + 2) rfl x y)) := by
  obtain ⟨b, rfl⟩ := (tateClassOfDoubleShift_surjective B) y
  let I := integralTrivialInteger.{u, u} G
  let C := Rep.coindShiftUp (Rep.coindShiftUp B)
  let i := Rep.tensorInvariant I C b
  let f := i ≫ (integerTensorLeftUnitIso C).hom
  let e (H : Subgroup G) (m : ℤ) := (subgroupCoindShiftEquiv H (Rep.coindShiftUp B) m).trans
    (subgroupCoindShiftEquiv H B (m + 1))
  have hres (H : Subgroup G) [Fintype (G ⧸ H)] :
      e H 0 ((tateFunctor H 0).map ((Rep.resFunctor H.subtype).map f) (tateCupUnit H)) =
        tateRestrict H B 2 (tateClassOfDoubleShift B b) := by
    exact (congrArg (e H 0) (tate_fixed_tensor_unitor_restriction H C b)).trans
      (doubleShift_fixedClass_restriction H B b).symm
  have hf : Function.Bijective ((tateFunctor G n).map f) := by
    refine tateMap_integer_fixed_bijective f ?_ ?_ ?_ n
    · intro p _ H hH
      exact (h₁ p H hH).of_iso (e H (-1)).toModuleIso
    · intro p _ H hH
      exact (Nat.card_congr (e H 0).toEquiv).trans (hcard p H hH)
    · intro p _ H hH z
      let : Fintype (G ⧸ H) := Fintype.ofFinite _
      let fH := (tateFunctor H 0).map ((Rep.resFunctor H.subtype).map f)
      obtain ⟨m, hm⟩ := hgen p H hH (e H 0 z)
      have he := map_zsmul (e H 0) m (fH (tateCupUnit H))
      exact ⟨m, (e H 0).injective (he.trans ((congrArg (m • ·) (hres H)).trans hm))⟩
  let g := (tateFunctor G n).map i
  let k := (tateFunctor G n).map (integerTensorLeftUnitIso C).hom
  have hmap := (tateFunctor G n).map_comp i (integerTensorLeftUnitIso C).hom
  have heq : (fun x : tate I n => (tateFunctor G n).map f x) = k ∘ g :=
    funext fun x => ConcreteCategory.congr_hom hmap x
  have hk : Function.Bijective k := ConcreteCategory.bijective_of_isIso k
  have hf' : Function.Bijective (k ∘ g) := by
    rw [← heq]
    exact hf
  have hi : Function.Bijective g := hf'.of_comp_left hk.injective
  let d : n + 1 + 1 = n + 2 := by omega
  let E := ((tensorCoindShiftEquiv I (Rep.coindShiftUp B) n).trans
      (tensorCoindShiftEquiv I B (n + 1))).trans (tateDegreeEquiv (I ⊗ᵣ B) d)
  have hcup (x : tate I n) : tateCup I B n 2 (n + 2) rfl x (tateClassOfDoubleShift B b) =
      E ((tateFunctor G n).map i x) := by
    have h := tateCup_classOfDoubleShift I B n x b
    have he (r : ℤ) (hr : n + 2 = r) :
        tateDegreeEquiv (I ⊗ᵣ B) hr
          (tateCup I B n 2 (n + 2) rfl x (tateClassOfDoubleShift B b)) =
        tateCup I B n 2 r hr x (tateClassOfDoubleShift B b) := by subst r; rfl
    have h' := congrArg (tateDegreeEquiv (I ⊗ᵣ B) d) h
    rw [← he (n + 1 + 1) d.symm] at h'
    change tateDegreeEquiv (I ⊗ᵣ B) d (tateDegreeEquiv (I ⊗ᵣ B) d.symm _) = _ at h'
    have hcancel {r s : ℤ} (h : r = s) (z : tate (I ⊗ᵣ B) r) :
        tateDegreeEquiv (I ⊗ᵣ B) h.symm (tateDegreeEquiv (I ⊗ᵣ B) h z) = z := by subst s; rfl
    rw [hcancel] at h'
    exact h'
  have hl : Function.Bijective ((tateFunctor G (n + 2)).map (integerTensorLeftUnitIso B).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have hfun :
      (fun x : tate I n => (tateFunctor G (n + 2)).map (integerTensorLeftUnitIso B).hom
        (tateCup I B n 2 (n + 2) rfl x (tateClassOfDoubleShift B b))) =
      ((tateFunctor G (n + 2)).map (integerTensorLeftUnitIso B).hom) ∘ E ∘
        ((tateFunctor G n).map i) :=
    funext fun x =>
      congrArg ((tateFunctor G (n + 2)).map (integerTensorLeftUnitIso B).hom) (hcup x)
  rw [hfun]
  exact hl.comp (E.bijective.comp hi)

/-- The all-degree isomorphism whose underlying map is the original cup
product with the supplied degree-two class, followed by the tensor unitor. -/
def tateNakayamaIso (B : Rep.{u} ℤ G) (y : tate B 2)
    (h₁ : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      IsZero (tate (Rep.res H.subtype B) 1))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G), IsPGroup p H →
      Nat.card (tate (Rep.res H.subtype B) 2) = Nat.card H)
    (hgen : ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup G) [Fintype (G ⧸ H)], IsPGroup p H →
      ∀ z : tate (Rep.res H.subtype B) 2, ∃ m : ℤ, m • tateRestrict H B 2 y = z)
    (n : ℤ) : tate (integralTrivialInteger.{u, u} G) n ≃ₗ[ℤ] tate B (n + 2) :=
  let I := integralTrivialInteger.{u, u} G
  let cup := tateCup I B n 2 (n + 2) rfl
  let unit := (tateFunctor G (n + 2)).map (integerTensorLeftUnitIso B).hom
  let eval : (tate B 2 →ₗ[ℤ] tate (I ⊗ᵣ B) (n + 2)) →+ tate (I ⊗ᵣ B) (n + 2) :=
    { toFun := fun f => f y, map_zero' := rfl, map_add' := fun _ _ => rfl }
  LinearEquiv.ofBijective (unit.hom.comp (integerModuleLinearMap (eval.comp cup.toAddMonoidHom)))
    (tateCup_degreeTwo_bijective B y h₁ hcard hgen n)

private theorem tateCupTrivialInteger_lift_evaluation
    (B : Rep.{v} ℤ G) (p q r : ℤ) (h : p + q = r)
    (x : tate (integralTrivialInteger.{u, v} G) p) (y : tate B q) :
    let F := Rep.universeLiftFunctor ℤ G
    let I := integralTrivialInteger.{u, v} G
    let U := F.obj I
    let V := F.obj B
    let eT := Rep.universeLiftIntegerTensorIso I B
    let e := tateIsoCommon (F.obj (I ⊗ᵣ B)) r
    tateCupTrivialInteger B p q r h y x =
      (tateFunctor G r).map (integerTensorLeftUnitIso B).hom
        (e.hom ((tateFunctor (ULift.{v} G) r).map eT.hom
          (tateCup U V p q r h ((tateIsoCommon U p).inv x) ((tateIsoCommon V q).inv y)))) := by
  rfl

private def liftedIntegerCupRight (B : Rep.{v} ℤ G) (y : tate B 2) (n : ℤ) :
    let F := Rep.universeLiftFunctor ℤ G
    let I := integralTrivialInteger.{u, v} G
    tate (F.obj I) n → tate (F.obj I ⊗ᵣ F.obj B) (n + 2) := by
  intro F I x
  let U := F.obj I
  let A := F.obj B
  let z : tate A 2 := (tateIsoCommon A 2).inv y
  let c := tateCup U A n 2 (n + 2) rfl
  exact c x z

private def liftedIntegerCup (B : Rep.{v} ℤ G) (y : tate B 2) (n : ℤ) :
    tate (integralTrivialInteger.{u, v} G) n → tate B (n + 2) :=
  let F := Rep.universeLiftFunctor ℤ G
  let I := integralTrivialInteger.{u, v} G
  let U := F.obj I
  let d := (tateIsoCommon U n).inv
  let t := (tateFunctor (ULift.{v} G) (n + 2)).map (Rep.universeLiftIntegerTensorIso I B).hom
  let a := (tateIsoCommon (F.obj (I ⊗ᵣ B)) (n + 2)).hom
  let l := (tateFunctor G (n + 2)).map (integerTensorLeftUnitIso B).hom
  fun x => l (a (t (liftedIntegerCupRight B y n (d x))))

private theorem tateCupTrivialInteger_eq_liftedIntegerCup (B : Rep.{v} ℤ G) (y : tate B 2) (n : ℤ) :
    (fun x : tate (integralTrivialInteger.{u, v} G) n =>
      tateCupTrivialInteger B n 2 (n + 2) rfl y x) =
      liftedIntegerCup B y n := by
  funext x
  unfold liftedIntegerCup liftedIntegerCupRight
  exact tateCupTrivialInteger_lift_evaluation B n 2 (n + 2) rfl x y

private theorem tateCupTrivialInteger_bijective_of_liftedCup
    (B : Rep.{v} ℤ G) (y : tate B 2) (n : ℤ)
    (h : Function.Bijective (liftedIntegerCupRight B y n)) :
    Function.Bijective (tateCupTrivialInteger B n 2 (n + 2) rfl y) := by
  let F := Rep.universeLiftFunctor ℤ G
  let I := integralTrivialInteger.{u, v} G
  let U := F.obj I
  let B' := F.obj B
  let J := ULift.{v} G
  let d := (tateIsoCommon U n).inv
  let t := (tateFunctor J (n + 2)).map (Rep.universeLiftIntegerTensorIso I B).hom
  let a := (tateIsoCommon (F.obj (I ⊗ᵣ B)) (n + 2)).hom
  let lB := (tateFunctor G (n + 2)).map (integerTensorLeftUnitIso B).hom
  let d' : tate I n → tate U n := d
  let t' : tate (U ⊗ᵣ B') (n + 2) → tate (F.obj (I ⊗ᵣ B)) (n + 2) := t
  let a' : tate (F.obj (I ⊗ᵣ B)) (n + 2) → tate (I ⊗ᵣ B) (n + 2) := a
  let l' : tate (I ⊗ᵣ B) (n + 2) → tate B (n + 2) := lB
  have hd : Function.Bijective d' := ConcreteCategory.bijective_of_isIso d
  have ht : Function.Bijective t' := ConcreteCategory.bijective_of_isIso t
  have ha : Function.Bijective a' := ConcreteCategory.bijective_of_isIso a
  have hl : Function.Bijective l' := ConcreteCategory.bijective_of_isIso lB
  have hMaps : Function.Bijective (l' ∘ a' ∘ t' ∘ liftedIntegerCupRight B y n ∘ d') :=
    hl.comp (ha.comp (ht.comp (h.comp hd)))
  have hLift : Function.Bijective (liftedIntegerCup B y n) := hMaps
  let f : tate I n → tate B (n + 2) := tateCupTrivialInteger B n 2 (n + 2) rfl y
  have hEq : f = liftedIntegerCup B y n := tateCupTrivialInteger_eq_liftedIntegerCup B y n
  exact Eq.mpr (congrArg Function.Bijective hEq) hLift

/-- The actual cup on independently sized coefficients is bijective under
the Tate–Nakayama conditions on the single lift used by its definition. -/
theorem tateCupTrivialInteger_bijective_of_lifted (B : Rep.{v} ℤ G) (y : tate B 2)
    (h₁ : let B' := (Rep.universeLiftFunctor ℤ G).obj B
      ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup (ULift.{v} G)), IsPGroup p H →
        IsZero (tate (Rep.res H.subtype B') 1))
    (hcard : let B' := (Rep.universeLiftFunctor ℤ G).obj B
      ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup (ULift.{v} G)), IsPGroup p H →
        Nat.card (tate (Rep.res H.subtype B') 2) = Nat.card H)
    (hgen : let B' := (Rep.universeLiftFunctor ℤ G).obj B
      ∀ (p : ℕ) [Fact p.Prime] (H : Subgroup (ULift.{v} G)) [Fintype (ULift.{v} G ⧸ H)],
        IsPGroup p H →
        ∀ z : tate (Rep.res H.subtype B') 2,
          ∃ m : ℤ, m • tateRestrict H B' 2 ((tateIsoCommon B' 2).inv y) = z)
    (n : ℤ) : Function.Bijective (tateCupTrivialInteger B n 2 (n + 2) rfl y) := by
  let F := Rep.universeLiftFunctor ℤ G
  let B' := F.obj B
  let I := integralTrivialInteger.{u, v} G
  let I' := integralTrivialInteger.{max u v, max u v} (ULift.{v} G)
  let U := F.obj I
  let v := (tateIsoCommon B' 2).inv y
  let J := ULift.{v} G
  let c : U ≃ₗ[ℤ] I' :=
    ((ULift.moduleEquiv : ULift.{u} (ULift.{v} ℤ) ≃ₗ[ℤ] ULift.{v} ℤ).trans
      (ULift.moduleEquiv : ULift.{v} ℤ ≃ₗ[ℤ] ℤ)).trans
      (ULift.moduleEquiv : ULift.{max u v} ℤ ≃ₗ[ℤ] ℤ).symm
  let e : U ≅ I' := Rep.mkIso (Representation.Equiv.mk c (fun _ => rfl))
  let f₁ := fun x : tate I' n => tateCup I' B' n 2 (n + 2) rfl x v
  let l := (tateFunctor J (n + 2)).map (integerTensorLeftUnitIso B').hom
  have hl : Function.Bijective l := ConcreteCategory.bijective_of_isIso l
  have h₁' : Function.Bijective f₁ := by
    have h : Function.Bijective (l ∘ f₁) := tateCup_degreeTwo_bijective B' v h₁ hcard hgen n
    exact h.of_comp_left hl.injective
  have h₂ := tateCup_fixedRight_bijective_of_leftIso e n v h₁'
  have hLift : Function.Bijective (liftedIntegerCupRight B y n) := by
    dsimp only [liftedIntegerCupRight]
    dsimp only [U, F, I, B', v] at h₂
    exact h₂
  exact tateCupTrivialInteger_bijective_of_liftedCup B y n hLift

end IntegralGroupCohomology.Universe
