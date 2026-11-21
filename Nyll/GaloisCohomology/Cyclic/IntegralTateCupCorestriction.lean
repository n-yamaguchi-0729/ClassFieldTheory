/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupConnecting
public import Nyll.GaloisCohomology.Cyclic.IntegralTateGroupTransferConnecting
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorShift
public import Nyll.GaloisCohomology.GroupTheory.TensorShiftExactness

/-!
# The integral Tate projection formula

The degree-zero formula is the original relative norm of fixed vectors.
Connecting maps first propagate it to all left degrees with a degree-zero
right factor, and then to all integer bidegrees.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped RepTensor

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] [Fintype (G ⧸ H)]

private theorem corestrictCup_zero_boundary {S : ShortComplex (Rep.{u} ℤ G)}
    (hS : S.ShortExact) (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    (B : Rep.{u} ℤ G) (n : ℤ) (x : tate S.X₃ n) (y : tate (Rep.res H.subtype B) 0) :
    let hT := Rep.tensorRight_shortExact_of_forget_splitting B s
    tateCorestrict H (S.X₁ ⊗ᵣ B) (n + 1)
        (tensorCupZeroRight (Rep.res H.subtype S.X₁) (Rep.res H.subtype B) (n + 1)
          (tateRestrict H S.X₁ (n + 1) (tateδ hS n x)) y) =
      tateδ hT n (tateCorestrict H (S.X₃ ⊗ᵣ B) n
        (tensorCupZeroRight (Rep.res H.subtype S.X₃) (Rep.res H.subtype B) n
          (tateRestrict H S.X₃ n x) y)) := by
  intro hT
  let B' := Rep.res H.subtype B
  let hS' := subgroupRestrict_shortExact H hS
  let hT' := subgroupRestrict_shortExact H hT
  let z := tateRestrict H S.X₃ n x
  let w := tensorCupZeroRight (Rep.res H.subtype S.X₃) B' n z y
  let tr := tateCorestrict H (S.X₁ ⊗ᵣ B) (n + 1)
  let cup (a : tate (Rep.res H.subtype S.X₁) (n + 1)) :=
    tensorCupZeroRight (Rep.res H.subtype S.X₁) B' (n + 1) a y
  have hr := tateRestrict_connecting H hS s n x
  have hc := tateCupZeroRight_connecting_left B' hS' hT' n z y
  have ht := tateCorestrict_connecting H hT (Rep.tensorRight_forget_splitting B s) n w
  exact (congrArg (fun a => tr (cup a)) hr).trans ((congrArg tr hc).trans ht)

private theorem corestrictCup_zero_step_up (A B : Rep.{u} ℤ G) (n : ℤ)
    (x : tate A (n + 1)) (y : tate (Rep.res H.subtype B) 0)
    (ih : ∀ z : tate (Rep.coindShiftUp A) n,
      tateCorestrict H (Rep.coindShiftUp A ⊗ᵣ B) n
          (tensorCupZeroRight (Rep.res H.subtype (Rep.coindShiftUp A)) (Rep.res H.subtype B) n
            (tateRestrict H (Rep.coindShiftUp A) n z) y) =
        tensorCupZeroRight (Rep.coindShiftUp A) B n z (tateCorestrict H B 0 y)) :
    tateCorestrict H (A ⊗ᵣ B) (n + 1)
        (tensorCupZeroRight (Rep.res H.subtype A) (Rep.res H.subtype B) (n + 1)
          (tateRestrict H A (n + 1) x) y) =
      tensorCupZeroRight A B (n + 1) x (tateCorestrict H B 0 y) := by
  obtain ⟨z, rfl⟩ := (coindShiftUpEquiv A n).surjective x
  let hS := Rep.coindShiftSequence_shortExact A
  let s := Rep.coindShiftSequence_forget_splitting A
  let hT := Rep.tensorRight_shortExact_of_forget_splitting B s
  have h₁ := corestrictCup_zero_boundary H hS s B n z y
  have h₂ := congrArg (tateδ hT n) (ih z)
  have h₃ := (tateCupZeroRight_connecting_left B hS hT n z (tateCorestrict H B 0 y)).symm
  exact h₁.trans (h₂.trans h₃)

private theorem corestrictCup_zero_step_down (A B : Rep.{u} ℤ G) (n : ℤ)
    (x : tate A n) (y : tate (Rep.res H.subtype B) 0)
    (ih : ∀ z : tate (Rep.indShiftDown A) (n + 1),
      tateCorestrict H (Rep.indShiftDown A ⊗ᵣ B) (n + 1)
          (tensorCupZeroRight (Rep.res H.subtype (Rep.indShiftDown A)) (Rep.res H.subtype B) (n + 1)
            (tateRestrict H (Rep.indShiftDown A) (n + 1) z) y) =
        tensorCupZeroRight (Rep.indShiftDown A) B (n + 1) z (tateCorestrict H B 0 y)) :
    tateCorestrict H (A ⊗ᵣ B) n
        (tensorCupZeroRight (Rep.res H.subtype A) (Rep.res H.subtype B) n
          (tateRestrict H A n x) y) =
      tensorCupZeroRight A B n x (tateCorestrict H B 0 y) := by
  let hS := Rep.indShiftSequence_shortExact A
  let s := Rep.indShiftSequence_forget_splitting A
  let hT := Rep.tensorRight_shortExact_of_forget_splitting B s
  let C := Rep.ind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A)
  have hz : IsZero (tate (C ⊗ᵣ B) n) :=
    (tate_tensorIndBot_isZero B (Rep.res (⊥ : Subgroup G).subtype A) n).of_iso
      ((tateFunctor G n).mapIso (Rep.diagonalTensorCommIso C B))
  have hδ := tateδ_injective_of_isZero_middle hT n hz
  have h₁ := (corestrictCup_zero_boundary H hS s B n x y).symm
  have h₂ := ih (tateδ hS n x)
  have h₃ := tateCupZeroRight_connecting_left B hS hT n x (tateCorestrict H B 0 y)
  exact hδ (h₁.trans (h₂.trans h₃))

/-- The projection formula with a degree-zero right class holds in every left degree. -/
theorem tateCorestrict_tensorCupZeroRight (B : Rep.{u} ℤ G) (n : ℤ)
    (y : tate (Rep.res H.subtype B) 0) : ∀ (A : Rep.{u} ℤ G) (x : tate A n),
    tateCorestrict H (A ⊗ᵣ B) n
        (tensorCupZeroRight (Rep.res H.subtype A) (Rep.res H.subtype B) n
          (tateRestrict H A n x) y) =
      tensorCupZeroRight A B n x (tateCorestrict H B 0 y) := by
  let P (n : ℤ) := ∀ (A : Rep.{u} ℤ G) (x : tate A n),
    tateCorestrict H (A ⊗ᵣ B) n
        (tensorCupZeroRight (Rep.res H.subtype A) (Rep.res H.subtype B) n
          (tateRestrict H A n x) y) =
      tensorCupZeroRight A B n x (tateCorestrict H B 0 y)
  change P n
  refine Int.inductionOn' (motive := P) n 0 (fun A x => tateZeroCorestrict_cup H A B x y) ?_ ?_
  · intro n _ ih A x
    exact corestrictCup_zero_step_up H A B n x y (ih (Rep.coindShiftUp A))
  · intro n _ ih
    have hn : (n - 1) + 1 = n := sub_add_cancel n 1
    have ih' : P ((n - 1) + 1) := hn.symm ▸ ih
    intro A x
    exact corestrictCup_zero_step_down H A B (n - 1) x y (ih' (Rep.indShiftDown A))

private theorem corestrictCup_sign (B : Rep.{u} ℤ G) (p n : ℤ)
    (x : tate (Rep.res H.subtype B) n) :
    tateCorestrict H B n (p.negOnePow • x) = p.negOnePow • tateCorestrict H B n x := by
  simp only [Units.smul_def]
  exact (tateCorestrict H B n).toAddMonoidHom.map_zsmul (p.negOnePow : ℤ) x

private theorem connectingRight_eq_signedCup
    {S : ShortComplex (Rep.{u} ℤ G)} (A : Rep.{u} ℤ G) (hS : S.ShortExact)
    (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    {p q r : ℤ} (h : p + q = r) (x : tate A p) (y : tate S.X₃ q) :
    tateδ (Rep.tensorLeft_shortExact_of_forget_splitting A s) r
        (tateCup A S.X₃ p q r h x y) =
      p.negOnePow • tateCup A S.X₁ p (q + 1) (r + 1) (by omega) x (tateδ hS q y) := by
  let X := tate (A ⊗ᵣ S.X₁) (r + 1)
  let z : X := tateδ (Rep.tensorLeft_shortExact_of_forget_splitting A s) r
    (tateCup A S.X₃ p q r h x y)
  have hz : p.negOnePow • (p.negOnePow • z) = z := by
    rw [← mul_smul, Int.units_mul_self, one_smul]
  exact hz.symm.trans
    (congrArg (fun w : X => p.negOnePow • w) (tateCup_connecting_right A hS s h x y).symm)

private theorem corestrictCup_step_up (A B : Rep.{u} ℤ G) {p q r : ℤ} (h : p + q = r)
    (x : tate A p) (y : tate (Rep.res H.subtype B) (q + 1))
    (ih : ∀ z : tate (Rep.res H.subtype (Rep.coindShiftUp B)) q,
      tateCorestrict H (A ⊗ᵣ Rep.coindShiftUp B) r
          (tateCup (Rep.res H.subtype A) (Rep.res H.subtype (Rep.coindShiftUp B)) p q r h
            (tateRestrict H A p x) z) =
        tateCup A (Rep.coindShiftUp B) p q r h x (tateCorestrict H (Rep.coindShiftUp B) q z)) :
    tateCorestrict H (A ⊗ᵣ B) (r + 1)
        (tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p (q + 1) (r + 1) (by omega)
          (tateRestrict H A p x) y) =
      tateCup A B p (q + 1) (r + 1) (by omega) x (tateCorestrict H B (q + 1) y) := by
  obtain ⟨z, rfl⟩ := (subgroupCoindShiftEquiv H B q).surjective y
  let A' := Rep.res H.subtype A
  let S := Rep.coindShiftSequence B
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let hS := Rep.coindShiftSequence_shortExact B
  let s := Rep.coindShiftSequence_forget_splitting B
  let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
  let sT := Rep.tensorLeft_forget_splitting A s
  let hS' := subgroupRestrict_shortExact H hS
  let s' : ((S.map F).map (forget₂ (Rep.{u} ℤ H) (ModuleCat.{u} ℤ))).Splitting := s
  have hC := tateCup_connecting_right A' hS' s' h (tateRestrict H A p x) z
  change tateCup A' (Rep.res H.subtype B) p (q + 1) (r + 1) (by omega)
    (tateRestrict H A p x) (subgroupCoindShiftEquiv H B q z) = _ at hC
  have hy := tateCorestrict_connecting H hS s q z
  change tateCorestrict H B (q + 1) (subgroupCoindShiftEquiv H B q z) =
    tateδ hS q (tateCorestrict H (Rep.coindShiftUp B) q z) at hy
  let B₁ := Rep.coindShiftUp B
  let xx := tateRestrict H A p x
  let w := tateCup A' (Rep.res H.subtype B₁) p q r h xx z
  let hT' := subgroupRestrict_shortExact H hT
  let X := tate (A ⊗ᵣ B) (r + 1)
  let sign (v : X) : X := p.negOnePow • v
  let tr := tateCorestrict H (A ⊗ᵣ B) (r + 1)
  let cup (v : tate B (q + 1)) : X := tateCup A B p (q + 1) (r + 1) (by omega) x v
  have h₁ := congrArg tr hC
  have h₂ := corestrictCup_sign H (A ⊗ᵣ B) p (r + 1) (tateδ hT' r w)
  have h₃ := congrArg sign (tateCorestrict_connecting H hT sT r w)
  have h₄ := congrArg (fun v => sign (tateδ hT r v)) (ih z)
  have h₅ := (tateCup_connecting_right A hS s h x (tateCorestrict H B₁ q z)).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (congrArg cup hy.symm)))))

private theorem corestrictCup_step_down (A B : Rep.{u} ℤ G) {p q r : ℤ} (h : p + q = r)
    (x : tate A p) (y : tate (Rep.res H.subtype B) q)
    (ih : ∀ z : tate (Rep.res H.subtype (Rep.indShiftDown B)) (q + 1),
      tateCorestrict H (A ⊗ᵣ Rep.indShiftDown B) (r + 1)
          (tateCup (Rep.res H.subtype A) (Rep.res H.subtype (Rep.indShiftDown B))
            p (q + 1) (r + 1) (by omega) (tateRestrict H A p x) z) =
        tateCup A (Rep.indShiftDown B) p (q + 1) (r + 1) (by omega) x
          (tateCorestrict H (Rep.indShiftDown B) (q + 1) z)) :
    tateCorestrict H (A ⊗ᵣ B) r
        (tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q r h (tateRestrict H A p x) y) =
      tateCup A B p q r h x (tateCorestrict H B q y) := by
  let A' := Rep.res H.subtype A
  let S := Rep.indShiftSequence B
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let hS := Rep.indShiftSequence_shortExact B
  let s := Rep.indShiftSequence_forget_splitting B
  let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
  let sT := Rep.tensorLeft_forget_splitting A s
  let hS' := subgroupRestrict_shortExact H hS
  let hT' := subgroupRestrict_shortExact H hT
  let s' : ((S.map F).map (forget₂ (Rep.{u} ℤ H) (ModuleCat.{u} ℤ))).Splitting := s
  apply tateδ_injective_of_isZero_middle hT r
    (tate_tensorIndBot_isZero A (Rep.res (⊥ : Subgroup G).subtype B) r)
  let B₁ := Rep.indShiftDown B
  let xx := tateRestrict H A p x
  let w := tateCup A' (Rep.res H.subtype B) p q r h xx y
  let z := tateδ hS' q y
  let w' := tateCup A' (Rep.res H.subtype B₁) p (q + 1) (r + 1) (by omega) xx z
  let X := tate (A ⊗ᵣ B₁) (r + 1)
  let sign (v : X) : X := p.negOnePow • v
  let tr := tateCorestrict H (A ⊗ᵣ B₁) (r + 1)
  let cup (v : tate B₁ (q + 1)) : X :=
    tateCup A B₁ p (q + 1) (r + 1) (by omega) x v
  have hL : tateδ hT' r w = p.negOnePow • w' :=
    connectingRight_eq_signedCup A' hS' s' h xx y
  have hR := connectingRight_eq_signedCup A hS s h x (tateCorestrict H B q y)
  have h₁ := (tateCorestrict_connecting H hT sT r w).symm
  have h₂ := congrArg tr hL
  have h₃ := corestrictCup_sign H (A ⊗ᵣ B₁) p (r + 1) w'
  have h₄ := congrArg sign (ih z)
  have h₅ := congrArg (fun v => sign (cup v)) (tateCorestrict_connecting H hS s q y)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans hR.symm))))

/-- Corestriction satisfies the projection formula in every integer bidegree. -/
theorem tateCorestrict_cup (A : Rep.{u} ℤ G) (p q : ℤ) (x : tate A p) :
    ∀ (B : Rep.{u} ℤ G) (r : ℤ) (h : p + q = r) (y : tate (Rep.res H.subtype B) q),
      tateCorestrict H (A ⊗ᵣ B) r
          (tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q r h (tateRestrict H A p x) y) =
        tateCup A B p q r h x (tateCorestrict H B q y) := by
  have hpos (i : ℕ) : ∀ (B : Rep.{u} ℤ G) (r : ℤ) (h : p + i = r)
      (y : tate (Rep.res H.subtype B) i),
      tateCorestrict H (A ⊗ᵣ B) r
          (tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p i r h (tateRestrict H A p x) y) =
        tateCup A B p i r h x (tateCorestrict H B i y) := by
    induction i with
    | zero =>
      intro B r h y
      have hr : r = p := h.symm.trans (add_zero p)
      revert h
      rw [hr]
      intro h
      let A' := Rep.res H.subtype A
      let B' := Rep.res H.subtype B
      let xx := tateRestrict H A p x
      let yy := tateCorestrict H B 0 y
      have hL := congrArg (fun f => tateCorestrict H (A ⊗ᵣ B) p (f xx y))
        (tateCup_zero_right A' B' p (add_zero p))
      have hR := congrArg (fun f => f x yy) (tateCup_zero_right A B p (add_zero p))
      exact hL.trans ((tateCorestrict_tensorCupZeroRight H B p y A x).trans hR.symm)
    | succ i ih =>
      intro B r h y
      obtain rfl : r = (p + i) + 1 := by omega
      exact corestrictCup_step_up H A B (p := p) (q := i) (r := p + i) rfl x y
        (ih (Rep.coindShiftUp B) (p + i) rfl)
  cases q with
  | ofNat i => exact hpos i
  | negSucc i =>
    induction i with
    | zero =>
      intro B r h y
      exact corestrictCup_step_down H A B h x y (hpos 0 (Rep.indShiftDown B) (r + 1) (by omega))
    | succ i ih =>
      intro B r h y
      exact corestrictCup_step_down H A B h x y (ih (Rep.indShiftDown B) (r + 1) (by omega))

private theorem corestrictCup_restrict_right_boundary (A : Rep.{u} ℤ G)
    {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (s : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting)
    {p q r : ℤ} (h : p + q = r) (x : tate (Rep.res H.subtype A) p) (y : tate S.X₃ q) :
    let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
    tateCorestrict H (A ⊗ᵣ S.X₁) (r + 1)
        (tateCup (Rep.res H.subtype A) (Rep.res H.subtype S.X₁) p (q + 1) (r + 1)
          (by omega) x (tateRestrict H S.X₁ (q + 1) (tateδ hS q y))) =
      p.negOnePow • tateδ hT r (tateCorestrict H (A ⊗ᵣ S.X₃) r
        (tateCup (Rep.res H.subtype A) (Rep.res H.subtype S.X₃) p q r h x
          (tateRestrict H S.X₃ q y))) := by
  intro hT
  let A' := Rep.res H.subtype A
  let F : Rep.{u} ℤ G ⥤ Rep.{u} ℤ H := Rep.resFunctor H.subtype
  let hS' := subgroupRestrict_shortExact H hS
  let hT' := subgroupRestrict_shortExact H hT
  let s' : ((S.map F).map (forget₂ (Rep.{u} ℤ H) (ModuleCat.{u} ℤ))).Splitting := s
  let z := tateRestrict H S.X₃ q y
  let w := tateCup A' (Rep.res H.subtype S.X₃) p q r h x z
  let tr := tateCorestrict H (A ⊗ᵣ S.X₁) (r + 1)
  let cup (a : tate (Rep.res H.subtype S.X₁) (q + 1)) :=
    tateCup A' (Rep.res H.subtype S.X₁) p (q + 1) (r + 1) (by omega) x a
  let sign (a : tate (A ⊗ᵣ S.X₁) (r + 1)) := p.negOnePow • a
  have hr := tateRestrict_connecting H hS s q y
  have hc := tateCup_connecting_right A' hS' s' h x z
  have hs := corestrictCup_sign H (A ⊗ᵣ S.X₁) p (r + 1) (tateδ hT' r w)
  have ht := tateCorestrict_connecting H hT (Rep.tensorLeft_forget_splitting A s) r w
  exact (congrArg (fun a => tr (cup a)) hr).trans
    ((congrArg tr hc).trans (hs.trans (congrArg sign ht)))

section CorestrictRight

variable (A : Rep.{u} ℤ G) (p : ℤ) (x : tate (Rep.res H.subtype A) p)

private def CorestrictCupRestrictRight (q : ℤ) : Prop :=
  ∀ (B : Rep.{u} ℤ G) (r : ℤ) (h : p + q = r) (y : tate B q),
    tateCorestrict H (A ⊗ᵣ B) r
        (tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q r h x (tateRestrict H B q y)) =
      tateCup A B p q r h (tateCorestrict H A p x) y

private theorem corestrictCup_restrict_right_zero : CorestrictCupRestrictRight H A p x 0 := by
  intro B r h y
  have hr : r = p := h.symm.trans (add_zero p)
  revert h
  rw [hr]
  intro h
  obtain ⟨b, rfl⟩ := fixedClass_surjective B y
  rw [tateCup_zero_right, tateCup_zero_right, tateRestrict_zero_fixedClass,
    tensorCupZeroRight_fixedClass, tensorCupZeroRight_fixedClass]
  exact (tateCorestrict_naturality H p (Rep.tensorInvariant A B b) x).symm

private theorem corestrictCup_restrict_right_up (q : ℤ)
    (ih : CorestrictCupRestrictRight H A p x q) : CorestrictCupRestrictRight H A p x (q + 1) := by
  intro B r h y
  obtain rfl : r = (p + q) + 1 := by omega
  obtain ⟨z, rfl⟩ := (coindShiftUpEquiv B q).surjective y
  let hS := Rep.coindShiftSequence_shortExact B
  let s := Rep.coindShiftSequence_forget_splitting B
  let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
  let sign (a : tate (A ⊗ᵣ B) (p + q + 1)) := p.negOnePow • a
  let d := tateδ hT (p + q)
  have hL := corestrictCup_restrict_right_boundary H A hS s rfl x z
  have hR := tateCup_connecting_right A hS s rfl (tateCorestrict H A p x) z
  have hz := congrArg (fun a => sign (d a)) (ih (Rep.coindShiftUp B) (p + q) rfl z)
  exact hL.trans (hz.trans hR.symm)

private theorem corestrictCup_restrict_right_down (q : ℤ)
    (ih : CorestrictCupRestrictRight H A p x (q + 1)) : CorestrictCupRestrictRight H A p x q := by
  intro B r h y
  let hS := Rep.indShiftSequence_shortExact B
  let s := Rep.indShiftSequence_forget_splitting B
  let hT := Rep.tensorLeft_shortExact_of_forget_splitting A s
  let sign : Equiv.Perm (tate (A ⊗ᵣ Rep.indShiftDown B) (r + 1)) := MulAction.toPerm p.negOnePow
  have hinj := tateδ_injective_of_isZero_middle hT r
    (tate_tensorIndBot_isZero A (Rep.res (⊥ : Subgroup G).subtype B) r)
  have hL := corestrictCup_restrict_right_boundary H A hS s h x y
  have hR := tateCup_connecting_right A hS s h (tateCorestrict H A p x) y
  have hz := ih (Rep.indShiftDown B) (r + 1) (by omega) (tateδ hS q y)
  exact hinj (sign.injective (hL.symm.trans (hz.trans hR)))

end CorestrictRight

/-- Corestriction also satisfies the projection formula when restriction is
on the right factor. The signs are those of the same right connecting rule. -/
theorem tateCorestrict_cup_restrict_right (A : Rep.{u} ℤ G) (p q : ℤ)
    (x : tate (Rep.res H.subtype A) p) :
    ∀ (B : Rep.{u} ℤ G) (r : ℤ) (h : p + q = r) (y : tate B q),
      tateCorestrict H (A ⊗ᵣ B) r
          (tateCup (Rep.res H.subtype A) (Rep.res H.subtype B) p q r h x (tateRestrict H B q y)) =
        tateCup A B p q r h (tateCorestrict H A p x) y := by
  change CorestrictCupRestrictRight H A p x q
  refine Int.inductionOn' (motive := CorestrictCupRestrictRight H A p x) q 0
    (corestrictCup_restrict_right_zero H A p x) ?_ ?_
  · intro q _ ih
    exact corestrictCup_restrict_right_up H A p x q ih
  · intro q _ ih
    have h : (q - 1) + 1 = q := sub_add_cancel q 1
    exact corestrictCup_restrict_right_down H A p x (q - 1) (h.symm ▸ ih)

end IntegralGroupCohomology.Universe
