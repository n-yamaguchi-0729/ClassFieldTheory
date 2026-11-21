/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupClass
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorUnit
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInflation
public import Nyll.GaloisCohomology.Cyclic.IntegralTateNegativeBoundaries
public import Nyll.GaloisCohomology.Cyclic.IntegralNormKernelVanishing
public import Nyll.GaloisCohomology.Cyclic.IntegralTateRestrictionComparison
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryInflation

/-!
# Evaluating a cyclic carry against the negative bar class

The two coinduced lifts are the original functions obtained from the
carry. The inverse action in the boundary of a bar chain is responsible
for the negative sign in its degree-zero pairing.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped RepTensor BigOperators TensorProduct
open ClassFieldTower.Cohomology

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- Summing the cyclic carry in its first argument gives the standard
representative of its second argument. -/
theorem sum_finiteCyclicCarry (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (y : G) :
    (∑ x : G, finiteCyclicCarry g hg x y) = (finiteCyclicGeneratorCoordinate g hg y).val := by
  have h := Finset.sum_congr (rfl : (Finset.univ : Finset G) = Finset.univ)
    (fun x _ => finiteCyclicCarry_balance g hg x y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at h
  have hsum : (∑ x : G, (finiteCyclicGeneratorCoordinate g hg (x * y)).val) =
      ∑ x : G, (finiteCyclicGeneratorCoordinate g hg x).val :=
    Fintype.sum_bijective (· * y) (Group.mulRight_bijective y) _ _ (fun _ => rfl)
  have hn : Nat.card G * (∑ x : G, finiteCyclicCarry g hg x y) =
      Nat.card G * (finiteCyclicGeneratorCoordinate g hg y).val := by
    rw [hsum, ← Nat.card_eq_fintype_card] at h
    exact Nat.add_right_cancel (h.trans (Nat.add_comm _ _))
  exact Nat.mul_left_cancel Nat.card_pos hn

/-- For the inverse generator, the sum is the order of the group minus one. -/
theorem sum_finiteCyclicCarry_generator_inv (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (∑ x : G, finiteCyclicCarry g hg x g⁻¹) = Nat.card G - 1 := by
  rw [sum_finiteCyclicCarry]
  have hcoord : finiteCyclicGeneratorCoordinate g hg g⁻¹ = -(1 : ZMod (Nat.card G)) := by
    change Multiplicative.toAdd (((zmodMulEquivOfGenerator hg rfl).symm) g⁻¹) = _
    rw [map_inv]
    change -finiteCyclicGeneratorCoordinate g hg g = _
    exact congrArg Neg.neg (finiteCyclicGeneratorCoordinate_generator g hg)
  rw [hcoord]
  have hp : 0 < Nat.card G := Nat.card_pos
  generalize Nat.card G = n at hp ⊢
  cases n with
  | zero => omega
  | succ n => exact ZMod.val_neg_one n

/-- An actual group equivalence preserves the finite cyclic coordinates, even
when the group carriers lie in independent universes. -/
theorem finiteCyclicCoordinate_val_equiv {H : Type v} [Group H] [Fintype H]
    (e : G ≃* H) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (he : ∀ x : H, x ∈ Subgroup.zpowers (e g)) (x : G) :
    (finiteCyclicGeneratorCoordinate g hg x).val =
      (finiteCyclicGeneratorCoordinate (e g) he (e x)).val := by
  let m := (finiteCyclicGeneratorCoordinate g hg x).val
  have hx : x = g ^ m := (finiteCyclicGenerator_zpow_coordinate g hg x).symm
  have h₁ := congrArg (fun z : G => (finiteCyclicGeneratorCoordinate g hg z).val) hx
  have h₂ := congrArg (fun z : G => (finiteCyclicGeneratorCoordinate (e g) he (e z)).val) hx
  rw [finiteCyclicGeneratorCoordinate_pow, ZMod.val_natCast] at h₁
  rw [map_pow, finiteCyclicGeneratorCoordinate_pow, ZMod.val_natCast] at h₂
  have hc := congrArg (fun n : ℕ => m % n) (Nat.card_congr e.toEquiv)
  exact h₁.trans (hc.trans h₂.symm)

/-- The original carry is unchanged by reindexing the same generator and group. -/
theorem finiteCyclicCarry_equiv {H : Type v} [Group H] [Fintype H]
    (e : G ≃* H) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (he : ∀ x : H, x ∈ Subgroup.zpowers (e g)) (x y : G) :
    finiteCyclicCarry g hg x y = finiteCyclicCarry (e g) he (e x) (e y) := by
  have h₁ := finiteCyclicCarry_balance g hg x y
  have h₂ := finiteCyclicCarry_balance (e g) he (e x) (e y)
  rw [← map_mul, ← finiteCyclicCoordinate_val_equiv e g hg he x,
    ← finiteCyclicCoordinate_val_equiv e g hg he y,
    ← finiteCyclicCoordinate_val_equiv e g hg he (x * y)] at h₂
  have hc := congrArg (fun n : ℕ => n * finiteCyclicCarry (e g) he (e x) (e y) +
    (finiteCyclicGeneratorCoordinate g hg (x * y)).val) (Nat.card_congr e.toEquiv)
  exact Nat.mul_left_cancel Nat.card_pos (Nat.add_right_cancel (h₁.trans (hc.trans h₂).symm))

/-- An arbitrary function is an element of the original coinduction from
the trivial subgroup. -/
def coindShiftFunction (A : Rep.{u} ℤ G) (f : G → A) : (Rep.coindShiftSequence A).X₂ :=
  ⟨f, fun h x => by
    have hh : h = 1 := Subsingleton.elim _ _
    subst h
    change f ((1 : G) * x) = A.ρ 1 (f x)
    rw [one_mul, map_one, one_apply_eq_self]⟩

/-- The original coinduced carry function with second argument fixed. -/
def carryCoindLift (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) (y : G) : (Rep.coindShiftSequence A).X₂ :=
  coindShiftFunction A (fun x => finiteCyclicCarry g hg x y • a.val)

/-- The coinduced functions lift the carry, with the original action embedding. -/
theorem carryCoindLift_d (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) (x y : G) :
    (Rep.coindShiftSequence A).X₂.ρ x (carryCoindLift A g hg a y) + carryCoindLift A g hg a x =
      carryCoindLift A g hg a (x * y) +
        (Rep.coindShiftSequence A).f (finiteCyclicCarry g hg x y • a.val) := by
  apply Subtype.ext
  funext w
  change (finiteCyclicCarry g hg (w * x) y • a.val + finiteCyclicCarry g hg w x • a.val) =
    finiteCyclicCarry g hg w (x * y) • a.val + A.ρ w (finiteCyclicCarry g hg x y • a.val)
  rw [map_nsmul, a.property, ← add_nsmul, ← add_nsmul, finiteCyclicCarry_cocycle, add_comm]

/-- Projecting the coinduced carry functions gives the first shifted one-cocycle. -/
def carryShiftCocycle (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) : G → Rep.coindShiftUp A :=
  fun y => (Rep.coindShiftSequence A).g (carryCoindLift A g hg a y)

theorem carryShiftCocycle_mul (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) (x y : G) :
    carryShiftCocycle A g hg a (x * y) =
      (Rep.coindShiftUp A).ρ x (carryShiftCocycle A g hg a y) + carryShiftCocycle A g hg a x := by
  let S := Rep.coindShiftSequence A
  have h := congrArg (fun v : S.X₂ => S.g v) (carryCoindLift_d A g hg a x y)
  have hz : S.g ((Rep.coindShiftSequence A).f (finiteCyclicCarry g hg x y • a.val)) = 0 :=
    congrArg (fun m : A ⟶ S.X₃ => m (finiteCyclicCarry g hg x y • a.val)) S.zero
  rw [map_add, map_add, hz, add_zero, Rep.hom_comm_apply] at h
  exact h.symm

omit [Fintype G] in
/-- The differential of the original coinduced one-cocycle function is its
value included by the original coefficient embedding. -/
theorem coindShiftFunction_cocycle_d (A : Rep.{u} ℤ G) (z : G → A)
    (hz : ∀ x y, z (x * y) = A.ρ x (z y) + z x) (g : G) :
    (Rep.coindShiftSequence A).X₂.ρ g (coindShiftFunction A z) - coindShiftFunction A z =
      Rep.coindShiftUnit A (z g) := by
  apply Subtype.ext
  funext x
  change z (x * g) - z x = A.ρ x (z g)
  rw [hz, add_sub_cancel_right]

/-- The original fixed vector in the twice shifted module coming from the carry. -/
def carryDoubleShiftFixed (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) : (Rep.coindShiftUp (Rep.coindShiftUp A)).ρ.invariants := by
  let B := Rep.coindShiftUp A
  let S := Rep.coindShiftSequence B
  let z := carryShiftCocycle A g hg a
  let w := coindShiftFunction B z
  refine ⟨S.g w, fun h => ?_⟩
  have he := congrArg S.g (coindShiftFunction_cocycle_d B z (carryShiftCocycle_mul A g hg a) h)
  have hzero : S.g (Rep.coindShiftUnit B (z h)) = 0 :=
    congrArg (fun φ : B ⟶ S.X₃ => φ (z h)) S.zero
  rw [map_sub, Rep.hom_comm_apply, hzero] at he
  exact sub_eq_zero.mp he

/-- The original norm of the coinduced carry is the constant action image of
the second argument's standard representative times the given invariant. -/
theorem carryCoindLift_norm (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) (y : G) :
    (Rep.coindShiftSequence A).X₂.ρ.norm (carryCoindLift A g hg a y) =
      Rep.coindShiftUnit A ((finiteCyclicGeneratorCoordinate g hg y).val • a.val) := by
  apply Subtype.ext
  funext w
  let ev : (Rep.coindShiftSequence A).X₂ →+ A :=
    { toFun := fun f => f.val w
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev ((Rep.coindShiftSequence A).X₂.ρ.norm (carryCoindLift A g hg a y)) =
    A.ρ w ((finiteCyclicGeneratorCoordinate g hg y).val • a.val)
  rw [Representation.norm, LinearMap.sum_apply, map_sum ev, map_nsmul]
  have ha : A.ρ w a.val = a.val := a.property w
  rw [ha]
  change (∑ x : G, finiteCyclicCarry g hg (w * x) y • a.val) = _
  calc
    _ = ∑ x : G, finiteCyclicCarry g hg x y • a.val :=
      Fintype.sum_bijective (w * ·) (Group.mulLeft_bijective w) _ _ (fun _ => rfl)
    _ = (∑ x : G, finiteCyclicCarry g hg x y) • a.val := Finset.sum_smul.symm
    _ = _ := by rw [sum_finiteCyclicCarry]

private theorem carryShiftCocycle_norm_zero (A : Rep.{u} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a : A.ρ.invariants) (y : G) :
    (Rep.coindShiftUp A).ρ.norm (carryShiftCocycle A g hg a y) = 0 := by
  let S := Rep.coindShiftSequence A
  have h := congrArg (fun φ : S.X₂ ⟶ S.X₃ => φ (carryCoindLift A g hg a y)) (Rep.norm_comm S.g)
  change S.X₃.ρ.norm (carryShiftCocycle A g hg a y) =
    S.g (S.X₂.ρ.norm (carryCoindLift A g hg a y)) at h
  rw [carryCoindLift_norm] at h
  exact h.trans (congrArg
    (fun φ : A ⟶ S.X₃ => φ ((finiteCyclicGeneratorCoordinate g hg y).val • a.val)) S.zero)

/-- The actual native two-cocycle whose coefficient is the original cyclic carry. -/
def nativeCarryCocycle (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) : groupCohomology.cocycles₂ ((nativeFunctor G).obj A) := by
  let M := (nativeFunctor G).obj A
  let z : ULift.{u} G × ULift.{u} G → M := fun x =>
    ULift.up (finiteCyclicCarry g hg x.1.down x.2.down • a.val)
  refine ⟨z, (groupCohomology.mem_cocycles₂_iff z).mpr (fun x y w => ?_)⟩
  apply ULift.down_injective
  change finiteCyclicCarry g hg (x.down * y.down) w.down • a.val +
      finiteCyclicCarry g hg x.down y.down • a.val =
    A.ρ x.down (finiteCyclicCarry g hg y.down w.down • a.val) +
      finiteCyclicCarry g hg x.down (y.down * w.down) • a.val
  rw [map_nsmul, a.property, ← add_nsmul, ← add_nsmul, finiteCyclicCarry_cocycle]

/-- The original cyclic carry regarded as a positive Tate class. -/
def tateCyclicCarryClass (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) : tate A 2 :=
  (tatePositiveIsoCohomology A 2).inv (groupCohomology.H2π _ (nativeCarryCocycle A g hg a))

/-- The carry cocycle on the original group and coefficient carrier over the
lifted integer scalar ring. -/
def commonCarryCocycle (A : Rep.{u} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : A.ρ.invariants) :
    groupCohomology.cocycles₂ ((IntegralGroupCohomology.coefficientFunctor G).obj A) := by
  let M := (IntegralGroupCohomology.coefficientFunctor G).obj A
  let z : G × G → M := fun x => finiteCyclicCarry g hg x.1 x.2 • a.val
  refine ⟨z, (groupCohomology.mem_cocycles₂_iff z).mpr (fun x y w => ?_)⟩
  change finiteCyclicCarry g hg (x * y) w • a.val + finiteCyclicCarry g hg x y • a.val =
    A.ρ x (finiteCyclicCarry g hg y w • a.val) + finiteCyclicCarry g hg x (y * w) • a.val
  rw [map_nsmul, a.property, ← add_nsmul, ← add_nsmul, finiteCyclicCarry_cocycle]

/-- The positive comparison removes the auxiliary lifts on the same carry representative. -/
theorem tatePositiveIsoCommonCohomology_hom_cyclicCarry (A : Rep.{u} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a : A.ρ.invariants) :
    (tatePositiveIsoCommonCohomology A 2).hom (tateCyclicCarryClass A g hg a) =
      groupCohomology.H2π _ (commonCarryCocycle A g hg a) := by
  let e := tatePositiveIsoCohomology A 2
  let z : cohomology A 2 := groupCohomology.H2π _ (nativeCarryCocycle A g hg a)
  change (cohomologyIsoCommon A 2).hom (e.hom (e.inv z)) = _
  refine (congrArg (cohomologyIsoCommon A 2).hom (e.inv_hom_id_apply z)).trans ?_
  change (groupCohomology.mapIso (MulEquiv.ulift : ULift.{u} G ≃* G)
    (nativeCarrierEquiv A) (nativeCarrierEquiv_comm A) 2).hom
      (groupCohomology.H2π _ (nativeCarryCocycle A g hg a)) = _
  unfold groupCohomology.mapIso
  dsimp only
  refine (groupCohomology.H2π_comp_map_apply _ _ _).trans ?_
  apply congrArg (groupCohomology.H2π _)
  apply groupCohomology.cocycles₂_ext
  intro x y
  rfl

/-- The twice shifted fixed vector represents exactly the original cyclic carry. -/
theorem tateClassOfDoubleShift_carryDoubleShiftFixed (A : Rep.{u} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a : A.ρ.invariants) :
    tateClassOfDoubleShift A (carryDoubleShiftFixed A g hg a) = tateCyclicCarryClass A g hg a := by
  let B := Rep.coindShiftUp A
  let S := Rep.coindShiftSequence A
  let T := Rep.coindShiftSequence B
  let hS := Rep.coindShiftSequence_shortExact A
  let hT := Rep.coindShiftSequence_shortExact B
  let b := carryDoubleShiftFixed A g hg a
  let w := coindShiftFunction B (carryShiftCocycle A g hg a)
  let z : groupCohomology.cocycles₁ ((nativeFunctor G).obj B) :=
    ⟨fun x => ULift.up (carryShiftCocycle A g hg a x.down),
      (groupCohomology.mem_cocycles₁_iff _).mpr (fun x y =>
        ULift.ext (carryShiftCocycle_mul A g hg a x.down y.down))⟩
  let t := tateδ hT 0 (fixedClass T.X₃ b)
  have h₁ : (tatePositiveIsoCohomology B 1).hom t = groupCohomology.H1π _ z := by
    change (tatePositiveIsoCohomology B 1).hom (tateδ hT 0 (fixedClass T.X₃ b)) = _
    refine (tateδ_zero_fixedClass_comparison hT b).trans ?_
    have h := groupCohomology.δ₀_apply (native_shortExact hT) (nativeFixedEquiv T.X₃ b)
      (ULift.up w) rfl (fun x => ULift.up (carryShiftCocycle A g hg a x.down)) (by
        funext x
        exact ULift.ext ((coindShiftFunction_cocycle_d B (carryShiftCocycle A g hg a)
          (carryShiftCocycle_mul A g hg a) x.down).symm))
    exact h
  have h₂ : δ hS 1 2 rfl (groupCohomology.H1π _ z) =
      groupCohomology.H2π _ (nativeCarryCocycle A g hg a) := by
    have h := groupCohomology.δ₁_apply (native_shortExact hS) z
      (fun x => ULift.up (carryCoindLift A g hg a x.down)) rfl
      (fun x : ULift.{u} G × ULift.{u} G =>
        ULift.up (finiteCyclicCarry g hg x.1.down x.2.down • a.val)) (by
        funext x
        obtain ⟨p, q⟩ := x
        apply ULift.down_injective
        change Rep.coindShiftUnit A (finiteCyclicCarry g hg p.down q.down • a.val) =
          S.X₂.ρ p.down (carryCoindLift A g hg a q.down) -
            carryCoindLift A g hg a (p.down * q.down) +
            carryCoindLift A g hg a p.down
        have hp := carryCoindLift_d A g hg a p.down q.down
        calc
          _ = (carryCoindLift A g hg a (p.down * q.down) +
              S.f (finiteCyclicCarry g hg p.down q.down • a.val)) -
                carryCoindLift A g hg a (p.down * q.down) := by abel
          _ = _ := by rw [← hp]; abel)
    exact h
  let e := tatePositiveIsoCohomology A 2
  apply e.toLinearEquiv.injective
  change (tateδ hS 1 ≫ e.hom) t =
    e.hom (e.inv (groupCohomology.H2π _ (nativeCarryCocycle A g hg a)))
  have hd := ConcreteCategory.congr_hom (tateδ_positive_comparison hS 1) t
  exact hd.trans ((congrArg (δ hS 1 2 rfl) h₁).trans
    (h₂.trans (e.inv_hom_id_apply _).symm))

/-- The original invariant tensor of two original fixed vectors. -/
def tensorFixedVector (A B : Rep.{v} ℤ G) (x : A.ρ.invariants) (y : B.ρ.invariants) :
    (A ⊗ᵣ B).ρ.invariants :=
  ⟨Rep.tensorInvariant A B y x.val, fun g => by rw [← Rep.hom_comm_apply, x.property]⟩

private theorem tensor_norm_fixed_left (A B : Rep.{u} ℤ G) (x : A.ρ.invariants) (y : B) :
    (A ⊗ᵣ B).ρ.norm (x.val ⊗ₜ[ℤ] y) = x.val ⊗ₜ[ℤ] B.ρ.norm y := by
  let f : B ⟶ A ⊗ᵣ B := Rep.tensorInvariant B A x ≫ (Rep.diagonalTensorCommIso B A).hom
  have hf (b : B) : f b = x.val ⊗ₜ[ℤ] b := Rep.diagonalTensorCommIso_tmul B A b x.val
  have hn := ConcreteCategory.congr_hom (Rep.norm_comm f) y
  exact (congrArg (A ⊗ᵣ B).ρ.norm (hf y).symm).trans (hn.trans (hf (B.ρ.norm y)))

private theorem fixedClass_natCard_sub_one (A : Rep.{u} ℤ G) (a : A.ρ.invariants) :
    fixedClass A ((Nat.card G - 1) • a) = -fixedClass A a := by
  let Q := fixedNormSubmodule A
  apply (tateZeroEquivFixedQuotient A).injective
  rw [tateZeroEquivFixedQuotient_fixedClass, map_neg,
    tateZeroEquivFixedQuotient_fixedClass, map_nsmul]
  have hz : Nat.card G • Q.mkQ a = 0 := by
    rw [← map_nsmul]
    apply (Submodule.Quotient.mk_eq_zero Q).mpr
    refine ⟨a.val, ?_⟩
    change A.ρ.norm a.val = Nat.card G • a.val
    rw [Representation.norm, LinearMap.sum_apply, Nat.card_eq_fintype_card]
    calc
      _ = ∑ _ : G, a.val := Finset.sum_congr rfl fun g _ => a.property g
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ]
  apply eq_neg_iff_add_eq_zero.mpr
  calc
    _ = (Nat.card G - 1 + 1) • Q.mkQ a := by rw [add_nsmul, one_nsmul]
    _ = 0 := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt Nat.card_pos), hz]

omit [Fintype G] in
private theorem tensorLeft_bar_boundary (A : Rep.{u} ℤ G)
    (T : ShortComplex (Rep.{u} ℤ G)) (g : G) (x : A.ρ.invariants)
    (z : T.X₁) (w : T.X₂) (h : T.f z = T.X₂.ρ g w - w) :
    (T.map (Rep.diagonalTensorLeft A)).f (x.val ⊗ₜ[ℤ] z) =
      @Sub.sub (↑(A ⊗ᵣ T.X₂)) _ ((A ⊗ᵣ T.X₂).ρ g (x.val ⊗ₜ[ℤ] w)) (x.val ⊗ₜ[ℤ] w) := by
  change (Rep.diagonalTensorMap (𝟙 A) T.f) (x.val ⊗ₜ[ℤ] z) =
    @Sub.sub (↑A ⊗[ℤ] ↑T.X₂) _ (TensorProduct.map (A.ρ g) (T.X₂.ρ g) (x.val ⊗ₜ[ℤ] w))
      (x.val ⊗ₜ[ℤ] w)
  have hmap := Rep.diagonalTensorMap_tmul (𝟙 A) T.f x.val z
  refine hmap.trans ?_
  change x.val ⊗ₜ[ℤ] T.f z =
    @Sub.sub (↑A ⊗[ℤ] ↑T.X₂) _ (TensorProduct.map (A.ρ g) (T.X₂.ρ g) (x.val ⊗ₜ[ℤ] w))
      (x.val ⊗ₜ[ℤ] w)
  rw [TensorProduct.map_tmul, x.property]
  let t := TensorProduct.mk ℤ A T.X₂ x.val
  exact (congrArg t h).trans (t.map_sub (T.X₂.ρ g w) w)

/-- The positive bar class against the original cyclic carry is the negative
of the original fixed tensor class, in the actual Tate group. -/
theorem tateCup_negTwoBar_carry (A B : Rep.{u} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (x : A.ρ.invariants) (a : B.ρ.invariants) :
    tateCup A B (-2) 2 0 (by decide) (tateNegTwoBarClass A g x.val (x.property g⁻¹))
        (tateCyclicCarryClass B g hg a) =
      -fixedClass (A ⊗ᵣ B) (tensorFixedVector A B x a) := by
  let C := Rep.coindShiftUp B
  let D := Rep.coindShiftUp C
  let S := Rep.coindShiftSequence B
  let T := Rep.coindShiftSequence C
  let hS := Rep.tensorLeft_coindShiftSequence_shortExact A B
  let hT := Rep.tensorLeft_coindShiftSequence_shortExact A C
  let b := carryDoubleShiftFixed B g hg a
  let w := coindShiftFunction C (carryShiftCocycle B g hg a)
  let z := carryShiftCocycle B g hg a g⁻¹
  let l := carryCoindLift B g hg a g⁻¹
  let m := (finiteCyclicGeneratorCoordinate g hg g⁻¹).val
  let a' : (A ⊗ᵣ B).ρ.invariants := tensorFixedVector A B x (m • a)
  have hb : (A ⊗ᵣ D).ρ g⁻¹ (x.val ⊗ₜ[ℤ] b.val) = x.val ⊗ₜ[ℤ] b.val := by
    change TensorProduct.map (A.ρ g⁻¹) (D.ρ g⁻¹) (x.val ⊗ₜ[ℤ] b.val) = _
    rw [TensorProduct.map_tmul, x.property, b.property]
  have hnorm : (A ⊗ᵣ C).ρ.norm (x.val ⊗ₜ[ℤ] z) = 0 := by
    rw [tensor_norm_fixed_left, carryShiftCocycle_norm_zero, TensorProduct.tmul_zero]
    rfl
  let wTensor : (↑A ⊗[ℤ] ↑T.X₂) := x.val ⊗ₜ[ℤ] w
  let zTensor : A ⊗ᵣ C := x.val ⊗ₜ[ℤ] z
  have hc := coindShiftFunction_cocycle_d C (carryShiftCocycle B g hg a)
    (carryShiftCocycle_mul B g hg a) g⁻¹
  have h₁ := tensorLeft_bar_boundary A T g⁻¹ x z w hc.symm
  have h₂ : (S.map (Rep.diagonalTensorLeft A)).f a'.val = (A ⊗ᵣ S.X₂).ρ.norm (x.val ⊗ₜ[ℤ] l) := by
    rw [tensor_norm_fixed_left, carryCoindLift_norm]
    rfl
  let v := tateNegTwoBarClass A g x.val (x.property g⁻¹)
  have hcarry := (tateClassOfDoubleShift_carryDoubleShiftFixed B g hg a).symm
  refine (congrArg (fun c : tate B 2 => tateCup A B (-2) 2 0 (by decide) v c) hcarry).trans ?_
  have hShift := tateCup_classOfDoubleShift A B (-2) v b
  refine hShift.trans ?_
  let m₀ := Rep.tensorInvariant A D b
  have hBar := tateMap_negTwoBarClass m₀ g x.val (x.property g⁻¹)
  let bar := tateNegTwoBarClass (A ⊗ᵣ D) g (x.val ⊗ₜ[ℤ] b.val) hb
  have hBar' : (tateFunctor G (-2)).map m₀ v = bar := hBar
  refine (congrArg (fun c => tateδ hS (-1) (tateδ hT (-2) c)) hBar').trans ?_
  have hδ₁ := tateδ_negTwoBarClass hT g _ hb wTensor rfl zTensor h₁ hnorm
  let Sₜ := S.map (Rep.diagonalTensorLeft A)
  let y₀ : Sₜ.X₂ := x.val ⊗ₜ[ℤ] l
  let z₀ : Sₜ.X₃ := zTensor
  have hLift : Sₜ.g y₀ = z₀ := rfl
  have hδ₂ := tateδ_negOneNormClass (S := Sₜ) hS z₀ hnorm y₀ hLift a' h₂
  let t : tate (A ⊗ᵣ C) (-1) := tateNegOneNormClass (A ⊗ᵣ C) zTensor hnorm
  have hFirst : tateδ hT (-2) bar = t := hδ₁
  have hSecond : tateδ hS (-1) t = fixedClass (A ⊗ᵣ B) a' := hδ₂
  let delta : tate (A ⊗ᵣ C) (-1) → tate (A ⊗ᵣ B) 0 := tateδ hS (-1)
  refine (congrArg delta hFirst).trans (hSecond.trans ?_)
  have hm : m = Nat.card G - 1 :=
    (sum_finiteCyclicCarry g hg g⁻¹).symm.trans (sum_finiteCyclicCarry_generator_inv g hg)
  have ha' : a' = m • tensorFixedVector A B x a := by
    apply Subtype.ext
    change x.val ⊗ₜ[ℤ] (m • a.val) = m • (x.val ⊗ₜ[ℤ] a.val)
    exact map_nsmul (TensorProduct.mk ℤ A B x.val) m a.val
  rw [ha', hm, fixedClass_natCard_sub_one]

/-- The original cyclic carry on independently sized coefficients, through
the same auxiliary lift used by the original cup construction. -/
def tateCyclicCarryViaLift (B : Rep.{v} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : B.ρ.invariants) : tate B 2 :=
  let F := Rep.universeLiftFunctor ℤ G
  (tateIsoCommon (F.obj B) 2).hom
    (tateCyclicCarryClass (F.obj B) (ULift.up g) (ulift_generator g hg)
      (universeLiftFixedVector B a))

private theorem tateIsoCommon_inv_cyclicCarryViaLift
    (B : Rep.{v} ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a : B.ρ.invariants) :
    let A := (Rep.universeLiftFunctor ℤ G).obj B
    (tateIsoCommon A 2).inv (tateCyclicCarryViaLift B g hg a) =
      tateCyclicCarryClass A (ULift.up g) (ulift_generator g hg) (universeLiftFixedVector B a) := by
  let A := (Rep.universeLiftFunctor ℤ G).obj B
  let c := tateCyclicCarryClass A (ULift.up g) (ulift_generator g hg) (universeLiftFixedVector B a)
  exact (tateIsoCommon A 2).hom_inv_id_apply c

omit [Fintype G] in
private theorem universeLiftIntegerTensorIso_hom_tmul
    (A B : Rep.{v} ℤ G) (a : A) (b : B) :
    (Rep.universeLiftIntegerTensorIso A B).hom
      (ULift.up a ⊗ₜ[ℤ] ULift.up b) = ULift.up (a ⊗ₜ[ℤ] b) := by
  let F := Rep.universeLiftFunctor ℤ G
  let lower (X : Rep.{v} ℤ G) : F.obj X ≃ₗ[ℤ] X :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let a' : F.obj A := ULift.up a
  let b' : F.obj B := ULift.up b
  have h := TensorProduct.congr_tmul (lower A) (lower B) a' b'
  exact congrArg (lower (A ⊗ᵣ B)).symm h

private def liftedTensorEvaluation (B : Rep.{v} ℤ G) (r : ℤ) :
    let F := Rep.universeLiftFunctor ℤ G
    let I := integralTrivialInteger.{u, v} G
    tate (F.obj I ⊗ᵣ F.obj B) r →ₗ[ℤ] tate B r := by
  intro F I
  let e := (tateFunctor (ULift.{v} G) r).mapIso (Rep.universeLiftIntegerTensorIso I B) ≪≫
    tateIsoCommon (F.obj (I ⊗ᵣ B)) r
  let unit := (tateFunctor G r).map (integerTensorLeftUnitIso B).hom
  exact unit.hom.comp e.hom.hom

private theorem tateCupTrivialInteger_lift_evaluation
    (B : Rep.{v} ℤ G) (p q r : ℤ) (h : p + q = r)
    (x : tate (integralTrivialInteger.{u, v} G) p) (y : tate B q) :
    let F := Rep.universeLiftFunctor ℤ G
    let I := integralTrivialInteger.{u, v} G
    let U := F.obj I
    let V := F.obj B
    tateCupTrivialInteger B p q r h y x =
      liftedTensorEvaluation B r
        (tateCup U V p q r h ((tateIsoCommon U p).inv x) ((tateIsoCommon V q).inv y)) := by
  rfl

private theorem liftedTensorFixedClass_unitor (B : Rep.{v} ℤ G)
    (a : B.ρ.invariants) :
    let F := Rep.universeLiftFunctor ℤ G
    let I := integralTrivialInteger.{u, v} G
    let U := F.obj I
    let A := F.obj B
    let i : I.ρ.invariants := ⟨integralTrivialIntegerOne G, fun _ => rfl⟩
    let i' := universeLiftFixedVector I i
    let a' := universeLiftFixedVector B a
    liftedTensorEvaluation B 0 (fixedClass (U ⊗ᵣ A) (tensorFixedVector U A i' a')) =
      fixedClass B a := by
  let J := ULift.{v} G
  let F := Rep.universeLiftFunctor ℤ G
  let I := integralTrivialInteger.{u, v} G
  let U := F.obj I
  let A := F.obj B
  let i : I.ρ.invariants := ⟨integralTrivialIntegerOne G, fun _ => rfl⟩
  let i' := universeLiftFixedVector I i
  let a' := universeLiftFixedVector B a
  let eT := Rep.universeLiftIntegerTensorIso I B
  let e := tateIsoCommon (F.obj (I ⊗ᵣ B)) 0
  let b₀ := tensorFixedVector I B i a
  dsimp only [liftedTensorEvaluation, LinearMap.comp_apply]
  have hT : (tateFunctor J 0).map eT.hom (fixedClass (U ⊗ᵣ A) (tensorFixedVector U A i' a')) =
      fixedClass (F.obj (I ⊗ᵣ B))
        (universeLiftFixedVector (I ⊗ᵣ B) b₀) := by
    rw [fixedClass_map]
    apply congrArg (fixedClass (F.obj (I ⊗ᵣ B)))
    apply Subtype.ext
    exact universeLiftIntegerTensorIso_hom_tmul I B i.val a.val
  have hB : (tateFunctor G 0).map (integerTensorLeftUnitIso B).hom
    (fixedClass (I ⊗ᵣ B) b₀) =
      fixedClass B a := by
    rw [fixedClass_map]
    apply congrArg (fixedClass B)
    apply Subtype.ext
    change (integerTensorLeftUnitIso B).hom (i.val ⊗ₜ[ℤ] a.val) = a.val
    exact (integerTensorLeftUnitIso_tmul B i.val a.val).trans (one_smul ℤ a.val)
  let f : tate (F.obj (I ⊗ᵣ B)) 0 → tate B 0 :=
    (tateFunctor G 0).map (integerTensorLeftUnitIso B).hom ∘ e.hom
  have h := tateIsoCommon_fixedClass_lift (I ⊗ᵣ B) b₀
  exact (congrArg f hT).trans
    ((congrArg ((tateFunctor G 0).map (integerTensorLeftUnitIso B).hom) h).trans hB)

private theorem tateIsoCommon_inv_unitBar (g : G) :
    let I := integralTrivialInteger.{u, v} G
    let U := (Rep.universeLiftFunctor ℤ G).obj I
    let i : I.ρ.invariants := ⟨integralTrivialIntegerOne G, fun _ => rfl⟩
    let i' := universeLiftFixedVector I i
    (tateIsoCommon U (-2)).inv (tateNegTwoUnitClass G g) =
      tateNegTwoBarClass U (ULift.up g) i'.val (i'.property (ULift.up g)⁻¹) := by
  let I := integralTrivialInteger.{u, v} G
  let U := (Rep.universeLiftFunctor ℤ G).obj I
  let i : I.ρ.invariants := ⟨integralTrivialIntegerOne G, fun _ => rfl⟩
  have h := tateNegTwoUnitClass_eq_bar.{u, v} g
  exact (congrArg (fun x : tate I (-2) => (tateIsoCommon U (-2)).inv x) h).trans
    (tateIsoCommon_inv_barClass I g i.val (i.property g⁻¹))

universe w₁ w₂

private theorem linearMap_eq_neg_of_eq
    {P : ModuleCat.{w₁} ℤ} {Q : ModuleCat.{w₂} ℤ} (f : P →ₗ[ℤ] Q)
    (x z : P) (y : Q) (hx : x = -z) (hy : f z = y) : f x = -y :=
  (congrArg f hx).trans ((map_neg f z).trans (congrArg Neg.neg hy))

/-- An evaluation of the original bar class on the lifted coefficients transports to
an evaluation on the original coefficients with the same sign. -/
theorem tateCupTrivialInteger_negTwo_of_lifted_cup (B : Rep.{v} ℤ G) (g : G)
    (y : tate B 2) (a : B.ρ.invariants)
    (hCup : let F := Rep.universeLiftFunctor ℤ G
      let I := integralTrivialInteger.{u, v} G
      let U := F.obj I
      let A := F.obj B
      let i : I.ρ.invariants := ⟨integralTrivialIntegerOne G, fun _ => rfl⟩
      let i' := universeLiftFixedVector I i
      let a' := universeLiftFixedVector B a
      tateCup U A (-2) 2 0 (by decide)
        (tateNegTwoBarClass U (ULift.up g) i'.val (i'.property (ULift.up g)⁻¹))
        ((tateIsoCommon A 2).inv y) =
        -fixedClass (U ⊗ᵣ A) (tensorFixedVector U A i' a')) :
    tateCupTrivialInteger B (-2) 2 0 (by decide) y (tateNegTwoUnitClass G g) =
      -fixedClass B a := by
  let F := Rep.universeLiftFunctor ℤ G
  let I := integralTrivialInteger.{u, v} G
  let U := F.obj I
  let A := F.obj B
  let i : I.ρ.invariants := ⟨integralTrivialIntegerOne G, fun _ => rfl⟩
  let i' := universeLiftFixedVector I i
  let a' := universeLiftFixedVector B a
  let z := fixedClass (U ⊗ᵣ A) (tensorFixedVector U A i' a')
  let b := tateNegTwoBarClass U (ULift.up g) i'.val (i'.property (ULift.up g)⁻¹)
  let x : tate I (-2) := tateNegTwoUnitClass G g
  let d : tate U (-2) := (tateIsoCommon U (-2)).inv x
  let y' : tate A 2 := (tateIsoCommon A 2).inv y
  let cup := tateCup U A (-2) 2 0 (by decide)
  let f := liftedTensorEvaluation B 0
  have hLift := tateCupTrivialInteger_lift_evaluation B (-2) 2 0 (by decide) x y
  have hOriginal : tateCupTrivialInteger B (-2) 2 0 (by decide) y x = f (cup d y') := by
    dsimp only at hLift
    dsimp only [f, cup, d, y', U, A, I, F]
    exact hLift
  have hBar : d = b := tateIsoCommon_inv_unitBar.{u, v} g
  have hValue : cup b y' = -z := hCup
  have hFixed : f z = fixedClass B a := liftedTensorFixedClass_unitor B a
  have hC : cup d y' = -z := (congrArg (fun t => cup t y') hBar).trans hValue
  have hMapped := linearMap_eq_neg_of_eq (P := tate (U ⊗ᵣ A) 0) (Q := tate B 0)
    f (cup d y') z (fixedClass B a) hC hFixed
  exact hOriginal.trans hMapped

/-- The exact `tateCupTrivialInteger` used by Tate–Nakayama sends the positive
bar class of a cyclic generator against the actual carry to the negative
class of its original invariant coefficient. -/
theorem tateCupTrivialInteger_negTwo_bar_carry (B : Rep.{v} ℤ G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a : B.ρ.invariants) :
    tateCupTrivialInteger B (-2) 2 0 (by decide) (tateCyclicCarryViaLift B g hg a)
      (tateNegTwoUnitClass G g) = -fixedClass B a := by
  apply tateCupTrivialInteger_negTwo_of_lifted_cup
  intro F I U A i i' a'
  rw [tateIsoCommon_inv_cyclicCarryViaLift B g hg a]
  exact tateCup_negTwoBar_carry U A (ULift.up g) (ulift_generator g hg) i' a'

end IntegralGroupCohomology.Universe
