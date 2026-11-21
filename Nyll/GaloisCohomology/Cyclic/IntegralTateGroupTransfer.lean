/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateDimensionShift
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInducedShift
public import Nyll.GaloisCohomology.Cyclic.IntegralTateSubgroupShift
public import Nyll.GaloisCohomology.Cyclic.IntegralTateZeroTransfers

/-!
# Restriction and corestriction in all integral Tate degrees

The maps start with the original inclusion and coset norm in degree zero.
The actual dimension-shift connecting maps over the group and the subgroup
transport these maps to every integer degree. No additional choice of
comparison isomorphisms is involved.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] [Fintype (G ⧸ H)]

/-- Restriction in nonnegative degrees via the actual coinduced sequence. -/
def tateRestrictNonnegative : (n : ℕ) → (A : Rep.{u} ℤ G) →
    tate A n →ₗ[ℤ] tate (Rep.res H.subtype A) n
  | 0, A => tateZeroRestrict H A
  | n + 1, A => (subgroupCoindShiftEquiv H A n).toLinearMap.comp
    ((tateRestrictNonnegative n (Rep.coindShiftUp A)).comp
      (coindShiftUpEquiv A n).symm.toLinearMap)

/-- Restriction in negative degrees via the actual induced sequence. -/
def tateRestrictNegative : (n : ℕ) → (A : Rep.{u} ℤ G) →
    tate A (Int.negSucc n) →ₗ[ℤ] tate (Rep.res H.subtype A) (Int.negSucc n)
  | 0, A =>
    let B := Rep.indShiftDown A
    let h : Int.negSucc 0 + 1 = 0 := by omega
    let e := (eqToIso (congrArg (tate B) h)).toLinearEquiv
    let eH := (eqToIso (congrArg (tate (Rep.res H.subtype B)) h)).toLinearEquiv
    ((subgroupIndShiftEquiv H A (Int.negSucc 0)).trans eH).symm.toLinearMap.comp
      ((tateZeroRestrict H B).comp ((indShiftDownEquiv A (Int.negSucc 0)).trans e).toLinearMap)
  | n + 1, A =>
    let B := Rep.indShiftDown A
    let h : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
    let e := (eqToIso (congrArg (tate B) h)).toLinearEquiv
    let eH := (eqToIso (congrArg (tate (Rep.res H.subtype B)) h)).toLinearEquiv
    ((subgroupIndShiftEquiv H A (Int.negSucc (n + 1))).trans eH).symm.toLinearMap.comp
      ((tateRestrictNegative n B).comp
        ((indShiftDownEquiv A (Int.negSucc (n + 1))).trans e).toLinearMap)

/-- Corestriction in nonnegative degrees via the actual coinduced sequence. -/
def tateCorestrictNonnegative : (n : ℕ) → (A : Rep.{u} ℤ G) →
    tate (Rep.res H.subtype A) n →ₗ[ℤ] tate A n
  | 0, A => tateZeroCorestrict H A
  | n + 1, A => (coindShiftUpEquiv A n).toLinearMap.comp
    ((tateCorestrictNonnegative n (Rep.coindShiftUp A)).comp
      (subgroupCoindShiftEquiv H A n).symm.toLinearMap)

/-- Corestriction in negative degrees via the actual induced sequence. -/
def tateCorestrictNegative : (n : ℕ) → (A : Rep.{u} ℤ G) →
    tate (Rep.res H.subtype A) (Int.negSucc n) →ₗ[ℤ] tate A (Int.negSucc n)
  | 0, A =>
    let B := Rep.indShiftDown A
    let h : Int.negSucc 0 + 1 = 0 := by omega
    let e := (eqToIso (congrArg (tate B) h)).toLinearEquiv
    let eH := (eqToIso (congrArg (tate (Rep.res H.subtype B)) h)).toLinearEquiv
    ((indShiftDownEquiv A (Int.negSucc 0)).trans e).symm.toLinearMap.comp
      ((tateZeroCorestrict H B).comp
        ((subgroupIndShiftEquiv H A (Int.negSucc 0)).trans eH).toLinearMap)
  | n + 1, A =>
    let B := Rep.indShiftDown A
    let h : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
    let e := (eqToIso (congrArg (tate B) h)).toLinearEquiv
    let eH := (eqToIso (congrArg (tate (Rep.res H.subtype B)) h)).toLinearEquiv
    ((indShiftDownEquiv A (Int.negSucc (n + 1))).trans e).symm.toLinearMap.comp
      ((tateCorestrictNegative n B).comp
        ((subgroupIndShiftEquiv H A (Int.negSucc (n + 1))).trans eH).toLinearMap)

/-- The subgroup restriction map in every integer Tate degree. -/
def tateRestrict (A : Rep.{u} ℤ G) (n : ℤ) :
    tate A n →ₗ[ℤ] tate (Rep.res H.subtype A) n :=
  match n with
  | .ofNat i => tateRestrictNonnegative H i A
  | .negSucc i => tateRestrictNegative H i A

/-- The subgroup corestriction map in every integer Tate degree. -/
def tateCorestrict (A : Rep.{u} ℤ G) (n : ℤ) :
    tate (Rep.res H.subtype A) n →ₗ[ℤ] tate A n :=
  match n with
  | .ofNat i => tateCorestrictNonnegative H i A
  | .negSucc i => tateCorestrictNegative H i A

/-- On a degree-zero fixed class restriction keeps the original vector. -/
theorem tateRestrict_zero_fixedClass (A : Rep.{u} ℤ G) (x : A.ρ.invariants) :
    tateRestrict H A 0 (fixedClass A x) =
      fixedClass (Rep.res H.subtype A) (restrictInvariants H A x) :=
  tateZeroRestrict_fixedClass H A x

/-- On a degree-zero fixed class corestriction takes the actual relative norm. -/
theorem tateCorestrict_zero_fixedClass (A : Rep.{u} ℤ G)
    (x : (Rep.res H.subtype A).ρ.invariants) :
    tateCorestrict H A 0 (fixedClass (Rep.res H.subtype A) x) =
      fixedClass A (corestrictInvariants H A x) :=
  tateZeroCorestrict_fixedClass H A x

/-- Restriction commutes with the upward shift in a nonnegative degree. -/
theorem tateRestrict_coindShift (A : Rep.{u} ℤ G) (n : ℕ)
    (x : tate (Rep.coindShiftUp A) n) :
    tateRestrict H A (n + 1 : ℕ) (coindShiftUpEquiv A n x) =
      subgroupCoindShiftEquiv H A n (tateRestrict H (Rep.coindShiftUp A) n x) := by
  change subgroupCoindShiftEquiv H A n (tateRestrictNonnegative H n (Rep.coindShiftUp A)
    ((coindShiftUpEquiv A n).symm (coindShiftUpEquiv A n x))) =
      subgroupCoindShiftEquiv H A n (tateRestrictNonnegative H n (Rep.coindShiftUp A) x)
  rw [LinearEquiv.symm_apply_apply]

/-- Corestriction commutes with the upward shift in a nonnegative degree. -/
theorem tateCorestrict_coindShift (A : Rep.{u} ℤ G) (n : ℕ)
    (x : tate (Rep.res H.subtype (Rep.coindShiftUp A)) n) :
    tateCorestrict H A (n + 1 : ℕ) (subgroupCoindShiftEquiv H A n x) =
      coindShiftUpEquiv A n (tateCorestrict H (Rep.coindShiftUp A) n x) := by
  change coindShiftUpEquiv A n (tateCorestrictNonnegative H n (Rep.coindShiftUp A)
    ((subgroupCoindShiftEquiv H A n).symm (subgroupCoindShiftEquiv H A n x))) =
      coindShiftUpEquiv A n (tateCorestrictNonnegative H n (Rep.coindShiftUp A) x)
  rw [LinearEquiv.symm_apply_apply]

private theorem transfer_commutes_with_degree_eq
    {J : Type u} [Group J] [Fintype J] {A : Rep.{u} ℤ G} {B : Rep.{u} ℤ J}
    (m : ∀ n : ℤ, tate A n →ₗ[ℤ] tate B n) {i j : ℤ} (h : i = j) (x : tate A i) :
    (eqToIso (congrArg (tate B) h)).toLinearEquiv.symm
        (m j ((eqToIso (congrArg (tate A) h)).toLinearEquiv x)) = m i x := by
  subst j
  rfl

/-- Restriction commutes with the downward shift in a negative degree. -/
theorem tateRestrict_indShift (A : Rep.{u} ℤ G) (n : ℕ)
    (x : tate A (Int.negSucc n)) :
    subgroupIndShiftEquiv H A (Int.negSucc n) (tateRestrict H A (Int.negSucc n) x) =
      tateRestrict H (Rep.indShiftDown A) (Int.negSucc n + 1)
        (indShiftDownEquiv A (Int.negSucc n) x) := by
  cases n with
  | zero =>
    let B := Rep.indShiftDown A
    let h : Int.negSucc 0 + 1 = 0 := by omega
    let e := indShiftDownEquiv A (Int.negSucc 0)
    let eH := subgroupIndShiftEquiv H A (Int.negSucc 0)
    let c := (eqToIso (congrArg (tate B) h)).toLinearEquiv
    let cH := (eqToIso (congrArg (tate (Rep.res H.subtype B)) h)).toLinearEquiv
    let m (i : ℤ) := tateRestrict H B i
    have hcast := transfer_commutes_with_degree_eq m h (e x)
    change eH (eH.symm (cH.symm (m 0 (c (e x))))) = m (Int.negSucc 0 + 1) (e x)
    exact (eH.apply_symm_apply _).trans hcast
  | succ n =>
    let B := Rep.indShiftDown A
    let h : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
    let e := indShiftDownEquiv A (Int.negSucc (n + 1))
    let eH := subgroupIndShiftEquiv H A (Int.negSucc (n + 1))
    let c := (eqToIso (congrArg (tate B) h)).toLinearEquiv
    let cH := (eqToIso (congrArg (tate (Rep.res H.subtype B)) h)).toLinearEquiv
    let m (i : ℤ) := tateRestrict H B i
    have hcast := transfer_commutes_with_degree_eq m h (e x)
    change eH (eH.symm (cH.symm (m (Int.negSucc n) (c (e x))))) =
      m (Int.negSucc (n + 1) + 1) (e x)
    exact (eH.apply_symm_apply _).trans hcast

/-- Corestriction commutes with the downward shift in a negative degree. -/
theorem tateCorestrict_indShift (A : Rep.{u} ℤ G) (n : ℕ)
    (x : tate (Rep.res H.subtype A) (Int.negSucc n)) :
    indShiftDownEquiv A (Int.negSucc n) (tateCorestrict H A (Int.negSucc n) x) =
      tateCorestrict H (Rep.indShiftDown A) (Int.negSucc n + 1)
        (subgroupIndShiftEquiv H A (Int.negSucc n) x) := by
  cases n with
  | zero =>
    let B := Rep.indShiftDown A
    let h : Int.negSucc 0 + 1 = 0 := by omega
    let e := indShiftDownEquiv A (Int.negSucc 0)
    let eH := subgroupIndShiftEquiv H A (Int.negSucc 0)
    let c := (eqToIso (congrArg (tate B) h)).toLinearEquiv
    let cH := (eqToIso (congrArg (tate (Rep.res H.subtype B)) h)).toLinearEquiv
    let m (i : ℤ) := tateCorestrict H B i
    have hcast := transfer_commutes_with_degree_eq m h (eH x)
    change e (e.symm (c.symm (m 0 (cH (eH x))))) = m (Int.negSucc 0 + 1) (eH x)
    exact (e.apply_symm_apply _).trans hcast
  | succ n =>
    let B := Rep.indShiftDown A
    let h : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
    let e := indShiftDownEquiv A (Int.negSucc (n + 1))
    let eH := subgroupIndShiftEquiv H A (Int.negSucc (n + 1))
    let c := (eqToIso (congrArg (tate B) h)).toLinearEquiv
    let cH := (eqToIso (congrArg (tate (Rep.res H.subtype B)) h)).toLinearEquiv
    let m (i : ℤ) := tateCorestrict H B i
    have hcast := transfer_commutes_with_degree_eq m h (eH x)
    change e (e.symm (c.symm (m (Int.negSucc n) (cH (eH x))))) =
      m (Int.negSucc (n + 1) + 1) (eH x)
    exact (e.apply_symm_apply _).trans hcast

private theorem tateCorestrict_restrict_of_indShift (A : Rep.{u} ℤ G) (n : ℕ)
    (x : tate A (Int.negSucc n))
    (hx : tateCorestrict H (Rep.indShiftDown A) (Int.negSucc n + 1)
          (tateRestrict H (Rep.indShiftDown A) (Int.negSucc n + 1)
            (indShiftDownEquiv A (Int.negSucc n) x)) =
        H.index • indShiftDownEquiv A (Int.negSucc n) x) :
    tateCorestrict H A (Int.negSucc n) (tateRestrict H A (Int.negSucc n) x) = H.index • x := by
  let i := Int.negSucc n
  let e := indShiftDownEquiv A i
  let eH := subgroupIndShiftEquiv H A i
  apply e.injective
  calc
    _ = tateCorestrict H (Rep.indShiftDown A) (i + 1) (eH (tateRestrict H A i x)) :=
      tateCorestrict_indShift H A n (tateRestrict H A i x)
    _ = tateCorestrict H (Rep.indShiftDown A) (i + 1)
          (tateRestrict H (Rep.indShiftDown A) (i + 1) (e x)) :=
      congrArg (tateCorestrict H (Rep.indShiftDown A) (i + 1)) (tateRestrict_indShift H A n x)
    _ = H.index • e x := hx
    _ = _ := (map_nsmul e H.index x).symm

/-- Corestriction after restriction is multiplication by the subgroup index
on the original Tate object in every integer degree. -/
theorem tateCorestrict_restrict (n : ℤ) (A : Rep.{u} ℤ G) (x : tate A n) :
    tateCorestrict H A n (tateRestrict H A n x) = H.index • x := by
  cases n with
  | ofNat i =>
    induction i generalizing A with
    | zero => exact tateZeroCorestrict_restrict H A x
    | succ i ih =>
      let e : tate (Rep.coindShiftUp A) i ≃ₗ[ℤ] tate A (Int.ofNat (i + 1)) :=
        coindShiftUpEquiv A i
      obtain ⟨z, rfl⟩ := e.surjective x
      let y := tateRestrict H (Rep.coindShiftUp A) i z
      calc
        _ = tateCorestrict H A (Int.ofNat (i + 1)) (subgroupCoindShiftEquiv H A i y) :=
          congrArg (tateCorestrict H A (Int.ofNat (i + 1))) (tateRestrict_coindShift H A i z)
        _ = e (tateCorestrict H (Rep.coindShiftUp A) i y) := tateCorestrict_coindShift H A i y
        _ = _ := (congrArg e (ih (Rep.coindShiftUp A) z)).trans (map_nsmul e H.index z)
  | negSucc i =>
    induction i generalizing A with
    | zero =>
      exact tateCorestrict_restrict_of_indShift H A 0 x (tateZeroCorestrict_restrict H _ _)
    | succ i ih =>
      exact tateCorestrict_restrict_of_indShift H A (i + 1) x (ih _ _)

end IntegralGroupCohomology.Universe
