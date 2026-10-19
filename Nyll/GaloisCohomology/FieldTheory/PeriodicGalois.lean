/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.PeriodicSubfield
import Mathlib.FieldTheory.Galois.Basic

/-!
# Galois extensions inside periodic subfields

The fixed field of an automorphism embeds canonically into every periodic
subfield. Restriction gives an actual finite cyclic action; its fixed field
is the original fixed field, and its order is the extension degree.
-/

noncomputable section

namespace RingAut

variable {F : Type*} [Field F]

/-- Every fixed element belongs to every periodic subfield. -/
theorem periodicSubfield_one_le (σ : RingAut F) (n : ℕ) :
    periodicSubfield σ 1 ≤ periodicSubfield σ n := by
  intro x hx
  have hfix : σ x = x := by
    have h : (σ ^ 1) x = x := hx
    simpa only [pow_one] using h
  change (σ ^ n) x = x
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', RingAut.mul_apply, ih, hfix]

/-- The algebra structure given by the inclusion of the actual fixed subfield. -/
abbrev periodicFixedAlgebra (σ : RingAut F) (n : ℕ) :
    Algebra (periodicSubfield σ 1) (periodicSubfield σ n) :=
  (Subfield.inclusion (periodicSubfield_one_le σ n)).toAlgebra

/-- Restriction to a periodic subfield has precisely the original fixed field. -/
def periodicFixedPointsEquiv (σ : RingAut F) (n : ℕ) :
    periodicSubfield σ 1 ≃+*
      FixedPoints.subfield (Subgroup.zpowers (periodicAut σ n)) (periodicSubfield σ n) := by
  let L := periodicSubfield σ n
  let α := periodicAut σ n
  let H := Subgroup.zpowers α
  let j : periodicSubfield σ 1 →+* L := Subfield.inclusion (periodicSubfield_one_le σ n)
  have hfix (x : periodicSubfield σ 1) : α • j x = j x := by
    apply Subtype.ext
    change σ (x : F) = x
    have h : (σ ^ 1) (x : F) = x := x.property
    simpa only [pow_one] using h
  let f : periodicSubfield σ 1 →+* FixedPoints.subfield H L :=
    j.codRestrict _ (fun x => by
      intro g
      obtain ⟨i, hi⟩ := g.property
      change (g : RingAut L) • j x = j x
      rw [← hi]
      exact MulAction.mem_fixedBy_zpow (hfix x) i)
  refine RingEquiv.ofBijective f ⟨f.injective, ?_⟩
  intro x
  have h : σ ((x : L) : F) = ((x : L) : F) :=
    congrArg (fun z : L => (z : F)) (x.property ⟨α, Subgroup.mem_zpowers α⟩)
  let y : periodicSubfield σ 1 := ⟨((x : L) : F), by
    change (σ ^ 1) ((x : L) : F) = ((x : L) : F)
    simpa only [pow_one] using h⟩
  exact ⟨y, Subtype.ext (Subtype.ext rfl)⟩

/-- The fixed-field comparison respects the canonical inclusion into the periodic field. -/
theorem periodicFixedPointsEquiv_commutes (σ : RingAut F) (n : ℕ) :
    let _ := periodicFixedAlgebra σ n
    (algebraMap _ (periodicSubfield σ n)).comp
        (periodicFixedPointsEquiv σ n).toRingHom =
      algebraMap (periodicSubfield σ 1) (periodicSubfield σ n) := rfl

/-- A positive periodic subfield is finite over the original fixed field. -/
theorem finiteDimensional_periodicSubfield (σ : RingAut F) (n : ℕ) (hn : n ≠ 0) :
    let _ := periodicFixedAlgebra σ n
    FiniteDimensional (periodicSubfield σ 1) (periodicSubfield σ n) := by
  intro alg
  let H := Subgroup.zpowers (periodicAut σ n)
  have : Finite H := finite_zpowers.mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, periodicAut_pow_period σ n⟩)
  exact Module.Finite.of_equiv_equiv (periodicFixedPointsEquiv σ n).symm
    (RingEquiv.refl _) (RingHom.ext (fun x => congrArg Subtype.val
      ((periodicFixedPointsEquiv σ n).apply_symm_apply x)))

/-- The extension of periodic subfields is Galois. -/
theorem isGalois_periodicSubfield (σ : RingAut F) (n : ℕ) (hn : n ≠ 0) :
    let _ := periodicFixedAlgebra σ n
    IsGalois (periodicSubfield σ 1) (periodicSubfield σ n) := by
  intro alg
  let H := Subgroup.zpowers (periodicAut σ n)
  have : Finite H := finite_zpowers.mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, periodicAut_pow_period σ n⟩)
  exact IsGalois.of_equiv_equiv (f := (periodicFixedPointsEquiv σ n).symm)
    (g := RingEquiv.refl _) (RingHom.ext (fun x => congrArg Subtype.val
      ((periodicFixedPointsEquiv σ n).apply_symm_apply x)))

/-- The actual extension degree is the order of the restricted automorphism. -/
theorem finrank_periodicSubfield (σ : RingAut F) (n : ℕ) (hn : n ≠ 0) :
    let _ := periodicFixedAlgebra σ n
    Module.finrank (periodicSubfield σ 1) (periodicSubfield σ n) =
      orderOf (periodicAut σ n) := by
  intro alg
  let L := periodicSubfield σ n
  let H := Subgroup.zpowers (periodicAut σ n)
  have : Finite H := finite_zpowers.mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, periodicAut_pow_period σ n⟩)
  let : Fintype H := Fintype.ofFinite H
  have : FaithfulSMul H L := ⟨fun {g h} he => Subtype.ext (RingEquiv.ext he)⟩
  calc
    Module.finrank (periodicSubfield σ 1) L = Module.finrank (FixedPoints.subfield H L) L :=
      Algebra.finrank_eq_of_equiv_equiv (periodicFixedPointsEquiv σ n) (RingEquiv.refl _)
        (periodicFixedPointsEquiv_commutes σ n)
    _ = Fintype.card H := FixedPoints.finrank_eq_card H L
    _ = orderOf (periodicAut σ n) := by rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]

/-- Transport the canonical fixed-field inclusion through an actual field equivalence. -/
abbrev periodicExtensionAlgebra {K : Type*} [Field K] (σ : RingAut F) (n : ℕ)
    (e : K ≃+* periodicSubfield σ 1) : Algebra K (periodicSubfield σ n) :=
  ((Subfield.inclusion (periodicSubfield_one_le σ n)).comp e.toRingHom).toAlgebra

/-- Finite Galois structure and degree after identifying the original fixed field. -/
theorem periodicExtension_properties {K : Type*} [Field K] (σ : RingAut F)
    (n : ℕ) (hn : n ≠ 0) (e : K ≃+* periodicSubfield σ 1) :
    let _ := periodicExtensionAlgebra σ n e
    FiniteDimensional K (periodicSubfield σ n) ∧ IsGalois K (periodicSubfield σ n) ∧
      Module.finrank K (periodicSubfield σ n) = orderOf (periodicAut σ n) := by
  intro alg
  let P := periodicSubfield σ n
  let fixedAlg : Algebra (periodicSubfield σ 1) P := periodicFixedAlgebra σ n
  have hfin : FiniteDimensional (periodicSubfield σ 1) P :=
    finiteDimensional_periodicSubfield σ n hn
  have hgal : IsGalois (periodicSubfield σ 1) P := isGalois_periodicSubfield σ n hn
  have hcomp : (algebraMap K P).comp e.symm.toRingHom =
      (RingEquiv.refl P).toRingHom.comp (algebraMap (periodicSubfield σ 1) P) :=
    RingHom.ext (fun x => congrArg (Subfield.inclusion (periodicSubfield_one_le σ n))
      (e.apply_symm_apply x))
  refine ⟨Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl P) hcomp,
    IsGalois.of_equiv_equiv (f := e.symm) (g := RingEquiv.refl P) hcomp, ?_⟩
  exact (Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl P) rfl).trans
    (finrank_periodicSubfield σ n hn)

end RingAut
