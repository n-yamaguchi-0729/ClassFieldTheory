/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! # Exact cardinalities of matrix projector images -/

@[expose] public section

open Function Matrix.Module

noncomputable section

namespace Matrix

variable {I R : Type*} [Ring R] [Fintype I] [DecidableEq I]
  (e : Matrix I I R)

/-- The fixed vectors of a matrix projector on an actual module. -/
def projectorFixed (M : Type*) [AddCommGroup M] [Module R M] : AddSubgroup (I → M) where
  carrier := {x | e • x = x}
  zero_mem' := smul_zero _
  add_mem' := by
    intro x y hx hy
    change e • x = x at hx
    change e • y = y at hy
    change e • (x + y) = x + y
    rw [smul_add, hx, hy]
  neg_mem' := by
    intro x hx
    change e • x = x at hx
    change e • (-x) = -x
    rw [smul_neg, hx]

theorem smul_projectorFixed (M : Type*) [AddCommGroup M] [Module R M] (x : projectorFixed e M) :
    e • x.val = x.val := x.property

variable {A B C : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

/-- Restriction of the original linear map to the fixed vectors. -/
def projectorFixedMap (f : A →ₗ[R] B) : projectorFixed e A →+ projectorFixed e B where
  toFun x := ⟨f.mapMatrixModule I x.val, by
    change e • f.mapMatrixModule I x.val = f.mapMatrixModule I x.val
    rw [← map_smul, smul_projectorFixed]⟩
  map_zero' := Subtype.ext (map_zero (f.mapMatrixModule I))
  map_add' x y := Subtype.ext (map_add (f.mapMatrixModule I) x.val y.val)

theorem projectorFixedMap_apply (f : A →ₗ[R] B) (x : projectorFixed e A) (i : I) :
    ((projectorFixedMap e f x : projectorFixed e B) : I → B) i = f (x.val i) := rfl

theorem projectorFixedMap_injective (f : A →ₗ[R] B) (hf : Injective f) :
    Injective (projectorFixedMap e f) := by
  intro x y h
  apply Subtype.ext
  funext i
  exact hf (congrArg (fun z : projectorFixed e B => z.val i) h)

theorem projectorFixedMap_surjective (he : IsIdempotentElem e) (f : A →ₗ[R] B)
    (hf : Surjective f) : Surjective (projectorFixedMap e f) := by
  intro y
  have hy (i : I) : ∃ x, f x = y.val i := hf _
  choose x hx using hy
  have hx' : f.mapMatrixModule I x = y.val := funext hx
  have hfix : e • (e • x) = e • x := by rw [← mul_smul, he.eq]
  use ⟨e • x, hfix⟩
  apply Subtype.ext
  change f.mapMatrixModule I (e • x) = y.val
  rw [map_smul, hx', smul_projectorFixed]

theorem projectorFixedMap_exact (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Injective f) (hex : Exact f g) :
    Exact (projectorFixedMap e f) (projectorFixedMap e g) := by
  intro y
  constructor
  · intro hy
    have hy' (i : I) : ∃ x, f x = y.val i := (hex _).mp
      (congrArg (fun z : projectorFixed e C => z.val i) hy)
    choose x hx using hy'
    have hx' : f.mapMatrixModule I x = y.val := funext hx
    have hxfix : e • x = x := by
      apply show Injective (f.mapMatrixModule I) from
        (fun a b h => funext fun i => hf (congrFun h i))
      rw [map_smul, hx', smul_projectorFixed]
    exact ⟨⟨x, hxfix⟩, Subtype.ext hx'⟩
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    funext i
    exact hex.apply_apply_eq_zero _

/-- An idempotent matrix preserves the cardinal product of a finite short
exact sequence under passage to its actual images. -/
theorem card_projectorFixed_mul_of_exact [Finite A] [Finite B] [Finite C]
    (he : IsIdempotentElem e) (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Injective f) (hg : Surjective g) (hex : Exact f g) :
    Nat.card (projectorFixed e B) =
      Nat.card (projectorFixed e A) * Nat.card (projectorFixed e C) := by
  let f' := projectorFixedMap e f
  let g' := projectorFixedMap e g
  have hk : g'.ker = f'.range := AddSubgroup.ext (fun x => projectorFixedMap_exact e f g hf hex x)
  have hf' : Nat.card f'.range = Nat.card (projectorFixed e A) :=
    Nat.card_range_of_injective (projectorFixedMap_injective e f hf)
  have hg' : Nat.card g'.range = Nat.card (projectorFixed e C) :=
    Nat.card_congr (Equiv.ofBijective (fun x : g'.range => x.val)
      ⟨Subtype.val_injective, fun x => ⟨⟨x, projectorFixedMap_surjective e he g hg x⟩, rfl⟩⟩)
  rw [← hf', ← hg', ← hk, ← AddSubgroup.index_ker, g'.ker.card_mul_index]

/-- The prime valuation of the cardinality of an actual projector image is
additive on finite short exact sequences. -/
theorem padicValNat_card_projectorFixed_add_of_exact (p : ℕ) [Fact p.Prime]
    [Finite A] [Finite B] [Finite C] (he : IsIdempotentElem e)
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Injective f) (hg : Surjective g)
    (hex : Exact f g) :
    padicValNat p (Nat.card (projectorFixed e B)) =
      padicValNat p (Nat.card (projectorFixed e A)) +
        padicValNat p (Nat.card (projectorFixed e C)) := by
  rw [card_projectorFixed_mul_of_exact e he f g hf hg hex]
  simp only [Nat.padicValNat_def]
  exact Nat.multiplicity_mul Nat.card_pos.ne' Nat.card_pos.ne'

/-- On a finite module, an actual projector gives the same cardinality on
the torsion and power quotient for a natural scalar. -/
theorem card_projectorFixed_ker_nsmul_eq_quotient [Finite A] (he : IsIdempotentElem e) (n : ℕ) :
    Nat.card (projectorFixed e (LinearMap.ker (n • (LinearMap.id : A →ₗ[R] A)))) =
      Nat.card (projectorFixed e (A ⧸ LinearMap.range (n • (LinearMap.id : A →ₗ[R] A)))) := by
  let f := n • (LinearMap.id : A →ₗ[R] A)
  let V := LinearMap.range f
  let : Finite (A ⧸ V) := Finite.of_surjective V.mkQ V.mkQ_surjective
  have h₁ : Exact (LinearMap.ker f).subtype f.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have h₂ : Exact V.subtype V.mkQ := by
    apply LinearMap.exact_iff.mpr
    rw [Submodule.ker_mkQ, Submodule.range_subtype]
  have hc₁ := card_projectorFixed_mul_of_exact e he _ _ Subtype.val_injective
    f.surjective_rangeRestrict h₁
  have hc₂ := card_projectorFixed_mul_of_exact e he _ _ Subtype.val_injective V.mkQ_surjective h₂
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card (projectorFixed e V))
  exact hc₁.symm.trans (hc₂.trans (mul_comm _ _))

end Matrix
