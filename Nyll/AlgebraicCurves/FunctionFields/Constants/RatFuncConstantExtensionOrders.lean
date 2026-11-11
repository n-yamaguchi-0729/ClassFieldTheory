/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Nyll.AlgebraicCurves.Places.ConstantExtension.ForgetConstantsRestrictEq
public import Nyll.AlgebraicCurves.Places.ConstantExtension.RamificationIndexForgetConstantsEqOneAdjoinRangeEqTop

/-! # Exact normalized orders under algebraic constant extensions -/

@[expose] public section

noncomputable section

open Polynomial AlgebraicCurve
open scoped RatFunc

-- The standard coefficient-extension algebra on polynomials is deliberately
-- local, as in mathlib's RatFunc.rank_ratFunc_ratFunc implementation.
attribute [local instance] Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

/-- The canonical fraction-field lift sends the variable to the variable. -/
theorem ratFunc_constantExtension_map_X :
    algebraMap (RatFunc k) (RatFunc L) RatFunc.X = RatFunc.X := by
  rw [← RatFunc.algebraMap_X,
    ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) (RatFunc L)]
  rw [RatFunc.algebraMap_apply]
  change algebraMap L[X] (RatFunc L)
      ((Polynomial.X : k[X]).map (algebraMap k L)) /
      algebraMap L[X] (RatFunc L) 1 = RatFunc.X
  simp only [Polynomial.map_X, RatFunc.algebraMap_X, map_one, div_one]

/-- The constants of a pure rational-function field are relatively
algebraically closed. This does not require k to be algebraically closed. -/
theorem ratFunc_isAlgebraic_mem_constants (f : RatFunc k)
    (hf : IsAlgebraic k f) : f ∈ (algebraMap k (RatFunc k)).range := by
  have hc : ∃ c : k, f = RatFunc.C c := by
    by_contra h
    exact (f.transcendental_of_ne_C h) hf
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, hc.symm⟩

variable [Algebra.IsAlgebraic k L]

/-- Every mapped constant is integral over k(t). -/
theorem ratFunc_constantExtension_constant_isIntegral (c : L) :
    IsIntegral (RatFunc k) (algebraMap L (RatFunc L) c) := by
  have hc : IsIntegral k c := Algebra.IsIntegral.isIntegral c
  exact (hc.map (IsScalarTower.toAlgHom k L (RatFunc L))).tower_top

/-- Actual generation of L(t) by k(t) and L; no generation hypothesis. -/
theorem ratFunc_constantExtension_adjoin_eq_top :
    Algebra.adjoin (RatFunc k)
      (Set.range (algebraMap L (RatFunc L))) = ⊤ := by
  let S : Set (RatFunc L) := Set.range (algebraMap L (RatFunc L))
  let E : IntermediateField (RatFunc k) (RatFunc L) :=
    IntermediateField.adjoin (RatFunc k) S
  have hXmem : (RatFunc.X : RatFunc L) ∈ E := by
    rw [← ratFunc_constantExtension_map_X (k := k) (L := L)]
    exact E.algebraMap_mem _
  have hpoly : ∀ p : L[X], algebraMap L[X] (RatFunc L) p ∈ E := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using E.add_mem hp hq
    | monomial n c =>
      rw [RatFunc.algebraMap_monomial]
      exact E.mul_mem
        (IntermediateField.subset_adjoin (RatFunc k) S ⟨c, rfl⟩)
        (E.pow_mem hXmem n)
  have htop : E = ⊤ := by
    apply top_unique
    intro f _
    exact RatFunc.induction_on f (fun p q _ => E.div_mem (hpoly p) (hpoly q))
  have halg : ∀ x ∈ S, IsAlgebraic (RatFunc k) x := by
    rintro _ ⟨c, rfl⟩
    exact (ratFunc_constantExtension_constant_isIntegral (k := k) c).isAlgebraic
  exact (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic halg).mp htop

/-- Integrality is derived from the constructed constants-generation result.
This is a theorem, not a new global instance. -/
theorem ratFunc_constantExtension_isIntegral :
    Algebra.IsIntegral (RatFunc k) (RatFunc L) := by
  have hle : Algebra.adjoin (RatFunc k)
      (Set.range (algebraMap L (RatFunc L))) ≤
      integralClosure (RatFunc k) (RatFunc L) := by
    apply Algebra.adjoin_le
    rintro _ ⟨c, rfl⟩
    exact ratFunc_constantExtension_constant_isIntegral (k := k) c
  refine ⟨fun f => ?_⟩
  apply hle
  rw [ratFunc_constantExtension_adjoin_eq_top (k := k) (L := L)]
  trivial

variable [Algebra.IsSeparable k L]

/-- Every arithmetic place admits a geometric/constant-extension place with
exactly the same normalized order on every rational function. All places,
including those defined by nonlinear irreducible polynomials, are covered.
No hgen, hconst, integrality, or ramification hypothesis is supplied externally. -/
theorem ratFunc_exists_constantExtension_ord_eq (V : Place k (RatFunc k)) :
    ∃ W : Place L (RatFunc L), ∀ f : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc L) f) = V.ord f := by
  let : Algebra.IsIntegral (RatFunc k) (RatFunc L) :=
    ratFunc_constantExtension_isIntegral (k := k) (L := L)
  have hgen := ratFunc_constantExtension_adjoin_eq_top (k := k) (L := L)
  have hconst : ∀ y : RatFunc k, IsAlgebraic k y →
      y ∈ (algebraMap k (RatFunc k)).range :=
    fun y hy => ratFunc_isAlgebraic_mem_constants y hy
  obtain ⟨W, hW⟩ :=
    Place.exists_forgetConstants_restrict_eq_of_isConstantFieldExtension
      (K := k) (K' := L) (F := RatFunc k) (F' := RatFunc L)
      (M := RatFunc k) hgen hconst V
  have he :=
    Place.ramificationIndex_forgetConstants_eq_one_of_adjoin_range_eq_top
      (K := k) hgen W
  refine ⟨W, ?_⟩
  intro f
  have h := (W.forgetConstants (K := k)).ord_restrict (F := RatFunc k) f
  simpa only [Place.ord_forgetConstants, he, hW, Nat.cast_one, one_mul] using h

/-- All-place geometric divisibility descends without a ramification factor.
For quadratic classification apply this with n = 2 and f equal to the quotient
of the transported radicand by the chosen coordinate. -/
theorem ratFunc_ord_dvd_of_constantExtension_ord_dvd
    (n : ℤ) (f : RatFunc k)
    (h : ∀ W : Place L (RatFunc L),
      n ∣ W.ord (algebraMap (RatFunc k) (RatFunc L) f))
    (V : Place k (RatFunc k)) : n ∣ V.ord f := by
  obtain ⟨W, hW⟩ := ratFunc_exists_constantExtension_ord_eq (L := L) V
  rw [← hW f]
  exact h W

end AnabelianGeometry.KummerTheory
