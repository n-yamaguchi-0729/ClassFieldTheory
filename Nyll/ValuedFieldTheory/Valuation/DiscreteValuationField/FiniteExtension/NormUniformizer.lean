/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# Uniformizers detected by their actual field norms

An integral element with prime field norm is a uniformizer. The Galois norm
product, invariance of normalized additive valuation, and the fundamental
ramification identity also prove that the extension is totally ramified.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace ValuationTheory.DiscreteValuationField

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField.ValuedExtension
open RamificationTheory.HilbertRamification.Higher

universe u v w x

/-- An integral element whose actual field norm is a prime parameter is a
uniformizer; the extension is totally ramified. -/
theorem isUniformizer_and_ramificationIndex_eq_degree_of_norm_eq_irreducible
    {C : Type u} {E : Type w} [Field C] [Field E] [Algebra C E]
    [FiniteDimensional C E] [IsGalois C E]
    (base : CompleteDVF.{u, v} C) (target : CompleteDVF.{w, x} E)
    [base.valuation.HasExtension target.valuation]
    (a : target.valuationSubring) (b : base.valuationSubring)
    (hb : Irreducible b) (hnorm : Algebra.norm C (a : E) = (b : C)) :
    target.valuation.IsUniformizer (a : E) ∧
      ramificationIndex base.toDVF target.toDVF = degree base.toDVF target.toDVF := by
  classical
  let : IsScalarTower base.valuationSubring target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base.toDVF target.toDVF :=
    hasUniqueValuationExtension_of_finite_separable base target
  let e := ramificationIndex base.toDVF target.toDVF
  let d := degree base.toDVF target.toDVF
  have horbit : integerMap base.toDVF target.toDVF b =
      ∏ σ : Gal(E/C),
        valuationSubringAutOfUniqueExtension
          (base := base.toDVF) (target := target.toDVF) huniq σ a := by
    apply Subtype.ext
    change algebraMap C E (b : C) = target.valuation.valuationSubring.subtype _
    rw [map_prod, ← hnorm]
    exact Algebra.norm_eq_prod_automorphisms C (a : E)
  have hprod : ∀ s : Finset Gal(E/C),
      IsDiscreteValuationRing.addVal target.valuationSubring
          (∏ σ ∈ s, valuationSubringAutOfUniqueExtension
            (base := base.toDVF) (target := target.toDVF) huniq σ a) =
        ∑ σ ∈ s, IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
            (base := base.toDVF) (target := target.toDVF) huniq σ a) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]
    | @insert σ s hσ ih =>
        rw [Finset.prod_insert hσ, Finset.sum_insert hσ,
          IsDiscreteValuationRing.addVal_mul, ih]
  have hprodVal : IsDiscreteValuationRing.addVal target.valuationSubring
      (∏ σ : Gal(E/C), valuationSubringAutOfUniqueExtension
        (base := base.toDVF) (target := target.toDVF) huniq σ a) =
      Nat.card Gal(E/C) • IsDiscreteValuationRing.addVal target.valuationSubring a := by
    simpa only [IsDiscreteValuationRing.addVal_ringEquiv, Finset.sum_const,
      Finset.card_univ, Nat.card_eq_fintype_card] using hprod Finset.univ
  have hcard : Nat.card Gal(E/C) = d := IsGalois.card_aut_eq_finrank C E
  have heq : (e : ℕ∞) =
      (d : ℕ∞) * IsDiscreteValuationRing.addVal target.valuationSubring a := by
    have h := congrArg (IsDiscreteValuationRing.addVal target.valuationSubring) horbit
    rw [addVal_integerMap_eq_ramificationIndex_nsmul,
      IsDiscreteValuationRing.addVal_uniformizer hb, hprodVal, hcard,
      nsmul_eq_mul, nsmul_eq_mul, mul_one] at h
    exact h
  have hdne : d ≠ 0 := by
    rw [← hcard]
    exact Nat.ne_of_gt Nat.card_pos
  have hfund : d = e * residueDegree base.toDVF target.toDVF :=
    degree_eq_ramificationIndex_mul_residueDegree_of_finite_separable base target
  have hene : e ≠ 0 := by
    intro he
    exact hdne (hfund.trans (by rw [he, zero_mul]))
  have hfne : residueDegree base.toDVF target.toDVF ≠ 0 := by
    intro hf
    exact hdne (hfund.trans (by rw [hf, mul_zero]))
  have hele : e ≤ d := by
    rw [hfund]
    exact Nat.le_mul_of_pos_right e (Nat.pos_of_ne_zero hfne)
  have hane : IsDiscreteValuationRing.addVal target.valuationSubring a ≠ 0 := by
    intro ha
    have he0 : (e : ℕ∞) = 0 := by rw [heq, ha, mul_zero]
    exact hene (by exact_mod_cast he0)
  have hdcoe : (d : ℕ∞) ≠ 0 := by exact_mod_cast hdne
  have havle : IsDiscreteValuationRing.addVal target.valuationSubring a ≤ 1 := by
    apply (ENat.mul_le_mul_left_iff hdcoe (ENat.natCast_ne_top d)).1
    rw [← heq, mul_one]
    exact_mod_cast hele
  have hav : IsDiscreteValuationRing.addVal target.valuationSubring a = 1 :=
    le_antisymm havle (Order.one_le_iff_ne_zero.mpr hane)
  have hed : e = d := by
    rw [hav, mul_one] at heq
    exact_mod_cast heq
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible target.valuationSubring
  have hval : IsDiscreteValuationRing.addVal target.valuationSubring a =
      IsDiscreteValuationRing.addVal target.valuationSubring π := by
    rw [hav, IsDiscreteValuationRing.addVal_uniformizer hπ]
  have hairr : Irreducible a :=
    ((IsDiscreteValuationRing.addVal_eq_iff_associated a π).1 hval).symm.irreducible hπ
  exact ⟨Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := target.valuation) hairr.maximalIdeal_eq, hed⟩

/-- A monic integral minimal polynomial with prime constant coefficient
supplies the norm witness for the actual power-basis generator. -/
theorem isUniformizer_and_ramificationIndex_eq_degree_of_integral_minpoly
    {C : Type u} {E : Type w} [Field C] [Field E] [Algebra C E]
    [FiniteDimensional C E] [IsGalois C E]
    (base : CompleteDVF.{u, v} C) (target : CompleteDVF.{w, x} E)
    [base.valuation.HasExtension target.valuation]
    [IsIntegralClosure target.valuationSubring base.valuationSubring E]
    (B : PowerBasis C E) (P : Polynomial base.valuationSubring)
    (hmonic : P.Monic)
    (hmap : P.map (algebraMap base.valuationSubring C) = minpoly C B.gen)
    (hcoeff : Irreducible (P.coeff 0)) :
    target.valuation.IsUniformizer B.gen ∧
      ramificationIndex base.toDVF target.toDVF = degree base.toDVF target.toDVF := by
  have hint : IsIntegral base.valuationSubring B.gen := by
    refine ⟨P, hmonic, ?_⟩
    change Polynomial.aeval B.gen P = 0
    rw [← Polynomial.aeval_map_algebraMap C B.gen P, hmap]
    exact minpoly.aeval C B.gen
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff
    (A := target.valuationSubring) (R := base.valuationSubring) (B := E)).mp hint
  change (a : E) = B.gen at ha
  let b : base.valuationSubring := (-1) ^ B.dim * P.coeff 0
  have hb : Irreducible b :=
    (irreducible_isUnit_mul (isUnit_neg_one.pow B.dim)).mpr hcoeff
  have hnorm : Algebra.norm C (a : E) = (b : C) := by
    rw [ha, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, ← hmap, Polynomial.coeff_map]
    change (-1 : C) ^ B.dim * algebraMap base.valuationSubring C (P.coeff 0) =
      algebraMap base.valuationSubring C ((-1) ^ B.dim * P.coeff 0)
    rw [map_mul, map_pow, map_neg, map_one]
  have h := isUniformizer_and_ramificationIndex_eq_degree_of_norm_eq_irreducible
    base target a b hb hnorm
  rw [ha] at h
  exact h

end ValuationTheory.DiscreteValuationField
