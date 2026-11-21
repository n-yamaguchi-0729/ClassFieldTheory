/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogExtension
public import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.AutomorphismEquivariance
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianAutomorphismValuation
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.MixedCharCompleteExtension
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import Nyll.GaloisCohomology.FieldTheory.NormTraceNormalAmbient

/-!
# The logarithm of the actual field norm

The existing principal-unit logarithm gives the finite product law. Uniqueness
of an extension of a Henselian valuation makes the actual Galois conjugates
valuation preserving, so the norm product becomes the trace sum. A finite
normal closure supplies the ambient field for every finite separable source.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u v w

open scoped BigOperators
open ValuationTheory.DiscreteValuationField.ValuedExtension
  (exists_complete_valuation_of_finite_separable_of_residueChar)

variable {K : Type u} [Field K]

private def principalUnitOfSubOne
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (x : K) (hx : v (x - 1) < 1) :
    CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1 :=
  CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup
    (completeDVFOfWithZeroValuation v) le_rfl ⟨x - 1, hx.le⟩ (by
      rw [pow_one]
      exact (ValuationTheory.DiscreteValuationField.CompleteDVF.mem_maximalIdeal_iff
        (completeDVFOfWithZeroValuation v) _).mpr hx)

private def principalUnitValue
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v] :
    CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1 →* K where
  toFun a := (a.1.val : K)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem principalUnitOfSubOne_value
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (x : K) (hx : v (x - 1) < 1) :
    principalUnitValue v (principalUnitOfSubOne v x hx) = x := by
  let D := completeDVFOfWithZeroValuation v
  let a : D.valuationSubring := ⟨x - 1, hx.le⟩
  have ha : a ∈ D.maximalIdeal ^ 1 := by
    rw [pow_one]
    exact (ValuationTheory.DiscreteValuationField.CompleteDVF.mem_maximalIdeal_iff D a).mpr hx
  change (((CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow
    D le_rfl a ha).val : D.valuationSubring) : K) = x
  rw [CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val]
  change 1 + (x - 1) = x
  ring

private theorem principalUnitProduct_value
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {ι : Type*} (s : Finset ι) (x : ι → K) (hx : ∀ i, v (x i - 1) < 1) :
    principalUnitValue v (∏ i ∈ s, principalUnitOfSubOne v (x i) (hx i)) =
      ∏ i ∈ s, x i := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => principalUnitOfSubOne_value v (x i) (hx i)

/-- Finite products of first principal units remain first principal units. -/
theorem valuation_prod_sub_one_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    {ι : Type*} (s : Finset ι) (x : ι → K) (hx : ∀ i, v (x i - 1) < 1) :
    v ((∏ i ∈ s, x i) - 1) < 1 := by
  rw [← principalUnitProduct_value v s x hx]
  exact principalUnitSubOne_val_lt_one_ofWithZeroValuation v _

variable [CharZero K]

private theorem principalUnitLogOfMixedChar_value
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (a : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1) :
    (principalUnitLogOfMixedChar v p a).toAdd =
      logOnePlusSeriesFieldOfWithZeroValuation v (principalUnitValue v a - 1)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) :=
  principalUnitLogOfMixedChar_apply_toAdd v p a

/-- The finite product law for the same convergent field-element log series. -/
theorem logOnePlusSeriesField_prod_of_lt_one
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    {ι : Type*} (s : Finset ι) (x : ι → K) (hx : ∀ i, v (x i - 1) < 1) :
    logOnePlusSeriesFieldOfWithZeroValuation v ((∏ i ∈ s, x i) - 1)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) =
      ∑ i ∈ s, logOnePlusSeriesFieldOfWithZeroValuation v (x i - 1)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) := by
  have h := congrArg Multiplicative.toAdd
    (map_prod (principalUnitLogOfMixedChar v p)
      (fun i => principalUnitOfSubOne v (x i) (hx i)) s)
  rw [principalUnitLogOfMixedChar_value, principalUnitProduct_value, toAdd_prod] at h
  refine h.trans (Finset.sum_congr rfl ?_)
  intro i _
  rw [principalUnitLogOfMixedChar_value, principalUnitOfSubOne_value]

variable {L : Type v} [Field L] [CharZero L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]

private theorem log_norm_eq_trace_of_normal_ambient
    (E : Type w) [Field E] [CharZero E]
    [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [FiniteDimensional K E] [Normal K E]
    (vK : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (vL : _root_.Valuation L (WithZero (Multiplicative ℤ)))
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vK]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vL]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    [vK.HasExtension vL] [vL.HasExtension vE] [vK.HasExtension vE]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vK.valuationSubring) p]
    [CharP (IsLocalRing.ResidueField vL.valuationSubring) p]
    [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    (x : L) (hx : vL (x - 1) < 1) :
    logOnePlusSeriesFieldOfWithZeroValuation vK (Algebra.norm K x - 1)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) =
      Algebra.trace K L (logOnePlusSeriesFieldOfWithZeroValuation vL (x - 1)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) := by
  classical
  let τ (σ : L →ₐ[K] AlgebraicClosure E) : E ≃ₐ[K] E :=
    (σ.liftNormal (AlgebraicClosure E)).restrictNormal' E
  have hval (σ : E ≃ₐ[K] E) (a : E) : vE (σ a) = vE a := by
    let base := (completeDVFOfWithZeroValuation vK).toHenselianDVF
    let target := (completeDVFOfWithZeroValuation vE).toDVF
    have : base.toDVF.valuation.HasExtension target.valuation := ‹vK.HasExtension vE›
    exact ValuationTheory.DiscreteValuationField.HenselianDVF.valuation_algEquiv_eq
      base target σ a
  have hxE : vE (algebraMap L E x - 1) < 1 := by
    simpa only [map_sub, map_one] using
      (Valuation.HasExtension.val_map_lt_one_iff vL vE (x - 1)).mpr hx
  have hconj (σ : L →ₐ[K] AlgebraicClosure E) :
      vE (τ σ (algebraMap L E x) - 1) < 1 := by
    have h := hval (τ σ) (algebraMap L E x - 1)
    rw [map_sub, map_one] at h
    rw [h]
    exact hxE
  have hnorm : vK (Algebra.norm K x - 1) < 1 := by
    apply (Valuation.HasExtension.val_map_lt_one_iff vK vE _).mp
    rw [map_sub, map_one, Algebra.norm_eq_prod_liftNormal K L E]
    exact valuation_prod_sub_one_lt_one vE Finset.univ
      (fun σ => τ σ (algebraMap L E x)) hconj
  apply (algebraMap K E).injective
  rw [map_logOnePlusSeriesField_of_hasExtension vK vE p _ hnorm,
    map_sub, map_one, Algebra.norm_eq_prod_liftNormal K L E]
  rw [logOnePlusSeriesField_prod_of_lt_one vE p Finset.univ
    (fun σ => τ σ (algebraMap L E x)) hconj,
    Algebra.trace_eq_sum_liftNormal K L E]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_logOnePlusSeriesField_of_hasExtension vL vE p _ hx]
  simpa only [map_sub, map_one, AlgEquiv.coe_toRingEquiv] using
    (map_logOnePlusSeriesField_of_preserves vE (τ σ).toRingEquiv
      (hval (τ σ)) (algebraMap L E x - 1)).symm

/-- On principal units, the logarithm of the actual separable field norm is the
actual field trace of the same logarithm. No deep-domain bound is needed for
this identity; the strict exponential threshold is needed for invertibility.
The finite normal ambient field and its complete extension valuation are
constructed inside the proof. -/
theorem logOnePlusSeriesField_norm_eq_trace
    (vK : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (vL : _root_.Valuation L (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vK]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vL]
    [vK.HasExtension vL]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vK.valuationSubring) p]
    [CharP (IsLocalRing.ResidueField vL.valuationSubring) p]
    (x : L) (hx : vL (x - 1) < 1) :
    logOnePlusSeriesFieldOfWithZeroValuation vK (Algebra.norm K x - 1)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) =
      Algebra.trace K L (logOnePlusSeriesFieldOfWithZeroValuation vL (x - 1)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) := by
  let E := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Algebra L E := normalClosure.algebra K L (AlgebraicClosure L)
  let : FiniteDimensional L E := Module.Finite.right K L E
  obtain ⟨vE, hcomplete, hext, hchar⟩ :=
    exists_complete_valuation_of_finite_separable_of_residueChar (E := E) vL p
  let : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE := hcomplete
  let : vL.HasExtension vE := hext
  let : CharP (IsLocalRing.ResidueField vE.valuationSubring) p := hchar
  let : vK.HasExtension vE :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans vK vL vE
  exact log_norm_eq_trace_of_normal_ambient E vK vL vE p x hx

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
