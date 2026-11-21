/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Nyll.GaloisCohomology.FieldTheory.NormTraceNormalAmbient
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitNorm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.Ramification.Different.Powers
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension

/-!
# Principal-unit norms in finite separable extensions

All embeddings into an algebraic closure act through automorphisms of a finite
normal closure. Their product is the same field norm. Integral-ring powers in
that closure prove the safe norm bound without a Galois assumption on the
original extension.
-/

@[expose] public section

noncomputable section

universe u v w

namespace LocalFieldTheory

open scoped BigOperators ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

section NormalAmbient

variable (K : Type u) (L : Type v) (E : Type w)
  [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [FiniteDimensional K E] [Normal K E]

variable [ValuativeRel K] [ValuativeRel L] [ValuativeRel E]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [Valuation.HasExtension (ValuativeRel.valuation L) (ValuativeRel.valuation E)]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] [hIntEK : IsIntegralClosure 𝒪[E] 𝒪[K] E]

omit [FiniteDimensional K E]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] in
private theorem integerUnitsMap_norm_eq_prod_liftNormal (a : 𝒪[L]ˣ) :
    integerUnitsMapOfValuationExtension K E (normIntegerUnits K L a) =
      ∏ σ : L →ₐ[K] AlgebraicClosure E,
        Units.mapEquiv
          (galoisGroupIntegerRingEquivOfIsIntegralClosure K E
            ((σ.liftNormal (AlgebraicClosure E)).restrictNormal' E)).toMulEquiv
          (integerUnitsMapOfValuationExtension L E a) := by
  apply integerUnitsToFieldUnits_injective E
  rw [map_prod]
  apply Units.ext
  rw [Units.coe_prod]
  change algebraMap K E (Algebra.norm K (a : L)) = _
  rw [Algebra.norm_eq_prod_liftNormal K L E]
  apply Finset.prod_congr rfl
  intro σ _
  rfl

variable [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [hIntEL : IsIntegralClosure 𝒪[E] 𝒪[L] E]

include E in
omit [FiniteDimensional K E] in
private theorem integerUnitsMap_norm_mem_of_normal_ambient
    {r : ℕ} (hr : 0 < r) {a : 𝒪[L]ˣ} (ha : a ∈ principalUnits L r) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L a) ∈
      principalUnits L r := by
  let : Algebra.IsIntegral 𝒪[L] 𝒪[E] :=
    integerRing_algebra_isIntegral_of_isIntegralClosure L E
  let e := (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[L]
  have he : 0 < e := Ideal.ramificationIdx_pos 𝒪[L] (𝓂[E] : Ideal 𝒪[E])
  have haE : integerUnitsMapOfValuationExtension L E a ∈ principalUnits E (e * r) := by
    have h := RamificationTheory.DiscreteValuationRing.map_mem_maximalIdeal_pow_mul
      𝒪[L] 𝒪[E] ha
    change algebraMap 𝒪[L] 𝒪[E] ((a : 𝒪[L]) - 1) ∈
      (𝓂[E] ^ (e * r) : Ideal 𝒪[E]) at h
    rw [map_sub, map_one] at h
    exact h
  have hnormE : integerUnitsMapOfValuationExtension K E (normIntegerUnits K L a) ∈
      principalUnits E (e * r) := by
    rw [integerUnitsMap_norm_eq_prod_liftNormal K L E]
    apply (principalUnits E (e * r)).prod_mem
    intro σ _
    exact principalUnits_integerRingEquiv_mem_self E (e * r)
      (galoisGroupIntegerRingEquivOfIsIntegralClosure K E
        ((σ.liftNormal (AlgebraicClosure E)).restrictNormal' E)) _ haE
  apply principalUnits_of_integerUnitsMap_mem_of_depth L E
    (Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hr (by omega)) he)
  have htower : integerUnitsMapOfValuationExtension L E
      (integerUnitsMapOfValuationExtension K L (normIntegerUnits K L a)) =
      integerUnitsMapOfValuationExtension K E (normIntegerUnits K L a) := by
    apply Units.ext
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply K L E
      (Algebra.norm K (a : L))).symm
  rw [htower]
  exact hnormE

end NormalAmbient

section Separable

variable (K : Type u) (L : Type v)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The finite separable norm, embedded back into its source, preserves every
positive principal-unit depth. The proof constructs the normal ambient field. -/
theorem integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isSeparable
    {r : ℕ} (hr : 0 < r) {a : 𝒪[L]ˣ} (ha : a ∈ principalUnits L r) :
    integerUnitsMapOfValuationExtension K L (normIntegerUnits K L a) ∈
      principalUnits L r := by
  let E := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Algebra L E := normalClosure.algebra K L (AlgebraicClosure L)
  let : FiniteDimensional L E := Module.Finite.right K L E
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField L E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel L E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField L E
  let : Valuation.HasExtension (ValuativeRel.valuation L) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension L E
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      (ValuativeRel.valuation K) (ValuativeRel.valuation L) (ValuativeRel.valuation E)
  let : Algebra.IsSeparable L E := Algebra.isSeparable_tower_top_of_isSeparable K L E
  let hIntEK : IsIntegralClosure 𝒪[E] 𝒪[K] E := localCompleteDVF_integerRing_isIntegralClosure K E
  let hIntEL : IsIntegralClosure 𝒪[E] 𝒪[L] E := localCompleteDVF_integerRing_isIntegralClosure L E
  exact integerUnitsMap_norm_mem_of_normal_ambient K L E (hIntEK := hIntEK) (hIntEL := hIntEL) hr ha

/-- The safe norm bound holds for every finite separable local extension. -/
theorem normIntegerUnits_mem_principalUnits_of_depth_of_isSeparable
    {r m : ℕ} (hr : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) < r)
    {a : 𝒪[L]ˣ} (ha : a ∈ principalUnits L r) :
    normIntegerUnits K L a ∈ principalUnits K m :=
  principalUnits_of_integerUnitsMap_mem_of_depth K L hr
    (integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isSeparable K L
      (Nat.zero_lt_of_lt hr) ha)

end Separable

/-- The actual field norm carries `U_L^r` into `U_K^m` at the safe depth,
with no normality or integral-closure hypothesis added to the extension. -/
theorem fieldPrincipalUnits_le_norm_preimage_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {r m : ℕ} (hr : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (m - 1) < r) :
    fieldPrincipalUnits L r ≤ (fieldPrincipalUnits K m).comap (normUnits K L) := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  rintro u ⟨a, ha, rfl⟩
  exact ⟨normIntegerUnits K L a,
    normIntegerUnits_mem_principalUnits_of_depth_of_isSeparable K L hr ha, rfl⟩

/-- For positive `r`, the actual separable norm lands at the ceiling of `r / e`,
written as `(r - 1) / e + 1` in natural numbers. -/
theorem fieldPrincipalUnits_norm_map_le_ceil
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    {r : ℕ} (hr : 1 ≤ r) :
    (fieldPrincipalUnits L r).map (normUnits K L) ≤
      fieldPrincipalUnits K ((r - 1) / (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] + 1) := by
  have hfloor := Nat.div_mul_le_self (r - 1)
    ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K])
  have hdepth : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] *
      (((r - 1) / (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] + 1) - 1) < r := by
    rw [Nat.add_sub_cancel, Nat.mul_comm]
    omega
  rintro _ ⟨a, ha, rfl⟩
  exact fieldPrincipalUnits_le_norm_preimage_of_isSeparable K L hdepth ha

end LocalFieldTheory
