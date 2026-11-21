/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiltered
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilNormNaturality
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparablePrincipalUnitNorm
import Nyll.ValuedFieldTheory.Ramification.Herbrand.Bounds

/-!
# Norm images of principal units in absolute reciprocity

For a finite separable fixed field, the actual norm image at every depth is
detected by the image of the upper field's absolute upper group in the lower
absolute abelianization. This includes wild ramification and fractional steps.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation ClassFieldTower.Martinet.Shafarevich
open LocalFieldTheory ProCGroups.Abelian RamificationTheory.LocalField
open RamificationTheory.HilbertRamification.Higher
open RamificationTheory.DiscreteValuationField.DVF (HasUniqueValuationExtension)

universe u v

section Congruences

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Modulo the given base unit step, actual norms of depth `r` factor
through the finite quotient by the indicated deeper step upstairs. -/
def fieldPrincipalUnitsNormQuotientMap (r n : ℕ) :
    let m := max r ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (n - 1) + 1)
    (fieldPrincipalUnits L r ⧸ (fieldPrincipalUnits L m).subgroupOf (fieldPrincipalUnits L r)) →*
      Kˣ ⧸ fieldPrincipalUnits K n := by
  intro m
  let q := QuotientGroup.mk' (fieldPrincipalUnits K n)
  refine QuotientGroup.lift _ (q.comp ((normUnits K L).comp (fieldPrincipalUnits L r).subtype)) ?_
  intro y hy
  change q (normUnits K L (y : Lˣ)) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  exact fieldPrincipalUnits_le_norm_preimage_of_isSeparable K L
    ((Nat.lt_succ_self _).trans_le (le_max_right _ _)) hy

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] in
/-- The source of each principal-unit norm coordinate is finite. -/
theorem fieldPrincipalUnitsNormQuotientMap_source_finite (r n : ℕ) :
    let m := max r ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (n - 1) + 1)
    Finite (fieldPrincipalUnits L r ⧸
      (fieldPrincipalUnits L m).subgroupOf (fieldPrincipalUnits L r)) := by
  intro m
  let : CompactSpace (fieldPrincipalUnits L r) :=
    isCompact_iff_compactSpace.mp (isCompact_fieldPrincipalUnits L r)
  apply Subgroup.quotient_finite_of_isOpen
  exact (isOpen_fieldPrincipalUnits L m).preimage continuous_subtype_val

/-- At any depth, including wild levels, the actual principal-unit norm
image is determined by its finite congruence coordinates. -/
theorem mem_fieldPrincipalUnits_norm_map_iff_quotients (r : ℕ) (x : Kˣ) :
    x ∈ (fieldPrincipalUnits L r).map (normUnits K L) ↔
      ∀ n : ℕ, (x : Kˣ ⧸ fieldPrincipalUnits K n) ∈
        (fieldPrincipalUnitsNormQuotientMap K L r n).range := by
  let S := (fieldPrincipalUnits L r).map (normUnits K L)
  have hcont : Continuous (normUnits K L) := by
    apply continuous_of_continuousAt_one (normUnits K L)
    rw [continuousAt_def, map_one]
    intro V hV
    obtain ⟨n, _hn, hV'⟩ := exists_fieldPrincipalUnits_subset_of_mem_nhds K V hV
    let m := (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (n - 1) + 1
    apply Filter.mem_of_superset ((isOpen_fieldPrincipalUnits L m).mem_nhds (Subgroup.one_mem _))
    intro y hy
    exact hV' (fieldPrincipalUnits_le_norm_preimage_of_isSeparable K L (Nat.lt_succ_self _) hy)
  let : T2Space K := localFieldT2Space K
  have hclosed : IsClosed (S : Set Kˣ) := ((isCompact_fieldPrincipalUnits L r).image hcont).isClosed
  constructor
  · rintro ⟨y, hy, rfl⟩ n
    exact ⟨QuotientGroup.mk ⟨y, hy⟩, rfl⟩
  · intro h
    change x ∈ (S : Set Kˣ)
    rw [← hclosed.closure_eq, mem_closure_iff_nhds]
    intro V hV
    let B := (fun z : Kˣ => x * z) ⁻¹' V
    have hB : B ∈ nhds (1 : Kˣ) := by
      have hc : Continuous (fun z : Kˣ => x * z) := continuous_const.mul continuous_id
      apply hc.continuousAt.preimage_mem_nhds
      exact (mul_one x).symm ▸ hV
    obtain ⟨n, _hn, hnB⟩ := exists_fieldPrincipalUnits_subset_of_mem_nhds K B hB
    obtain ⟨z, hz⟩ := h n
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    change (normUnits K L (y : Lˣ) : Kˣ ⧸ fieldPrincipalUnits K n) =
      (x : Kˣ ⧸ fieldPrincipalUnits K n) at hz
    let a := normUnits K L (y : Lˣ)
    have ha : x⁻¹ * a ∈ fieldPrincipalUnits K n :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact' hz.symm)
    have haV : x * (x⁻¹ * a) ∈ V := hnB ha
    rw [← mul_assoc, mul_inv_cancel, one_mul] at haV
    exact ⟨a, haV, ⟨(y : Lˣ), y.property, rfl⟩⟩

/-- At the first integral Herbrand step the actual norm lands in the first
principal-unit group, including for wild Galois extensions. -/
theorem fieldPrincipalUnits_norm_map_le_at_inverseHerbrand_one [IsGalois K L] :
    let huniq : HasUniqueValuationExtension.{u, u, v, 0, 0}
        (localCompleteDVF K).toDVF (chosenLocalExtensionCompleteDVF K L).toDVF :=
      chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K L
    let t := inverseHerbrandFunctionOfUniqueExtension huniq 1
    (fieldPrincipalUnits L ⌊t⌋₊).map (normUnits K L) ≤ fieldPrincipalUnits K 1 := by
  intro huniq t
  have hφ : herbrandFunctionOfUniqueExtension huniq 1 ≤ (1 : ℝ) := by
    rw [herbrandFunctionOfUniqueExtension_apply]
    have hBound := (lowerRamificationFiltrationOfUniqueExtension huniq).herbrandFunction_nat_le 1
    simpa only [Nat.cast_one] using hBound
  have ht : (1 : ℝ) ≤ t := by
    calc
      1 = inverseHerbrandFunctionOfUniqueExtension huniq
          (herbrandFunctionOfUniqueExtension huniq 1) :=
        (inverseHerbrandFunctionOfUniqueExtension_eta huniq 1).symm
      _ ≤ t := (inverseHerbrandFunctionOfUniqueExtension_strictMono huniq).monotone hφ
  have hIntegral : t = (⌊t⌋₊ : ℝ) := by
    simpa only [Nat.cast_one] using inverseHerbrandFunctionOfUniqueExtension_nat_eq_natFloor huniq 1
  have hDepth : 1 ≤ ⌊t⌋₊ := by
    rw [hIntegral] at ht
    exact_mod_cast ht
  apply Subgroup.map_le_iff_le_comap.mpr
  apply fieldPrincipalUnits_le_norm_preimage_of_isSeparable K L
  simpa only [Nat.sub_self, mul_zero] using Nat.zero_lt_one.trans_le hDepth

end Congruences

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (H : FiniteAbstractField (Gal(SeparableClosure K/K)))

local notation "F" => finiteFixedField K H

attribute [local instance] finiteFixedFieldFiniteDimensional finiteFixedFieldNormedField
  finiteFixedFieldValuativeRel finiteFixedFieldLocalField
  finiteFixedFieldSeparableClosureAlgebra weilFixedFieldAmbientAlgebra

private theorem subgroup_map_eq_comap_of_commuting_square
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (U : Subgroup A) (norm : A →* B) (left : A →* C) (top : C →* D) (right : B →* D)
    (injective : Function.Injective right)
    (commutes : ∀ y, top (left y) = right (norm y)) (V : Subgroup C)
    (himage : U.map left = V) :
    U.map norm = (V.map top).comap right := by
  have square : top.comp left = right.comp norm := MonoidHom.ext commutes
  rw [← himage, Subgroup.map_map, square, ← Subgroup.map_map,
    Subgroup.comap_map_eq_self_of_injective injective]

private theorem absoluteArtin_injective_for_norm_filtration
    (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] :
    Function.Injective (separableAbsoluteLocalArtinMap M) := by
  intro x y hxy
  exact (localWeilReciprocity M).injective (localWeilAbelianizationToAbsolute_injective M
    ((localWeilAbelianizationToAbsolute_localWeilReciprocity M x).trans
      (hxy.trans (localWeilAbelianizationToAbsolute_localWeilReciprocity M y).symm)))

/-- A norm from the `⌈t⌉₊` principal units is exactly a field unit whose
absolute Artin class comes from the upper field's absolute upper group at `t`. -/
theorem localFixedField_norm_fieldPrincipalUnits_eq_absoluteUpper_preimage
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) (t : ℝ) (ht : 0 ≤ t) :
    let norm := normUnits K F
    let i : localAbsoluteAbelianProfinite F →* localAbsoluteAbelianProfinite K :=
      (TopologicalAbelianization.map (localFixedFieldAbsoluteInclusion K H e)).toMonoidHom
    let baseArtin := (separableAbsoluteLocalArtinMap K).toMonoidHom
    let units := fieldPrincipalUnits F ⌈t⌉₊
    let upper := (separableLocalUpperRamificationGroup F t).map
      (localAbsoluteAbelianizationQuotientMap F)
    units.map norm = (upper.map i).comap baseArtin := by
  intro norm i baseArtin units upper
  let upperArtin := (separableAbsoluteLocalArtinMap F).toMonoidHom
  have hcomm (x : Fˣ) : i (upperArtin x) = baseArtin (norm x) :=
    separableAbsoluteLocalArtinMap_norm_restriction K H e x
  have hfiltration : units.map upperArtin = upper :=
    separableAbsoluteLocalArtinMap_fieldPrincipalUnits F t ht
  have hinj : Function.Injective baseArtin := absoluteArtin_injective_for_norm_filtration K
  let baseGroup : Group Kˣ := inferInstance
  let upperGroup : Group Fˣ := inferInstance
  let baseAbelianGroup : Group (localAbsoluteAbelianProfinite K) := inferInstance
  let upperAbelianGroup : Group (localAbsoluteAbelianProfinite F) := inferInstance
  let h := @subgroup_map_eq_comap_of_commuting_square Fˣ Kˣ
    (localAbsoluteAbelianProfinite F) (localAbsoluteAbelianProfinite K)
    upperGroup baseGroup upperAbelianGroup baseAbelianGroup
    units norm upperArtin i baseArtin hinj hcomm upper hfiltration
  with_reducible exact h

/-- In the Galois case the same norm image at the inverse Herbrand step
uses its exact integral lower depth. -/
theorem localFixedField_norm_fieldPrincipalUnits_at_inverseHerbrand [IsGalois K F]
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) (n : ℕ) :
    let huniq : HasUniqueValuationExtension.{u, u, u, 0, 0}
        (localCompleteDVF K).toDVF (chosenLocalExtensionCompleteDVF K F).toDVF :=
      chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension K F
    let t := inverseHerbrandFunctionOfUniqueExtension huniq (n : ℝ)
    let norm := normUnits K F
    let i : localAbsoluteAbelianProfinite F →* localAbsoluteAbelianProfinite K :=
      (TopologicalAbelianization.map (localFixedFieldAbsoluteInclusion K H e)).toMonoidHom
    let baseArtin := (separableAbsoluteLocalArtinMap K).toMonoidHom
    let upper := (separableLocalUpperRamificationGroup F t).map
      (localAbsoluteAbelianizationQuotientMap F)
    (fieldPrincipalUnits F ⌊t⌋₊).map norm = (upper.map i).comap baseArtin := by
  intro huniq t norm i baseArtin upper
  have hInt : t = (⌊t⌋₊ : ℝ) :=
    inverseHerbrandFunctionOfUniqueExtension_nat_eq_natFloor huniq n
  have ht : 0 ≤ t := hInt.symm ▸ Nat.cast_nonneg _
  have hceil : ⌈t⌉₊ = ⌊t⌋₊ :=
    (congrArg Nat.ceil hInt).trans (Nat.ceil_natCast _)
  have hNorm := localFixedField_norm_fieldPrincipalUnits_eq_absoluteUpper_preimage K H e t ht
  have hDepth := congrArg (fun r : ℕ => (fieldPrincipalUnits F r).map norm) hceil.symm
  with_reducible exact hDepth.trans hNorm

end LocalClassFieldTheory
