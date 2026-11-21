/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.GaloisPrincipalUnitLog
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.NormalBasisPowerClasses
public import Nyll.ClassFieldTheory.Algebra.LocalField.PrincipalUnitTopology

/-! # Normal-basis lattices in the mixed-characteristic principal units -/

@[expose] public section

open LocalFieldTheory LocalClassFieldTheory CyclicCohomology
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

local notation "M" => chosenNormalBasisIntegerLattice K L

/-- A sufficiently small Galois-invariant dilation puts the integral
normal-basis lattice in the actual power of the maximal ideal. -/
theorem exists_normalBasisLattice_maximalIdealPow_finite_quotient (r : ℕ) :
    ∃ f : M →ₗ[𝒪[K]] (𝓂[L] ^ r : Ideal 𝒪[L]),
      Function.Injective f ∧ Finite ((𝓂[L] ^ r : Ideal 𝒪[L]) ⧸ LinearMap.range f) ∧
      ∀ (σ : Gal(L/K)) (x : M),
        (f (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x) : 𝒪[L]) =
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (f x) := by
  let p := ringChar 𝓀[L]
  let b : 𝒪[L] := (p : 𝒪[L]) ^ r
  let I : Ideal 𝒪[L] := 𝓂[L] ^ r
  have hp : p ≠ 0 := CharP.ringChar_ne_zero_of_finite 𝓀[L]
  have hb : (b : L) ≠ 0 := by
    change ((p : L) ^ r) ≠ 0
    exact pow_ne_zero r (Nat.cast_ne_zero.mpr hp)
  have hbI : b ∈ I := by
    apply Ideal.pow_mem_pow
    apply (IsLocalRing.residue_eq_zero_iff (p : 𝒪[L])).mp
    rw [map_natCast]
    exact ringChar.Nat.cast_ringChar (R := 𝓀[L])
  obtain ⟨g, hg, hgopen, hgal⟩ := exists_normalBasisLattice_integerRing_open_range K L
  let f : M →ₗ[𝒪[K]] I :=
    { toFun := fun x => ⟨b * g x, Ideal.mul_mem_right (g x) I hbI⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        change b * g (x + y) = b * g x + b * g y
        rw [map_add, mul_add]
      map_smul' := by
        intro a x
        apply Subtype.ext
        change b * g (a • x) = a • (b * g x)
        rw [map_smul, Algebra.smul_def, Algebra.smul_def, mul_left_comm] }
  have hf : Function.Injective f := by
    intro x y hxy
    apply hg
    apply Subtype.ext
    apply mul_left_cancel₀ hb
    exact congrArg (fun z : I => ((z : 𝒪[L]) : L)) hxy
  have hopenO : IsOpen (𝒪[L] : Set L) := (ValuativeRel.valuation L).isOpen_integer
  let bg : L → L := fun x => (b : L) * x
  have hopen : IsOpen (Set.range f) := by
    have heq : Set.range f = (fun z : I => ((z : 𝒪[L]) : L)) ⁻¹'
        (bg '' ((Subtype.val : 𝒪[L] → L) '' Set.range g)) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨(g x : L), ⟨g x, ⟨x, rfl⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, hx⟩
        exact ⟨x, Subtype.ext (Subtype.ext hx)⟩
    rw [heq]
    exact ((isOpenMap_smul₀ hb) _ (hopenO.isOpenMap_subtype_val _ hgopen)).preimage
      (continuous_subtype_val.comp continuous_subtype_val)
  let : T2Space L := localFieldT2Space L
  have hI : IsOpen (I : Set 𝒪[L]) := IsLocalRing.isOpen_maximalIdeal_pow 𝒪[L] r
  let : CompactSpace I := isCompact_iff_compactSpace.mp
    ((I.toAddSubgroup.isClosed_of_isOpen hI).isCompact)
  refine ⟨f, hf, AddSubgroup.quotient_finite_of_isOpen (LinearMap.range f).toAddSubgroup hopen, ?_⟩
  intro σ x
  change b * g (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x) =
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (b * g x)
  rw [hgal, map_mul, show galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ b = b by
    simp only [b, map_pow, map_natCast]]

/-- Through the actual local logarithm, the normal-basis lattice embeds with
finite index in the deep principal units and retains their Galois action. -/
theorem exists_normalBasisLattice_principalUnits_finite_quotient (r : ℕ)
    (hr : localLogExpThreshold L < (r : ℚ)) :
    ∃ f : M →ₗ[ℤ] Additive (principalUnits L r),
      Function.Injective f ∧ Finite (Additive (principalUnits L r) ⧸ LinearMap.range f) ∧
      ∀ (σ : Gal(L/K)) (x : M),
        (f (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x)).toMul =
          galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L r σ (f x).toMul := by
  obtain ⟨g, hg, hIg, hgal⟩ := exists_normalBasisLattice_maximalIdealPow_finite_quotient K L r
  let I := (𝓂[L] ^ r : Ideal 𝒪[L])
  let e : Additive (principalUnits L r) ≃ₗ[ℤ] I :=
    (integerPrincipalUnitsLogEquiv L r hr).toIntLinearEquiv
  let g₀ : M →ₗ[ℤ] I := g.restrictScalars ℤ
  let f : M →ₗ[ℤ] Additive (principalUnits L r) := e.symm.toLinearMap.comp g₀
  have hmap : (LinearMap.range g₀).map e.symm.toLinearMap = LinearMap.range f := by
    rw [LinearMap.range_comp]
  let eQ := Submodule.Quotient.equiv (LinearMap.range g₀) (LinearMap.range f) e.symm hmap
  let : Finite (I ⧸ LinearMap.range g₀) := hIg
  refine ⟨f, e.symm.injective.comp hg, Finite.of_surjective eQ eQ.surjective, ?_⟩
  intro σ x
  apply Additive.ofMul.injective
  apply e.injective
  apply Subtype.ext
  change ((e (f (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x))) : 𝒪[L]) =
    (integerPrincipalUnitsLogEquiv L r hr
      (Additive.ofMul
        (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L r σ (f x).toMul)) : 𝒪[L])
  rw [integerPrincipalUnitsLogEquiv_galois]
  change ((e (e.symm (g (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x)))) : 𝒪[L]) =
    galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ ((e (e.symm (g x))) : 𝒪[L])
  rw [e.apply_symm_apply, e.apply_symm_apply]
  exact hgal σ x

/-- The same normal-basis embedding has finite index in the actual integer
unit group. The remaining index is the finite principal-unit quotient. -/
theorem exists_normalBasisLattice_integerUnits_finite_quotient :
    ∃ f : M →ₗ[ℤ] Additive 𝒪[L]ˣ,
      Function.Injective f ∧ Finite (Additive 𝒪[L]ˣ ⧸ LinearMap.range f) ∧
      ∀ (σ : Gal(L/K)) (x : M),
        (f (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x)).toMul =
          Units.mapEquiv (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv
            (f x).toMul := by
  obtain ⟨r, hr⟩ := exists_nat_gt (localLogExpThreshold L)
  obtain ⟨g, hg, hQ, hgal⟩ := exists_normalBasisLattice_principalUnits_finite_quotient K L r hr
  let P := principalUnits L r
  let j := P.subtype.toAdditive.toIntLinearMap
  let f := j.comp g
  have hj : Function.Injective j := fun x y h => Additive.toMul.injective (Subtype.ext h)
  let W := LinearMap.range g
  have hW : W.toAddSubgroup.index ≠ 0 := W.toAddSubgroup.index_ne_zero_iff_finite.mpr hQ
  let : T2Space L := localFieldT2Space L
  let : CompactSpace 𝒪[L]ˣ := inferInstanceAs (CompactSpace (localUnits_profinite L))
  have hP : P.index ≠ 0 := P.index_ne_zero_iff_finite.mpr
    (Subgroup.quotient_finite_of_isOpen P (isOpen_principalUnits L r))
  have hR : j.toAddMonoidHom.range = P.toAddSubgroup := by
    change (MonoidHom.toAdditive P.subtype).range = _
    rw [MonoidHom.coe_toAdditive_range, P.range_subtype]
  have hW' : (LinearMap.range f).toAddSubgroup.index ≠ 0 := by
    change (LinearMap.range (j.comp g)).toAddSubgroup.index ≠ 0
    rw [LinearMap.range_comp, Submodule.map_toAddSubgroup]
    change (W.toAddSubgroup.map j.toAddMonoidHom).index ≠ 0
    have hidx := W.toAddSubgroup.index_map_of_injective
      (f := j.toAddMonoidHom) (show Function.Injective j.toAddMonoidHom from hj)
    rw [hidx, hR, Subgroup.index_toAddSubgroup]
    exact mul_ne_zero hW hP
  refine ⟨f, hj.comp hg, (LinearMap.range f).toAddSubgroup.index_ne_zero_iff_finite.mp hW', ?_⟩
  intro σ x
  exact (congrArg Subtype.val (hgal σ x)).trans
    (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure_apply K L r σ (g x).toMul)

end ClassFieldTheory.Brauer
