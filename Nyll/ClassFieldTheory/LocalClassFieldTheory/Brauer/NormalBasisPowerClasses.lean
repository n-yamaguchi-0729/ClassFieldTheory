/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis
public import Nyll.GaloisCohomology.GroupTheory.EquivariantPowerReduction
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.DeepPrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.IntegralLattice
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import Mathlib.LinearAlgebra.Quotient.Pi

/-! # The regular action on the power reduction of the chosen normal-basis lattice -/

@[expose] public section

open LocalFieldTheory LocalClassFieldTheory CyclicCohomology
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "G" => Gal(L/K)
local notation "M" => chosenNormalBasisIntegerLattice K L
local notation "N[" n "," X "]" => LinearMap.nsmulLinear (R := ℤ) n X
local notation "PowQuot[" n "," X "]" => X ⧸ LinearMap.range (N[n,X])

/-- The normal-basis coordinates carry the power subgroup to the coordinatewise power subgroup. -/
theorem normalBasisPowerCoordinates_map_range (n : ℕ) :
    (LinearMap.range (N[n,M])).map
        ((chosenNormalBasisIntegerLatticeBasis K L).equivFun.restrictScalars ℤ).toLinearMap =
      Submodule.pi Set.univ (fun _ : G => LinearMap.range (N[n,𝒪[K]])) := by
  let e := (chosenNormalBasisIntegerLatticeBasis K L).equivFun.restrictScalars ℤ
  ext f
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    apply Submodule.mem_pi.mpr
    intro g _
    refine ⟨e y g, ?_⟩
    change (n • e y) g = e (n • y) g
    rw [map_nsmul]
  · intro hf
    have hfun (g : G) : ∃ z : 𝒪[K], n • z = f g :=
      (Submodule.mem_pi.mp hf) g (Set.mem_univ g)
    choose c hc using hfun
    refine ⟨n • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
    change e (n • e.symm c) = f
    rw [map_nsmul, e.apply_symm_apply]
    exact funext hc

/-- The integral normal-basis orbit identifies its reduction with one
copy of the reduced base integer ring for each element of the Galois group. -/
def normalBasisPowerCoordinates (n : ℕ) :
    PowQuot[n,M] ≃ₗ[ℤ] (G → PowQuot[n,𝒪[K]]) := by
  classical
  let e := (chosenNormalBasisIntegerLatticeBasis K L).equivFun.restrictScalars ℤ
  let W := LinearMap.range (N[n,M])
  let V := fun _ : G => LinearMap.range (N[n,𝒪[K]])
  exact (Submodule.Quotient.equiv W (Submodule.pi Set.univ V) e
    (normalBasisPowerCoordinates_map_range K L n)).trans (Submodule.quotientPi V)

theorem normalBasisPowerCoordinates_mkQ (n : ℕ) (x : M) (g : G) :
    normalBasisPowerCoordinates K L n ((LinearMap.range (N[n,M])).mkQ x) g =
      (LinearMap.range (N[n,𝒪[K]])).mkQ ((chosenNormalBasisIntegerLatticeBasis K L).equivFun x g) :=
  rfl

/-- The original finite-field Galois action becomes left translation on
the normal-basis reduction. -/
theorem normalBasisPowerCoordinates_galois (n : ℕ) (σ g : G) (x : PowQuot[n,M]) :
    normalBasisPowerCoordinates K L n
      (LinearMap.powerReductionMap n
        (LinearEquiv.toLinearMap
          ((galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ).restrictScalars ℤ))
        x) g =
      normalBasisPowerCoordinates K L n x (σ⁻¹ * g) := by
  obtain ⟨y, rfl⟩ := (LinearMap.range (N[n,M])).mkQ_surjective x
  rw [LinearMap.powerReductionMap_mkQ, normalBasisPowerCoordinates_mkQ,
    normalBasisPowerCoordinates_mkQ]
  exact congrArg (fun z : 𝒪[K] => (LinearMap.range (N[n,𝒪[K]])).mkQ z)
    (chosenNormalBasisIntegerLatticeBasis_equivFun_galoisGroup K L σ g y)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]

/-- The actual normal-basis lattice has a Galois-equivariant open
embedding in the valuation integer ring. The embedding is a base uniformizer dilate. -/
theorem exists_normalBasisLattice_integerRing_open_range :
    ∃ f : M →ₗ[𝒪[K]] 𝒪[L], Function.Injective f ∧ IsOpen (Set.range f) ∧
      ∀ (σ : G) (x : M), f (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x) =
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (f x) := by
  obtain ⟨a, ha⟩ :=
    exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmodule K L
  obtain ⟨b, hb⟩ :=
    exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zero K L
  let n := max a b
  let T := chosenBaseUniformizerPowSubmodule K L n M
  have hT : T ≤ integerRingFieldSubmodule K L :=
    (chosenBaseUniformizerPowSubmodule_antitone K L M (le_max_left a b)).trans ha
  have hTopen : IsOpen (T : Set L) :=
    submodule_isOpen_of_mem_nhds_zero K L (hb n (le_max_right a b))
  let e : M ≃ₗ[𝒪[K]] T := chosenNormalBasisIntegerLatticeMulPowLinearEquiv K L n
  let f : M →ₗ[𝒪[K]] 𝒪[L] :=
    { toFun := fun x => ⟨(e x : L), hT (e x).property⟩
      map_add' := fun x y => Subtype.ext (congrArg (fun t : T => (t : L)) (map_add e x y))
      map_smul' := fun a x =>
        Subtype.ext (congrArg (fun t : T => (t : L)) (map_smul e a x)) }
  have hf : Function.Injective f := fun x y hxy =>
    e.injective (Subtype.ext (congrArg (fun t : 𝒪[L] => (t : L)) hxy))
  let W := LinearMap.range f
  have hW : (W : Set 𝒪[L]) = (Subtype.val : 𝒪[L] → L) ⁻¹' (T : Set L) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).property
    · intro hy
      obtain ⟨x, hx⟩ := e.surjective ⟨(y : L), hy⟩
      exact ⟨x, Subtype.ext (congrArg (fun t : T => (t : L)) hx)⟩
  have hopen : IsOpen (W : Set 𝒪[L]) := by
    rw [hW]
    exact hTopen.preimage continuous_subtype_val
  refine ⟨f, hf, hopen, ?_⟩
  intro σ x
  apply Subtype.ext
  change ((e (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x) : T) : L) =
    σ ((e x : T) : L)
  exact chosenNormalBasisIntegerLatticeMulPowLinearEquiv_galoisGroup_apply_coe K L n σ x

/-- The integral normal-basis embedding has finite additive index. -/
theorem exists_normalBasisLattice_integerRing_finite_quotient :
    ∃ f : M →ₗ[𝒪[K]] 𝒪[L], Function.Injective f ∧ Finite (𝒪[L] ⧸ LinearMap.range f) ∧
      ∀ (σ : G) (x : M), f (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L σ x) =
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (f x) := by
  obtain ⟨f, hf, hopen, hgal⟩ := exists_normalBasisLattice_integerRing_open_range K L
  exact ⟨f, hf, AddSubgroup.quotient_finite_of_isOpen (LinearMap.range f).toAddSubgroup hopen, hgal⟩

end ClassFieldTheory.Brauer

namespace ClassFieldTheory.Brauer

open LocalFieldTheory.DiscreteValuationField

universe w

variable (K : Type w) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

/-- The actual base integer ring modulo a nonzero integer has the coordinate
cardinality obtained from its mixed-characteristic integral basis. -/
theorem card_baseIntegerRingPowerQuotient (n : ℕ) (hn : n ≠ 0) :
    let v := localIntegerValuation K
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
    Nat.card (𝒪[K] ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ) n 𝒪[K])) =
      (F.residueCharacteristic ^ padicValNat F.residueCharacteristic n) ^
        Module.finrank ℚ_[F.residueCharacteristic] K := by
  let v := localIntegerValuation K
  let F := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
  let p := F.residueCharacteristic
  let d := Module.finrank ℚ_[p] K
  let e₀ := (localIntegerValuationSubringEquiv K).symm.toAddEquiv
  let e₁ := F.mixed_valuationSubringLinearEquivPi.toAddEquiv
  let e : 𝒪[K] ≃+ (Fin d → ℤ_[p]) := e₀.trans e₁
  let W := LocalFieldTheory.nsmulAddSubgroup 𝒪[K] n
  let V := LocalFieldTheory.nsmulAddSubgroup (Fin d → ℤ_[p]) n
  have hWV : W.map e.toAddMonoidHom = V := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨e z, (map_nsmul e n z).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨n • e.symm z, ⟨e.symm z, rfl⟩, ?_⟩
      change e (n • e.symm z) = n • z
      rw [map_nsmul, e.apply_symm_apply]
  let R := QuotientAddGroup.congr W V e hWV
  let P := padicIntPiNsmulQuotientEquiv (p := p) (ι := Fin d) n hn
  change Nat.card (𝒪[K] ⧸ W) = (p ^ padicValNat p n) ^ d
  rw [Nat.card_congr (R.trans P).toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

end ClassFieldTheory.Brauer
