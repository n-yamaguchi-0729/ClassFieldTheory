/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.FiniteField
public import Nyll.GaloisCohomology.GroupTheory.EquivariantPowerReduction
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitRoots
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # Equivariant local power classes and the valuation summand -/

@[expose] public section

open CategoryTheory LocalClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [ValuativeRel K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

local notation "G" => Gal(L/K)

/-- The integral Galois representation on actual valuation-ring units. -/
def localIntegerUnitRep : Rep.{u} ℤ G := by
  let : MulDistribMulAction G 𝒪[L]ˣ :=
    galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  exact Rep.ofMulDistribMulAction G 𝒪[L]ˣ

/-- The trivial representation on the value group of the normalized valuation. -/
abbrev localValueRep : Rep.{u} ℤ G :=
  Rep.of (Representation.trivial ℤ G (ULift.{u} ℤ))

local notation "O" => localIntegerUnitRep K L
local notation "U" => Rep.ofAlgebraAutOnUnits K L
local notation "Z" => localValueRep K L

/-- The original inclusion of valuation-ring units into field units. -/
def localIntegerUnitInclusion : O ⟶ U :=
  Rep.ofHom ⟨(additiveIntegerUnitsToFieldUnits L).toIntLinearMap, fun g => by
    apply LinearMap.ext
    intro a
    exact congrArg Additive.ofMul
      (integerUnitsToFieldUnits_galoisGroup_equivariant K L g (Additive.toMul a))⟩

/-- The original normalized valuation as a morphism of Galois representations. -/
def localUnitValuation : U ⟶ Z :=
  Rep.ofHom
    ⟨(ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).symm.toLinearMap.comp
      (valuationMap L).toIntLinearMap, fun g => by
      apply LinearMap.ext
      intro x
      exact congrArg ULift.up (valuationMap_unitsMapEquiv_galoisGroup K L g (Additive.toMul x))⟩

/-- Inclusion of the original integer-unit power classes into the field power classes. -/
def localIntegerUnitPowerClassInclusion (n : ℕ) :
    Rep.powerReduction O n ⟶ Rep.powerReduction U n :=
  Rep.powerReductionHom n (localIntegerUnitInclusion K L)

/-- The normalized valuation on the actual field power classes. -/
def localPowerClassValuation (n : ℕ) : Rep.powerReduction U n ⟶ Rep.powerReduction Z n :=
  Rep.powerReductionHom n (localUnitValuation K L)

/-- The original normalized valuation has kernel the actual integer units. -/
theorem localUnitValuation_exact :
    Function.Injective (localIntegerUnitInclusion K L) ∧
      Function.Exact (localIntegerUnitInclusion K L) (localUnitValuation K L) ∧
      Function.Surjective (localUnitValuation K L) := by
  let i := (localIntegerUnitInclusion K L).hom.toLinearMap
  let q := (localUnitValuation K L).hom.toLinearMap
  have hi : Function.Injective i := by
    intro x y hxy
    exact Additive.toMul.injective (integerUnitsToFieldUnits_injective L
      (congrArg Additive.toMul hxy))
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨x, hx⟩ := valuationMap_surjective L (show ULift.{u} ℤ from z).down
    exact ⟨x, ULift.ext hx⟩
  have hex : Function.Exact i q := by
    intro x
    change (ULift.up (valuationMap L x) : ULift.{u} ℤ) = 0 ↔
      ∃ a : Additive 𝒪[L]ˣ, additiveIntegerUnitsToFieldUnits L a = x
    rw [show (ULift.up (valuationMap L x) : ULift.{u} ℤ) = 0 ↔ valuationMap L x = 0 from
      ⟨congrArg ULift.down, ULift.ext⟩]
    exact (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L x.toMul).symm
  exact ⟨hi, hex, hq⟩

omit [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L] in
/-- Multiplication by a positive integer is injective on the value group. -/
theorem localValue_nsmul_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (LinearMap.nsmulLinear (R := ℤ) n Z) := by
  intro x y hxy
  apply ULift.ext
  have h := congrArg ULift.down hxy
  change n • (show ULift.{u} ℤ from x).down = n • (show ULift.{u} ℤ from y).down at h
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn.ne') h

/-- The valuation sequence remains short exact on the actual power quotients. -/
theorem localPowerClassValuation_exact (n : ℕ) (hn : 0 < n) :
    Function.Injective (localIntegerUnitPowerClassInclusion K L n) ∧
      Function.Exact (localIntegerUnitPowerClassInclusion K L n) (localPowerClassValuation K L n) ∧
      Function.Surjective (localPowerClassValuation K L n) := by
  let i := (localIntegerUnitInclusion K L).hom.toLinearMap
  let q := (localUnitValuation K L).hom.toLinearMap
  obtain ⟨hi, hex, hq⟩ := localUnitValuation_exact K L
  exact ⟨LinearMap.powerReductionMap_injective_of_quotient n i q hi hq hex
      (localValue_nsmul_injective K L n hn),
    LinearMap.powerReduction_exact n i q hq hex,
    LinearMap.powerReductionMap_surjective n q hq⟩

section Residue

variable [Fintype 𝓀[L]] (n : ℕ+) (hn : (n : ℕ) ∣ Fintype.card 𝓀[L] - 1)

/-- Integer-unit power classes away from the residue characteristic are detected
by the actual finite-field residue power symbol. -/
def integerUnitResiduePowerSymbol : 𝒪[L]ˣ →* rootsOfUnity (n : ℕ) 𝓀[L] :=
  (finiteFieldPowerResidueSymbol 𝓀[L] n hn).comp (integerUnitsToResidueUnits L)

theorem integerUnitResiduePowerSymbol_eq_one_iff [NeZero ((n : ℕ) : 𝓀[L])] (u : 𝒪[L]ˣ) :
    integerUnitResiduePowerSymbol L n hn u = 1 ↔ ∃ a : 𝒪[L]ˣ, a ^ (n : ℕ) = u := by
  let z : 𝓀[L]ˣ := integerUnitsToResidueUnits L u
  have hz : integerUnitResiduePowerSymbol L n hn u = 1 ↔
      ∃ a : 𝓀[L]ˣ, a ^ (n : ℕ) = z :=
    finiteFieldPowerResidueSymbol_eq_one_iff 𝓀[L] n hn z
  refine hz.trans ?_
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := integerUnitsToResidueUnits_surjective L a
    have hprincipal : u / b ^ (n : ℕ) ∈ principalUnits L 1 := by
      apply (integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one L _).mp
      let f := integerUnitsToResidueUnits L
      have hbpow : f (b ^ (n : ℕ)) = f u :=
        (map_pow f b (n : ℕ)).trans ((congrArg (fun t : 𝓀[L]ˣ => t ^ (n : ℕ)) hb).trans ha)
      exact (map_div f u (b ^ (n : ℕ))).trans (div_eq_one.mpr hbpow.symm)
    have hunit : IsUnit ((n : ℕ) : 𝒪[L]) :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by
        rw [map_natCast]
        exact NeZero.ne ((n : ℕ) : 𝓀[L]))
    obtain ⟨w, _, hw⟩ := exists_principalUnit_pow_eq_of_isUnit_natCast L n hunit le_rfl hprincipal
    exact ⟨w * b, (mul_pow w b (n : ℕ)).trans (by rw [hw, div_mul_cancel])⟩
  · rintro ⟨a, rfl⟩
    exact ⟨integerUnitsToResidueUnits L a, (map_pow _ _ _).symm⟩

/-- Every finite-field root is realized by the residue power symbol. -/
theorem residueSymbol_surjective :
    Function.Surjective (finiteFieldPowerResidueSymbol 𝓀[L] n hn) := by
  classical
  let f := finiteFieldPowerResidueSymbol 𝓀[L] n hn
  have hk : f.ker = (powMonoidHom (n : ℕ) : 𝓀[L]ˣ →* 𝓀[L]ˣ).range := by
    ext a
    exact finiteFieldPowerResidueSymbol_eq_one_iff 𝓀[L] n hn a
  have hκ : Nat.card 𝓀[L]ˣ = Fintype.card 𝓀[L] - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hcard : Nat.card f.range = (n : ℕ) := by
    rw [← Subgroup.index_ker, hk, IsCyclic.index_powMonoidHom_range, hκ, Nat.gcd_eq_right hn]
  have hroots : Nat.card (rootsOfUnity (n : ℕ) 𝓀[L]) = (n : ℕ) := by
    rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, hκ, Nat.gcd_eq_right hn]
  have hf : f.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hroots, hcard]
  intro z
  have hz : z ∈ f.range := by
    rw [hf]
    exact Subgroup.mem_top z
  exact MonoidHom.mem_range.mp hz

/-- The actual residue power symbol induces an equivalence on the integer-unit quotient. -/
def integerUnitPowerClassesResidueEquiv [NeZero ((n : ℕ) : 𝓀[L])] :
    (𝒪[L]ˣ ⧸ (powMonoidHom (n : ℕ) : 𝒪[L]ˣ →* 𝒪[L]ˣ).range) ≃*
      rootsOfUnity (n : ℕ) 𝓀[L] := by
  let f := integerUnitResiduePowerSymbol L n hn
  have hk : (powMonoidHom (n : ℕ) : 𝒪[L]ˣ →* 𝒪[L]ˣ).range = f.ker := by
    ext u
    exact (integerUnitResiduePowerSymbol_eq_one_iff L n hn u).symm
  have hf : Function.Surjective f :=
    (residueSymbol_surjective L n hn).comp (integerUnitsToResidueUnits_surjective L)
  exact (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- The finite-field root assigned to an integer unit commutes with conjugation. -/
theorem integerUnitResiduePowerSymbol_galois (g : G) (u : 𝒪[L]ˣ) :
    integerUnitResiduePowerSymbol L n hn
        (Units.mapEquiv (galoisGroupIntegerRingEquivOfIsIntegralClosure K L g).toMulEquiv u) =
      restrictRootsOfUnity
        (galoisGroupResidueFieldEquivOfIsIntegralClosure K L g).toRingHom (n : ℕ)
        (integerUnitResiduePowerSymbol L n hn u) := by
  apply Subtype.ext
  let σ := (galoisGroupResidueFieldEquivOfIsIntegralClosure K L g).toMulEquiv
  let τ := (galoisGroupIntegerRingEquivOfIsIntegralClosure K L g).toMulEquiv
  let j := (Fintype.card 𝓀[L] - 1) / (n : ℕ)
  change integerUnitsToResidueUnits L (Units.mapEquiv τ u) ^ j =
    Units.mapEquiv σ (integerUnitsToResidueUnits L u ^ j)
  exact (congrArg (fun t : 𝓀[L]ˣ => t ^ j)
    (galoisGroupResidueFieldEquivOfIsIntegralClosure_integerUnitsToResidueUnits K L g u)).trans
      ((map_pow (Units.mapEquiv σ) (integerUnitsToResidueUnits L u) j).symm)

end Residue

end ClassFieldTheory.Brauer
