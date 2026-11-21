/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalEulerWild
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension

/-! # The Euler characteristic of finite local coefficients -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory Polynomial
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open RamificationTheory.HilbertRamification.ValuationSubring
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer
attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)

private theorem localEulerCoefficient_prime_awayResidue_irreducible
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ ringChar 𝓀[K])
    (E : FiniteGaloisIntermediateField K Ω) (k : Type u) [Field k] [Finite k] [CharP k p]
    (hsplit : Splits ((X : k[X]) ^ Nat.card Gal(E/K) - C 1))
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (ρ : Representation k Gal(E/K) V) [Representation.IsIrreducible ρ] :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E ρ) := by
  let q := ringChar 𝓀[K]
  let Vb := (localCompleteDVF K).valuation.valuationSubring
  let : HenselianRing Vb (IsLocalRing.maximalIdeal Vb) := (localCompleteDVF K).henselianRing
  obtain ⟨W, _, _, _, hW⟩ :=
    open ValuationTheory.DiscreteValuationField.Valuation in
    exists_extension_valuationSubring_with_hasExtension (L := Ω) Vb.valuation
  let : Vb.valuation.HasExtension W.valuation := hW
  let : Fact (Nat.Prime q) := ⟨CharP.prime_ringChar 𝓀[K]⟩
  let : CharP (IsLocalRing.ResidueField Vb) q := ringChar.charP _
  let : CharP (IsLocalRing.ResidueField W) q :=
    charP_of_injective_ringHom
      (ValuationTheory.Valuations.residueFieldMapOfHasExtension Vb W hW).injective q
  let N := ramificationGroupInAut K W
  let r := (finiteGaloisRestriction E).toMonoidHom
  let M := N.map r
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective Ω
  let hN : N.Normal := ramificationGroupInAut_normal_of_henselianRing K Vb W
  let : M.Normal := Subgroup.Normal.map hN r hr
  rcases Representation.noInvariants_or_trivial_of_normal_isIrreducible ρ M with hzero | htriv
  · let A := finiteStageIntegralCoefficient K E ρ
    let b := Module.finBasis k V
    let : Finite A := Finite.of_injective b.equivFun b.equivFun.injective
    have hpA (x : A) : p • x = 0 := by
      let a : V := x
      change p • a = 0
      rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]
    have hfix (x : A) (hx : ∀ g : N, A.ρ g.val x = x) : x = 0 := by
      apply hzero x
      intro g
      obtain ⟨t, ht, h⟩ := g.property
      rw [← h]
      exact hx ⟨t, ht⟩
    exact localEulerCoefficient_wild_noInvariants K W p A Vb hpq hpA
      (finiteStageIntegralCoefficient_actionContinuous K E k ρ) hfix
  · let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
    let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
    let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
    let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
      finiteExtensionSpectralValuation_hasExtension K E
    have hfix (g : N) (x : V) : ρ (r g.val) x = x :=
      htriv ⟨r g.val, ⟨g.val, g.property, rfl⟩⟩ x
    obtain ⟨F, χ, e⟩ :=
      exists_localTameInducedCharacter_of_absoluteWildFixed K E W q k V ρ hfix hsplit
    exact localEulerCoefficient_finiteStageInducedLine K E p k ρ F.fixingSubgroup χ e

private theorem localEulerCoefficient_prime (p : ℕ) [Fact p.Prime]
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K) A := by
  by_cases h : p = ringChar 𝓀[K]
  · exact localEulerCoefficient_prime_residue K p h A hA hp
  refine localEulerCoefficient_prime_of_irreducibleStages K p ?_ A hA hp
  intro E k _ _ _ hs V _ _ _ _ ρ hρ
  let : Representation.IsIrreducible ρ := hρ
  exact localEulerCoefficient_prime_awayResidue_irreducible K p h E k hs V ρ

/-- The local Euler characteristic for every finite discrete coefficient
module with continuous action over a characteristic-zero local field. -/
theorem localEulerCoefficient (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K) A :=
  hasLowDegreeEulerCharacteristic_of_prime_coefficients G (localCoefficientOrderNorm K)
    (localCoefficientOrderNorm_one K) (localCoefficientOrderNorm_mul K)
    (finiteLocalIntegralH3_isZero K) (localEulerCoefficient_prime K) A hA

/-- The cardinal formula on the actual local cohomology groups for all
finite discrete coefficients in mixed characteristic. -/
theorem card_localH1 (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) :
    let v := localIntegerValuation K
    let F := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
    let p := F.residueCharacteristic
    let d := Module.finrank ℚ_[p] K
    Nat.card (continuousCohomology 1 A) = Nat.card (continuousCohomology 0 A) *
      Nat.card (continuousCohomology 2 A) * p ^ (d * padicValNat p (Nat.card A)) :=
  card_localH1_of_eulerCharacteristic K A (localEulerCoefficient K A hA)

end ClassFieldTheory.Brauer
