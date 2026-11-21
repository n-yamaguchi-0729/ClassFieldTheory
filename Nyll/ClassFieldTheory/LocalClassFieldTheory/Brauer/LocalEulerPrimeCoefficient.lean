/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.RingTheory.TensorProduct.Finite
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FiniteStageEulerDevissage
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTameMonomial
public import Nyll.GaloisCohomology.Topology.ContinuousEulerScalarExtension

/-! # Prime-coefficient Euler characteristic by finite scalar extension -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory Polynomial
open scoped TensorProduct ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local notation "Ω" => SeparableClosure K
local notation "Γabs" => Gal(Ω/K)

private theorem localCoefficientOrderNorm_nonneg (m : ℕ) : 0 ≤ localCoefficientOrderNorm K m := by
  unfold localCoefficientOrderNorm
  positivity

/-- Scalar extension acts by the actual tensor extension of the original action. -/
def finiteStageScalarExtension
    (E : FiniteGaloisIntermediateField K Ω) (p : ℕ)
    (k : Type u) [Field k] [Algebra (ZMod p) k]
    {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) Gal(E/K) V) :
    Representation k Gal(E/K) (k ⊗[ZMod p] V) :=
  (Module.End.baseChangeHom (ZMod p) k V).toRingHom.toMonoidHom.comp ρ

private def finiteStageScalarExtensionIso
    (E : FiniteGaloisIntermediateField K Ω) (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Algebra (ZMod p) k] [FiniteDimensional (ZMod p) k]
    {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) Gal(E/K) V) :
    finiteStageIntegralCoefficient K E (finiteStageScalarExtension K E p k ρ) ≅
      repeatedContinuousCoefficient Γabs (Module.finrank (ZMod p) k)
        (finiteStageIntegralCoefficient K E ρ) := by
  let d := Module.finrank (ZMod p) k
  let F := finiteStageIntegralCoefficient K E ρ
  let R := repeatedContinuousCoefficient Γabs d F
  let : DiscreteTopology R := inferInstanceAs (DiscreteTopology (Fin d → F))
  let b := Module.finBasis (ZMod p) k
  let e := TensorProduct.repeatedCoefficientBasisEquiv (M := V) b
  refine discreteIntegralCoefficientIso e.toAddEquiv (fun g x => funext fun i => ?_)
  let f := ρ (finiteGaloisRestriction E g)
  change e (f.baseChange k x) i = f (e x i)
  exact TensorProduct.repeatedCoefficientBasisEquiv_map b f x i

/-- The Euler formula descends from the actual finite tensor extension to
the original coefficient representation. -/
theorem localEulerCoefficient_of_finiteStageScalarExtension
    (E : FiniteGaloisIntermediateField K Ω) (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [Algebra (ZMod p) k] [FiniteDimensional (ZMod p) k]
    {V : Type u} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : Representation (ZMod p) Gal(E/K) V)
    (h : hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E (finiteStageScalarExtension K E p k ρ))) :
    hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K)
      (finiteStageIntegralCoefficient K E ρ) := by
  let d := Module.finrank (ZMod p) k
  let A := finiteStageIntegralCoefficient K E ρ
  let : Finite A := inferInstanceAs (Finite V)
  exact hasLowDegreeEulerCharacteristic_of_repeated Γabs (localCoefficientOrderNorm K)
    (localCoefficientOrderNorm_one K) (localCoefficientOrderNorm_mul K)
    (fun m _ => localCoefficientOrderNorm_nonneg K m) d Module.finrank_pos A
    (hasLowDegreeEulerCharacteristic_of_iso (finiteStageScalarExtensionIso K E p k ρ) h)


/-- A finite splitting extension of the prime field reduces the Euler formula
to the original irreducible actions over finite splitting fields. -/
theorem localEulerCoefficient_prime_of_irreducibleStages (p : ℕ) [Fact p.Prime]
    (hSimple : ∀ (E : FiniteGaloisIntermediateField K Ω) (k : Type u)
      [Field k] [Finite k] [CharP k p], Splits ((X : k[X]) ^ Nat.card Gal(E/K) - C 1) →
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
        (ρ : Representation k Gal(E/K) V), Representation.IsIrreducible ρ →
        hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K)
          (finiteStageIntegralCoefficient K E ρ))
    (A : TopRep.{u} ℤ Γabs) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0) :
    hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K) A := by
  let : Module (ZMod p) A := AddCommGroup.zmodModule hp
  obtain ⟨E, ρ, ⟨e⟩⟩ := exists_finiteStagePrimeCoefficient K p A hA hp
  let P : (ZMod p)[X] := (X : (ZMod p)[X]) ^ Nat.card Gal(E/K) - C 1
  let k₀ := P.SplittingField
  let k := ULift.{u} k₀
  let : CharP k₀ p := charP_of_injective_algebraMap (algebraMap (ZMod p) k₀).injective p
  let : CharP k p := inferInstanceAs (CharP (ULift.{u} k₀) p)
  let j : k ≃ₐ[ZMod p] k₀ := ULift.algEquiv
  let : FiniteDimensional (ZMod p) k := j.symm.toLinearEquiv.finiteDimensional
  let b := Module.finBasis (ZMod p) k
  let : Finite k := Finite.of_injective b.equivFun b.equivFun.injective
  let : FiniteDimensional (ZMod p) A := Module.Finite.of_finite
  have hs₀ : Splits ((X : k₀[X]) ^ Nat.card Gal(E/K) - C 1) :=
    Representation.splits_tameGroupPowerPolynomial (G := Gal(E/K)) (ZMod p)
  have hs : Splits ((X : k[X]) ^ Nat.card Gal(E/K) - C 1) := by
    have h := hs₀.map j.symm.toRingHom
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_one, map_one] using h
  let ρk := finiteStageScalarExtension K E p k ρ
  have hk := finiteStageEuler_of_irreducible K E k (hSimple E k hs) _ ρk
  exact hasLowDegreeEulerCharacteristic_of_iso e
    (localEulerCoefficient_of_finiteStageScalarExtension K E p k ρ hk)

/-- The local Euler characteristic for every finite discrete module killed
by the residue prime of a characteristic-zero local field. -/
theorem localEulerCoefficient_prime_residue (p : ℕ) [Fact p.Prime] (hq : p = ringChar 𝓀[K])
    (A : TopRep.{u} ℤ Γabs) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0) :
    hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K) A := by
  refine localEulerCoefficient_prime_of_irreducibleStages K p ?_ A hA hp
  intro E k _ _ instChar hs V _ _ _ _ ρ hρ
  let : CharP k p := instChar
  let : Representation.IsIrreducible ρ := hρ
  let : NontriviallyNormedField E := finiteExtensionSpectralNormedField K E
  let : ValuativeRel E := finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E := finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  have hqE : p = ringChar 𝓀[E] := hq.trans (Algebra.ringChar_eq 𝓀[K] 𝓀[E])
  let : CharP k (ringChar 𝓀[E]) := hqE ▸ (inferInstance : CharP k p)
  obtain ⟨F, χ, e⟩ := exists_localTameInducedCharacter K E k V ρ hs
  exact @localEulerCoefficient_finiteStageInducedLine K _ _ _ _ _ E p _ k _ _ instChar
    V _ _ ρ F.fixingSubgroup χ e

end ClassFieldTheory.Brauer
