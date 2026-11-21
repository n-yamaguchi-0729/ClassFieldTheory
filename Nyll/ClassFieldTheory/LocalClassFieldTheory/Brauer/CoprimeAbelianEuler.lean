/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeEulerH1Length
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeEulerRootsTerm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeScalarStage
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeValueTerm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FiniteCoefficientEuler

/-! # Euler characteristic at an actual coprime abelian Galois stage -/

@[expose] public section

open CategoryTheory ContinuousCohomology LocalFieldTheory TopRep
open LocalFieldTheory.DiscreteValuationField
open scoped IsMulCommutative Ring ValuativeRel MonoidAlgebra

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [CharZero E]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    [hIntegerClosure : @IsIntegralClosure 𝒪[E] 𝒪[K] E _ _ _ (Algebra.ofSubsemiring 𝒪[K]) _]
    [Module.Finite 𝒪[K] 𝒪[E]]
    (p : ℕ) [Fact p.Prime]

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Q" => Gal(E/K)
local notation "GroupAlgebra" => localGaloisGroupAlgebraFunctor K E
local notation "ML" => ModuleCat.carrier (Functor.obj GroupAlgebra (normalBasisLatticeRep K E))
local notation "UL" => ModuleCat.carrier (Functor.obj GroupAlgebra (localIntegerUnitRep K E))
local notation "VL" => ModuleCat.carrier (Functor.obj GroupAlgebra (localValueRep K E))
local notation "T" => LinearMap.ker (LinearMap.nsmulLinear (R := ℤ[Q]) p UL)
local notation "P[" X "]" => X ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ[Q]) p X)
local notation "primeIndex" => (Subtype.mk p (Nat.Prime.pos (Fact.out : p.Prime)) : ℕ+)

private theorem card_eq_prime_pow_valuation_of_module (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [Finite A] :
    Nat.card A = p ^ padicValNat p (Nat.card A) := by
  let : Module.Finite (ZMod p) A := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := A)
  rw [Nat.card_zmod] at h
  exact h.trans (by rw [h, Nat.padicValNat_def, Nat.multiplicity_prime_pow])

private theorem card_eq_prime_pow_valuation (p : ℕ) [Fact p.Prime]
    (A : Type*) [AddCommGroup A] [Finite A] (hA : ∀ a : A, p • a = 0) :
    Nat.card A = p ^ padicValNat p (Nat.card A) :=
  @card_eq_prime_pow_valuation_of_module p _ A _ (AddCommGroup.zmodModule hA) _

attribute [local instance] canonicalSeparableClosureAlgebra

variable [IsMulCommutative Gal(E/K)]
    (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [Finite A] [DiscreteTopology A]
    (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ (h : ↥(stageOpenFixingSubgroup K E.toIntermediateField).toSubgroup) (a : A),
      A.ρ (h : Gal(SeparableClosure K/K)) a = a)
    (j : SeparableClosure K ≃ₐ[E] SeparableClosure E)

private theorem cardinal_from_prime_valuations (p a c₀ c₁ c₂ d : ℕ)
    (ha : a = p ^ padicValNat p a) (h₀ : c₀ = p ^ padicValNat p c₀)
    (h₁ : c₁ = p ^ padicValNat p c₁) (h₂ : c₂ = p ^ padicValNat p c₂)
    (h : padicValNat p c₁ = d * padicValNat p a + padicValNat p c₀ + padicValNat p c₂) :
    c₁ = c₀ * c₂ * a ^ d := by
  calc
    c₁ = p ^ padicValNat p c₁ := h₁
    _ = (p ^ padicValNat p a) ^ d * p ^ padicValNat p c₀ * p ^ padicValNat p c₂ := by
      rw [h, pow_add, pow_add, ← pow_mul, Nat.mul_comm d]
    _ = c₀ * c₂ * a ^ d := by
      rw [← ha, ← h₀, ← h₂]
      ac_rfl

private theorem nat_eq_of_int_eq_sum {n a b c : ℕ}
    (h : (n : ℤ) = (a : ℤ) + (b : ℤ) + (c : ℤ)) : n = a + b + c := by
  exact_mod_cast h

include ζ hζ hfix j in
private theorem localH1_valuation_of_coprimeAbelianStage (hA : ∀ a : A, p • a = 0)
    (hAc : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2))
    (hdeg : ¬p ∣ Module.finrank K E) :
    let v := localIntegerValuation K
    let L := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[L.residueCharacteristic] K * padicValNat L.residueCharacteristic p
    padicValNat p (Nat.card (continuousCohomology 1 A)) =
      d * padicValNat p (Nat.card A) +
        padicValNat p (Nat.card (continuousCohomology 0 A)) +
        padicValNat p (Nat.card (continuousCohomology 2 A)) := by
  intro v L d
  let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
  let hp : p.Prime := Fact.out
  let : Finite T := integerUnitPowerTorsion_finite K E p hp.ne_zero
  let : Finite (P[ML]) := normalBasisLatticePowerQuotient_finite K E p hp.ne_zero
  let : Finite (P[VL]) := valueGroupPowerQuotient_finite K E p hp.pos
  obtain ⟨m, e, he, hproj, hlen⟩ :=
    exists_coprimeStageH1_projectorLength K E p A ζ hζ hfix j hA hdeg
  let D := coprimeStageDualRep K E p ζ hζ A hfix
  let V := ModuleCat.carrier (Functor.obj GroupAlgebra D)
  let Mu := separableMuTopRep K p
  let : Finite Mu :=
    separableMuTopRep_finite K primeIndex (Nat.cast_ne_zero.mpr hp.ne_zero)
  let : Finite D := discreteLinearDual_finite A Mu
  have hD (f : D) : p • f = 0 := by
    let f' : discreteLinearDual A Mu := f
    exact separableMu_dual_nsmul_eq_zero K primeIndex A f'
  have hM : Nat.card (V →ₗ[ℤ[Q]] P[ML]) = (Nat.card A) ^ d :=
    (card_normalBasisPowerHom K E p D hD).trans
      (congrArg (fun k : ℕ => k ^ d)
        (separableMu_dual_card K primeIndex (Nat.cast_ne_zero.mpr hp.ne_zero) A hA))
  have hT : Nat.card (V →ₗ[ℤ[Q]] T) = Nat.card (continuousCohomology 0 A) :=
    coprimeStageEulerRootsHom_card K E p ζ hζ A hfix (Nat.cast_ne_zero.mpr hp.ne_zero) hA
  have hZ : Nat.card (V →ₗ[ℤ[Q]] P[VL]) = Nat.card (continuousCohomology 2 A) :=
    coprimeStageEulerValueHom_card K E p A ζ hζ hfix hdeg hA hAc
  let valuation (n : ℕ) : ℤ := padicValNat p n
  have hmLen : MonoidAlgebra.primeProjectorLength Q e he hp (ModuleCat.of ℤ[Q] (P[ML])) =
      valuation (Nat.card A ^ d) :=
    congrArg valuation
      ((hproj (ModuleCat.of ℤ[Q] (P[ML])) (LinearMap.nsmul_powerQuotient_eq_zero p)).symm.trans hM)
  have htLen : MonoidAlgebra.primeProjectorLength Q e he hp (ModuleCat.of ℤ[Q] T) =
      valuation (Nat.card (continuousCohomology 0 A)) :=
    congrArg valuation
      ((hproj (ModuleCat.of ℤ[Q] T) (fun x => Subtype.ext x.property)).symm.trans hT)
  have hzLen : MonoidAlgebra.primeProjectorLength Q e he hp (ModuleCat.of ℤ[Q] (P[VL])) =
      valuation (Nat.card (continuousCohomology 2 A)) :=
    congrArg valuation
      ((hproj (ModuleCat.of ℤ[Q] (P[VL])) (LinearMap.nsmul_powerQuotient_eq_zero p)).symm.trans hZ)
  have hpow : padicValNat p (Nat.card (continuousCohomology 1 A)) =
      padicValNat p (Nat.card A ^ d) + padicValNat p (Nat.card (continuousCohomology 0 A)) +
        padicValNat p (Nat.card (continuousCohomology 2 A)) :=
    nat_eq_of_int_eq_sum (hlen.trans (congrArg₂ (· + ·) (congrArg₂ (· + ·) hmLen htLen) hzLen))
  simpa only [Nat.padicValNat_def, Nat.multiplicity_pow] using hpow

omit [IsMulCommutative Gal(E/K)] in
private theorem localH_card_eq_prime_pow_valuation (hA : ∀ a : A, p • a = 0)
    (hAc : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2)) (i : ℕ) (hi : i < 3) :
    Nat.card (continuousCohomology i A) =
      p ^ padicValNat p (Nat.card (continuousCohomology i A)) := by
  let : Finite (continuousCohomology i A) := finite_localIntegralCohomology_lt_three K A hAc i hi
  exact card_eq_prime_pow_valuation p _
    (nsmul_continuousCohomology_eq_zero_of_coefficients A p hA i)

include ζ hζ hfix j in
/-- The actual degree-one cardinal gives the local Euler formula for a
prime coefficient trivialized by a coprime finite abelian Galois stage
containing its roots of unity. -/
theorem card_localH1_of_coprimeAbelianStage (hA : ∀ a : A, p • a = 0)
    (hAc : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2))
    (hdeg : ¬p ∣ Module.finrank K E) :
    let v := localIntegerValuation K
    let L := LocalField.ofWithZeroValuation v
    letI : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
    Nat.card (continuousCohomology 1 A) =
      Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
        Nat.card A ^ (Module.finrank ℚ_[L.residueCharacteristic] K *
          padicValNat L.residueCharacteristic p) := by
  intro v L
  let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
  exact cardinal_from_prime_valuations p _ _ _ _ _ (card_eq_prime_pow_valuation p A hA)
    (localH_card_eq_prime_pow_valuation K p A hA hAc 0 (by decide))
    (localH_card_eq_prime_pow_valuation K p A hA hAc 1 (by decide))
    (localH_card_eq_prime_pow_valuation K p A hA hAc 2 (by decide))
    (localH1_valuation_of_coprimeAbelianStage K E p A ζ hζ hfix j hA hAc hdeg)

include ζ hζ hfix j in
/-- The same actual abelian-stage calculation gives the normalized Euler
ratio on the original continuous cochain complex. -/
theorem localEulerCoefficient_of_coprimeAbelianStage (hA : ∀ a : A, p • a = 0)
    (hAc : Continuous (fun ga : Γabs × A => A.ρ ga.1 ga.2))
    (hdeg : ¬p ∣ Module.finrank K E) :
    hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K) A := by
  let v := localIntegerValuation K
  let L := LocalField.ofWithZeroValuation v
  let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
  let q := L.residueCharacteristic
  let d := Module.finrank ℚ_[q] K
  let : Fact q.Prime := ⟨L.residueCharacteristic_prime⟩
  let C := (continuousModuleComplexFunctor Γabs).obj A
  let c (i : ℕ) := Nat.card (continuousCohomology i A)
  let e (i : ℕ) := continuousModuleHomologyIso Γabs A i
  have hc (i : ℕ) : Nat.card (C.homology i) = c i :=
    Nat.card_congr (Equiv.ofBijective (e i).hom (ConcreteCategory.bijective_of_isIso (e i).hom))
  have hfin (i : ℕ) (hi : i < 3) : Finite (continuousCohomology i A) :=
    finite_localIntegralCohomology_lt_three K A hAc i hi
  refine ⟨(fun i hi => ?_), ?_⟩
  · let : Finite (continuousCohomology i A) := hfin i hi
    exact Finite.of_injective (e i).hom (ConcreteCategory.bijective_of_isIso (e i).hom).1
  have h1 := card_localH1_of_coprimeAbelianStage K E p A ζ hζ hfix j hA hAc hdeg
  change c 1 = c 0 * c 2 * Nat.card A ^ (d * padicValNat q p) at h1
  have hweight : Nat.card A ^ (d * padicValNat q p) = q ^ (d * padicValNat q (Nat.card A)) := by
    rw [card_eq_prime_pow_valuation p A hA]
    simp only [Nat.padicValNat_def, Nat.multiplicity_pow]
    by_cases hq : q = p
    · rw [hq, Nat.Prime.multiplicity_self, mul_one, mul_one, ← pow_mul, mul_comm d]
    · simp only [multiplicity_primes hq, mul_zero, pow_zero]
  have hcard : (c 1 : ℚ) = (c 0 : ℚ) * (c 2 : ℚ) * (q : ℚ) ^ (d * padicValNat q (Nat.card A)) := by
    rw [hweight] at h1
    exact_mod_cast h1
  let : Finite (continuousCohomology 1 A) := hfin 1 (by decide)
  have hc₁ : (c 1 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hq₀ : (q : ℚ) ^ (d * padicValNat q (Nat.card A)) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr L.residueCharacteristic_prime.ne_zero)
  change lowDegreeEulerCharacteristic C = _
  rw [lowDegreeEulerCharacteristic, hc 0, hc 1, hc 2]
  change (c 0 : ℚ) * (c 2 : ℚ) / (c 1 : ℚ) = (q : ℚ)⁻¹ ^ (d * padicValNat q (Nat.card A))
  rw [inv_pow, div_eq_iff hc₁, hcard, ← mul_assoc, mul_comm ((q : ℚ) ^ _)⁻¹, mul_assoc,
    inv_mul_cancel₀ hq₀, mul_one]

private theorem localEulerCoefficient_of_scalarStage (B : TopRep.{u} ℤ Γabs)
    [Finite B] [DiscreteTopology B]
    (hB : Continuous (fun ga : Γabs × B => B.ρ ga.1 ga.2)) (hBp : ∀ b : B, p • b = 0)
    (F : FiniteGaloisIntermediateField K (SeparableClosure K))
    [IsMulCommutative Gal(F/K)] (α : F) (hα : IsPrimitiveRoot α p)
    (hdeg : ¬ p ∣ Module.finrank K F)
    (hfix : ∀ σ : Γabs, σ ∈ F.toIntermediateField.fixingSubgroup → ∀ b : B, B.ρ σ b = b) :
    hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K) B := by
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let : NontriviallyNormedField F := finiteExtensionSpectralNormedField K F
  let : ValuativeRel F := finiteExtensionSpectralValuativeRel K F
  let : IsNonarchimedeanLocalField F := finiteExtensionSpectralIsNonarchimedeanLocalField K F
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let : IsIntegralClosure 𝒪[F] 𝒪[K] F := localCompleteDVF_integerRing_isIntegralClosure K F
  let : Module.Finite 𝒪[K] 𝒪[F] := localCompleteDVF_integerRing_moduleFinite K F
  let : IsSepClosure F (SeparableClosure K) := ⟨inferInstance, inferInstance⟩
  let j := IsSepClosure.equiv F (SeparableClosure K) (SeparableClosure F)
  exact localEulerCoefficient_of_coprimeAbelianStage K F p B α hα
    (fun σ b => hfix σ σ.property b) j hBp hB hdeg

/-- A prime scalar character has the local Euler characteristic on its
actual coefficient module. Its finite splitting stage simultaneously
trivializes the original action and contains the prime roots of unity. -/
theorem localEulerCoefficient_scalarLine (B : TopRep.{u} ℤ Γabs) [DiscreteTopology B]
    (e : B ≃+ ZMod p) (hB : Continuous (fun ga : Γabs × B => B.ρ ga.1 ga.2)) :
    hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K) B := by
  let hp : p.Prime := Fact.out
  let : Finite B := Finite.of_injective e e.injective
  obtain ⟨F, hab, α, hα, hdeg, hfix⟩ :=
    exists_coprimeScalarLineStage K p (Nat.cast_ne_zero.mpr hp.ne_zero) B e hB
  let : IsMulCommutative Gal(F/K) := hab
  refine localEulerCoefficient_of_scalarStage K p B hB (fun b => e.injective ?_) F α hα hdeg hfix
  rw [map_nsmul, map_zero]
  exact ZModModule.char_nsmul_eq_zero p (e b)

/-- The scalar-character formula also holds for a line over a finite
coefficient field of characteristic `p`, viewed as an integral module. -/
theorem localEulerCoefficient_finiteFieldScalarLine (k : Type*) [Field k] [Finite k] [CharP k p]
    (B : TopRep.{u} ℤ Γabs) [DiscreteTopology B] (e : B ≃+ k)
    (χ : Γabs →* kˣ) (hχ : IsLocallyConstant χ)
    (hact : ∀ σ b, e (B.ρ σ b) = (χ σ : k) * e b)
    (hB : Continuous (fun ga : Γabs × B => B.ρ ga.1 ga.2)) :
    hasLowDegreeEulerCharacteristic Γabs (localCoefficientOrderNorm K) B := by
  let hp : p.Prime := Fact.out
  let : Finite B := Finite.of_injective e e.injective
  obtain ⟨F, hab, α, hα, hdeg, hfix⟩ := exists_coprimeFiniteFieldScalarLineStage K p
    (Nat.cast_ne_zero.mpr hp.ne_zero) k B e χ hχ hact
  let : IsMulCommutative Gal(F/K) := hab
  refine localEulerCoefficient_of_scalarStage K p B hB (fun b => e.injective ?_) F α hα hdeg hfix
  rw [map_nsmul, map_zero, nsmul_eq_mul, CharP.cast_eq_zero k p, zero_mul]

end ClassFieldTheory.Brauer
