/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianCharacterConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbsoluteCharacterConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RankOneArtinConductor
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Euler polynomials for one-dimensional finite Galois characters

The constant polynomial at a ramified character and the arithmetic
Frobenius factor at an unramified character both use the existing global
Artin symbol and its conductor.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup Reciprocity FunctionField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The two Artin normalizations give inverse values on the same idele class. -/
theorem rankOneCharacter_arithmetic_eq_inv_geometric
    (χ : Gal(L/K) →* ℂˣ) (c : IdeleClassGroup K) :
    χ (arithmeticGlobalNormResidueMonoidHom K L c) =
      (χ (globalNormResidueMonoidHom K L c))⁻¹ := by
  rw [arithmeticGlobalNormResidueMonoidHom_apply, map_inv]

/-- The arithmetic and geometric pullbacks have the same character kernel. -/
theorem rankOneCharacter_arithmetic_ker_eq_geometric
    (χ : Gal(L/K) →* ℂˣ) :
    (χ.comp (arithmeticGlobalNormResidueMonoidHom K L)).ker =
      (abelianCharacterConductorialSubgroup K L χ).val := by
  ext c
  change χ (arithmeticGlobalNormResidueMonoidHom K L c) = 1 ↔
    χ (globalNormResidueMonoidHom K L c) = 1
  rw [rankOneCharacter_arithmetic_eq_inv_geometric, inv_eq_one]

/-- A faithful character has exactly the conductor of the extension it cuts out. -/
theorem rankOneCharacter_conductor_eq_extension_of_injective
    (χ : Gal(L/K) →* ℂˣ) (hχ : Function.Injective χ) :
    abelianCharacterConductor K L χ =
      (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor := by
  have hker : abelianCharacterConductorialSubgroup K L χ =
      ideleClassNormConductorialSubgroup (K := K) (L := L) := by
    apply Subtype.ext
    ext c
    change χ (globalNormResidueMonoidHom K L c) = 1 ↔ c ∈ (_root_.ideleClassNorm K L).range
    rw [← globalNormResidueMonoidHom_eq_one_iff K L c, ← map_one χ]
    exact hχ.eq_iff
  exact congrArg ConductorialSubgroup.fullConductor hker

/-- The local Euler polynomial uses the prime idele value in arithmetic
normalization. Positive local character conductor gives the polynomial one. -/
def rankOneEulerPolynomial (χ : Gal(L/K) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) : Polynomial ℂ :=
  Nat.rec
    (1 - Polynomial.C (χ (arithmeticFinitePlacePrimeArtin (L := L) v)).val * Polynomial.X)
    (fun _ _ => 1) ((abelianCharacterConductor K L χ).finitePart v)

theorem rankOneEulerPolynomial_of_ramified (χ : Gal(L/K) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : 0 < (abelianCharacterConductor K L χ).finitePart v) :
    rankOneEulerPolynomial χ v = 1 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  simp only [rankOneEulerPolynomial, hn]

/-- The geometric Hecke evaluation contributes its inverse to the factor. -/
theorem rankOneEulerPolynomial_of_conductor_zero (χ : Gal(L/K) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (abelianCharacterConductor K L χ).finitePart v = 0) :
    rankOneEulerPolynomial χ v =
      1 - Polynomial.C ((χ (finitePlacePrimeArtin (L := L) v))⁻¹).val * Polynomial.X := by
  simp only [rankOneEulerPolynomial, hv,
    arithmeticFinitePlacePrimeArtin_eq_inv, map_inv]
  rfl

/-- At an unramified place the prime idele value is the actual local
arithmetic Frobenius transported into the finite global Galois group. -/
theorem rankOneEulerPolynomial_of_unramified (χ : Gal(L/K) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : _root_.ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    rankOneEulerPolynomial χ v =
      1 - Polynomial.C (χ (chosenFinitePlaceArithmeticFrobenius v hv)).val * Polynomial.X := by
  have h := (ClassFieldTheory.abelianFullConductor_finiteExponent_eq_zero_iff_unramified
    (K := K) (L := L) v).mpr hv
  have hc : (abelianCharacterConductor K L χ).finitePart v = 0 := by
    have hle := (abelianCharacterConductor_le K L χ).1 v
    rw [h] at hle
    exact Nat.le_zero.mp hle
  simp only [rankOneEulerPolynomial, hc,
    arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius v hv]
  rfl

/-- A continuous finite-image rank-one representation has a faithful
restriction stage with the same full conductor. At its unramified places,
the Euler factor uses the value of the original representation on any
absolute lift of the arithmetic Frobenius. -/
theorem exists_finiteImageAbsoluteGaloisCharacter_rankOneStage
    (ρ : Field.absoluteGaloisGroup K →ₜ* ℂˣ) (hρ : Finite ρ.toMonoidHom.range) :
    ∃ E : ClassFieldTheory.FiniteAbelianExtension K, ∃ ψ : Gal(E/K) →ₜ* ℂˣ,
      (∀ σ, ρ σ = ψ (absoluteRestrictionOfEmbedding K E E.1.val
        (QuotientGroup.mk (AlgEquiv.separableClosure σ)))) ∧
      Function.Injective ψ ∧
      finiteImageAbsoluteGaloisCharacterConductor K ρ hρ =
        (ideleClassNormConductorialSubgroup (K := K) (L := E)).fullConductor ∧
      (∀ v : RayClass.RealPlace K,
        v ∈ (finiteImageAbsoluteGaloisCharacterConductor K ρ hρ).infinitePart ↔
          ψ (chosenInfinitePlaceArtinMonoidHom (K := K) (L := E) v.1
            (-1 : v.1.Completionˣ)) ≠ 1) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K))
        (hv : _root_.ChosenFinitePlaceIsUnramified (K := K) (L := E) v)
        (σ : Field.absoluteGaloisGroup K),
        absoluteRestrictionOfEmbedding K E E.1.val
            (QuotientGroup.mk (AlgEquiv.separableClosure σ)) =
          chosenFinitePlaceArithmeticFrobenius v hv →
        rankOneEulerPolynomial ψ.toMonoidHom v = 1 - Polynomial.C (ρ σ).val * Polynomial.X) := by
  obtain ⟨E, ψ, hψ, hInj, hCond⟩ := exists_finiteImageAbsoluteGaloisCharacter_finiteStage K ρ hρ
  refine ⟨E, ψ, hψ, hInj,
    hCond.trans (rankOneCharacter_conductor_eq_extension_of_injective ψ.toMonoidHom hInj), ?_, ?_⟩
  · intro v
    rw [hCond]
    exact rankOneCharacter_mem_infinitePart_iff ψ.toMonoidHom v
  · intro v hv σ hσ
    rw [rankOneEulerPolynomial_of_unramified ψ.toMonoidHom v hv, hψ σ, hσ]
    rfl

end GlobalClassFieldTheory.GlobalClassFields
