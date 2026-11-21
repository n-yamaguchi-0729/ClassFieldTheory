/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianCharacterConductor
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap

/-! # Ideals attached to the finite character conductors -/

@[expose] public section

open scoped NumberField nonZeroDivisors
open ClassFieldTheory
open NumberField IsDedekindDomain

noncomputable section
namespace GlobalClassFieldTheory.GlobalClassFields

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
  {A : Type*} [CommGroup A]

/-- The integral ideal represented by the finite part of the full conductor. -/
def abelianCharacterFiniteConductorIdeal (χ : Gal(L/K) →* A) : Ideal (𝓞 K) :=
  (abelianCharacterConductor K L χ).finitePart.prod fun v n => v.asIdeal ^ n

private theorem abelianCharacterFiniteConductorIdeal_coe (χ : Gal(L/K) →* A) :
    let e := (abelianCharacterConductor K L χ).finitePart.mapRange
      (fun n : ℕ => (n : ℤ)) (by rfl)
    (abelianCharacterFiniteConductorIdeal χ : FractionalIdeal (𝓞 K)⁰ K) =
      (NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  intro e
  let c := (abelianCharacterConductor K L χ).finitePart
  have hs : e.support = c.support := by
    ext v
    simp only [e, c, Finsupp.mem_support_iff, Finsupp.mapRange_apply, Nat.cast_ne_zero]
  change (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) (c.prod fun v n => v.asIdeal ^ n) = _
  rw [NumberFieldFractionalIdealGroup.factorization_val,
    toAdd_ofAdd, map_finsuppProd,
    Finsupp.prod, Finsupp.prod, hs]
  apply Finset.prod_congr rfl
  intro v _
  change ((v.asIdeal ^ c v : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
    (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ ((c v : ℕ) : ℤ)
  rw [FractionalIdeal.coeIdeal_pow, zpow_natCast]

/-- A character conductor is a nonzero integral ideal. -/
theorem abelianCharacterFiniteConductorIdeal_ne_bot (χ : Gal(L/K) →* A) :
    abelianCharacterFiniteConductorIdeal χ ≠ ⊥ := by
  apply (FractionalIdeal.coeIdeal_ne_zero (K := K)).mp
  rw [abelianCharacterFiniteConductorIdeal_coe]
  exact Units.ne_zero _

/-- The coefficient of a prime in the character conductor ideal is the
local exponent in the full conductor. -/
theorem count_abelianCharacterFiniteConductorIdeal
    (χ : Gal(L/K) →* A) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (abelianCharacterFiniteConductorIdeal χ : FractionalIdeal (𝓞 K)⁰ K) =
      ((abelianCharacterConductor K L χ).finitePart v : ℤ) := by
  simp only [abelianCharacterFiniteConductorIdeal_coe,
    NumberFieldFractionalIdealGroup.count_factorization,
    toAdd_ofAdd, Finsupp.mapRange_apply]

/-- The prime coefficient of the product of character conductor ideals is
the sum of their local conductor exponents. -/
theorem count_prod_abelianCharacterFiniteConductorIdeal
    (s : Finset (Gal(L/K) →* A)) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((∏ χ ∈ s, abelianCharacterFiniteConductorIdeal χ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ∑ χ ∈ s, ((abelianCharacterConductor K L χ).finitePart v : ℤ) := by
  let conductor (χ : Gal(L/K) →* A) : FractionalIdeal (𝓞 K)⁰ K :=
    abelianCharacterFiniteConductorIdeal χ
  have hne (χ : Gal(L/K) →* A) (_ : χ ∈ s) : conductor χ ≠ 0 :=
    (FractionalIdeal.coeIdeal_ne_zero (K := K)).mpr
      (abelianCharacterFiniteConductorIdeal_ne_bot χ)
  change FractionalIdeal.count K v
    (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K (∏ χ ∈ s, abelianCharacterFiniteConductorIdeal χ)) = _
  rw [map_prod]
  change FractionalIdeal.count K v (∏ χ ∈ s, conductor χ) = _
  rw [FractionalIdeal.count_prod K v s conductor hne]
  exact Finset.sum_congr rfl (fun χ _ => count_abelianCharacterFiniteConductorIdeal χ v)

end GlobalClassFieldTheory.GlobalClassFields
