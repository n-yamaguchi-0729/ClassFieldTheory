/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitKummerExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnitPowerIndex
import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation

/-!
# Degree of the actual S-unit Kummer extension

The valuation criterion for S-units identifies the ambient-power quotient
with the S-unit power quotient. The existing Kummer pairing and finite
character duality then compute the degree of the actual root field.
-/

noncomputable section

namespace FunctionField.SUnits

open AlgebraicCurve KummerTheory

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- Ambient n-th powers among S-units are precisely powers of S-units. -/
theorem nthPowers_subgroupOf_units (n : ℕ+) (S : Finset (Place k K)) :
    (unitNthPowersSubgroup K n).subgroupOf (units k K S) =
      (powMonoidHom (α := units k K S) (n : ℕ)).range := by
  ext a
  constructor
  · rintro ⟨b, hb⟩
    change b ^ (n : ℕ) = a.val at hb
    have hbS : b ∈ units k K S := mem_units_of_pow_mem S n n.ne_zero b
      (by rw [hb]; exact a.property)
    exact ⟨⟨b, hbS⟩, Subtype.ext hb⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, rfl⟩

/-- The radical quotient defining the actual S-unit root field is its power quotient. -/
def radicalQuotientEquivPowerQuotient (n : ℕ+) (S : Finset (Place k K)) :
    RestrictedRadicalQuotient n (kummerSubgroup n S) ≃*
      units k K S ⧸ (powMonoidHom (α := units k K S) (n : ℕ)).range :=
  (restrictedRadicalQuotientMulEquiv n (kummerSubgroup n S)).trans
    ((QuotientGroup.quotientInfEquivProdNormalQuotient
      (units k K S) (unitNthPowersSubgroup K n)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq (nthPowers_subgroupOf_units n S)))

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- The actual S-unit Kummer extension has degree n raised to the number of
places in a nonempty S. Its finite and Galois structures are constructed. -/
theorem kummerExtension_finrank {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (S : Finset (Place k K)) (hS : S.Nonempty) :
    Module.finrank K (kummerExtension (Ω := Ω) n S) = (n : ℕ) ^ S.card := by
  let Δ := kummerSubgroup n S
  let E := kummerRadicalExtension (K := K) (Omega := Ω) n Δ.1
  let R := RestrictedRadicalQuotient n Δ
  have hR : Finite R := finite_restrictedRadicalQuotient n S
  have hE : FiniteDimensional K E :=
    kummerRadicalExtension_finiteDimensional_of_finite_quotient n hn hmu Δ
  have hGalois : IsGalois K E := kummerRadicalExtension_isGalois n Δ.1
  obtain ⟨dual⟩ := finiteNthRootsCharacterDuality (G := R) (K := K) (L := E)
    n hmu (restrictedRadicalQuotient_pow_eq_one n Δ)
  have hdegree : Module.finrank K E = Nat.card R :=
    (IsGalois.card_aut_eq_finrank K E).symm.trans
      (Nat.card_congr ((kummerRadicalExtensionRestrictedTransposeMulEquiv
        (K := K) (Omega := Ω) n hn hmu Δ).trans dual).toEquiv)
  have hfield : E = kummerExtension (Ω := Ω) n S :=
    kummerRadicalExtension_sup_unitNthPowers n hn hmu (units k K S)
  rw [← hfield]
  exact hdegree.trans ((Nat.card_congr (radicalQuotientEquivPowerQuotient n S).toEquiv).trans
    (card_powerQuotient S hS n hmu))

end FunctionField.SUnits
