/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.KrullTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantFrobeniusResidue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegree

/-!
# The Frobenius character for actual constant extensions

The normalized degree of an actual idele class determines an automorphism of
each finite constant extension: raise its arithmetic Frobenius to that degree.
The product formula has already descended degree to idele classes. On a local
uniformizer the resulting character is Frobenius to the degree of the place
over the full constant field.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

open AlgebraicCurve

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K] [Algebra K Ω] [IsSepClosed Ω]

/-- The normalized degree character valued in the actual constant-extension Galois group. -/
def constantFrobeniusCharacter (n : ℕ) [NeZero n] :
    IdeleClassGroup k K →*
      (fullConstantDegreeStage k K Ω n ≃ₐ[K] fullConstantDegreeStage k K Ω n) :=
  (zpowersHom _ (fullConstantDegreeFrobenius k K Ω n)).comp
    (normalizedDegree (k := k) (K := K))

/-- The character is arithmetic Frobenius raised to the normalized idele-class degree. -/
theorem constantFrobeniusCharacter_apply (n : ℕ) [NeZero n] (c : IdeleClassGroup k K) :
    constantFrobeniusCharacter k K Ω n c =
      fullConstantDegreeFrobenius k K Ω n ^ (normalizedDegree (k := k) (K := K) c).toAdd :=
  rfl

/-- The kernel is exactly the classes whose normalized degree is divisible by `n`. -/
theorem constantFrobeniusCharacter_eq_one_iff (n : ℕ) [NeZero n]
    (c : IdeleClassGroup k K) :
    constantFrobeniusCharacter k K Ω n c = 1 ↔
      (n : ℤ) ∣ (normalizedDegree (k := k) (K := K) c).toAdd := by
  rw [constantFrobeniusCharacter_apply, ← orderOf_dvd_iff_zpow_eq_one,
    orderOf_fullConstantDegreeFrobenius]

/-- The constant-extension Frobenius character is continuous for the quotient topology. -/
theorem continuous_constantFrobeniusCharacter (n : ℕ) [NeZero n] :
    Continuous (constantFrobeniusCharacter k K Ω n) :=
  (continuous_of_discreteTopology :
    Continuous (zpowersHom _ (fullConstantDegreeFrobenius k K Ω n))).comp
      continuous_normalizedDegree

/-- On a local idele, the exponent is its order times the place degree over the full constants. -/
theorem constantFrobeniusCharacter_placeIdele (n : ℕ) [NeZero n]
    (v : Place k K) (x : v.adicCompletionˣ) :
    constantFrobeniusCharacter k K Ω n (mk (k := k) (K := K) (IdeleGroup.placeIdele v x)) =
      fullConstantDegreeFrobenius k K Ω n ^
        ((IdeleGroup.localOrder v x).toAdd * (v.extendConstants (algebraicClosure k K)).deg) := by
  rw [constantFrobeniusCharacter_apply]
  apply congrArg (fun z : ℤ => fullConstantDegreeFrobenius k K Ω n ^ z)
  exact normalizedDegree_placeIdele v x

/-- A local uniformizer maps to arithmetic Frobenius to the full-constant place degree. -/
theorem constantFrobeniusCharacter_uniformizer (n : ℕ) [NeZero n]
    (v : Place k K) (x : v.adicCompletionˣ) (hx : (IdeleGroup.localOrder v x).toAdd = 1) :
    constantFrobeniusCharacter k K Ω n (mk (k := k) (K := K) (IdeleGroup.placeIdele v x)) =
      fullConstantDegreeFrobenius k K Ω n ^
        (v.extendConstants (algebraicClosure k K)).deg := by
  rw [constantFrobeniusCharacter_placeIdele, hx, one_mul, zpow_natCast]

/-- A uniformizer character is the unique decomposition automorphism inducing
arithmetic Frobenius on the actual residue field of the constant extension. -/
theorem constantFrobeniusCharacter_uniformizer_eq_iff (n : ℕ) [NeZero n]
    (v : Place k K) (x : v.adicCompletionˣ) (hx : (IdeleGroup.localOrder v x).toAdd = 1)
    (w : Place (algebraicClosure k K) (fullConstantDegreeStage k K Ω n))
    (hw : w.restrict K = v.extendConstants (algebraicClosure k K))
    (σ : IdeleGroup.decompositionGroup (K := K) w) :
    constantFrobeniusCharacter k K Ω n (mk (k := k) (K := K) (IdeleGroup.placeIdele v x)) =
        σ.val ↔
      ∀ y : w.ResidueField, IdeleGroup.decompositionResidueAut (K := K) w σ y =
        y ^ Nat.card (w.restrict K).ResidueField := by
  have hchar : constantFrobeniusCharacter k K Ω n
      (mk (k := k) (K := K) (IdeleGroup.placeIdele v x)) =
        (fullConstantDegreeFrobeniusDecomposition k K Ω n w).val := by
    rw [constantFrobeniusCharacter_uniformizer k K Ω n v x hx]
    change fullConstantDegreeFrobenius k K Ω n ^ _ =
      fullConstantDegreeFrobenius k K Ω n ^ (w.restrict K).deg
    rw [hw]
  rw [hchar]
  constructor
  · intro h y
    have hσ : σ = fullConstantDegreeFrobeniusDecomposition k K Ω n w := Subtype.ext h.symm
    rw [hσ]
    exact fullConstantDegreeFrobeniusDecomposition_residue k K Ω n w y
  · intro h
    apply congrArg Subtype.val
    apply (decompositionResidueAut_bijective_fullConstantDegreeStage k K Ω n w).1
    apply AlgEquiv.ext
    intro y
    rw [fullConstantDegreeFrobeniusDecomposition_residue, h y]

end FunctionField.IdeleClassGroup
