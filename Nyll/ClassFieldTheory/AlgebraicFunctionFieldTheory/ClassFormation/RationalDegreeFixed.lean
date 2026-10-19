/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.RationalDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Representation
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.InvariantNorm

/-!
# Rational degree on actual fixed coefficients and norms

The degree on an arbitrary finite intermediate field is computed through
its normal closure. The resulting invariant additive functional evaluates
the actual abstract relative norm by multiplication by its index.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology
open IdeleClassGroup IdeleClassGroup.FiniteExtensionLimit
open IdeleClassGroup.FiniteExtensionSystem

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω]

/-- Rational degree as an additive functional on the actual integral representation. -/
def ideleClassRationalDegree : (ideleClassRepresentation k K Ω).V →+ ℚ := by
  change Additive (Limit k K Ω) →+ ℚ
  exact MonoidHom.toAdditiveLeft (rationalDegree (k := k) (K := K) (Ω := Ω))

/-- The degree functional is invariant under the actual representation action. -/
theorem ideleClassRationalDegree_action (σ : Gal(Ω/K))
    (c : (ideleClassRepresentation k K Ω).V) :
    ideleClassRationalDegree k K Ω ((ideleClassRepresentation k K Ω).ρ σ c) =
      ideleClassRationalDegree k K Ω c :=
  congrArg Multiplicative.toAdd (rationalDegree_smul σ c.toMul)

/-- The degree of an actual relative norm is its index times the original rational degree. -/
theorem ideleClassRationalDegree_relativeNorm
    (H J : ClosedSubgroup Gal(Ω/K)) (hJH : J.toSubgroup ≤ H.toSubgroup)
    [Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)]
    (c : ambientFixedAddSubgroup (ideleClassRepresentation k K Ω) J) :
    ideleClassRationalDegree k K Ω
        (relativeNorm (ideleClassRepresentation k K Ω) H J hJH c).1 =
      Nat.card (H.toSubgroup ⧸ extensionSubgroup H J hJH) •
        ideleClassRationalDegree k K Ω c.1 :=
  invariantHom_relativeNorm (ideleClassRepresentation k K Ω) (ideleClassRationalDegree k K Ω)
    (ideleClassRationalDegree_action k K Ω) H J hJH c

variable [IsGalois K Ω]

/-- Evaluation on a possibly nonnormal finite intermediate field uses its actual field degree. -/
theorem rationalDegree_ofIntermediate (E : IntermediateField K Ω) [FiniteDimensional K E]
    (c : IdeleClassGroup k E) :
    (rationalDegree (k := k) (K := K) (Ω := Ω) (ofIntermediate (k := k) E c)).toAdd =
      ((degree (k := k) (K := E) c).toAdd : ℚ) / (Module.finrank K E : ℚ) := by
  let H := normalClosureStage E
  have hEH : E ≤ H := IntermediateField.le_normalClosure E
  let aEH : Algebra E H := (IntermediateField.inclusion hEH).toRingHom.toAlgebra
  have hKEH : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkEH : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hfin : FiniteDimensional E H := FiniteDimensional.right K E H
  have hgal : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  rw [ofIntermediate_eq_of E H hEH, rationalDegree_of]
  have hd : ((degree (k := k) (K := H) (includeInStage (k := k) E H hEH c)).toAdd : ℚ) =
      (Module.finrank E H : ℚ) * (degree (k := k) (K := E) c).toAdd := by
    exact_mod_cast (degree_baseChange (k := k) (K := E) (L := H) c)
  have hn : (Module.finrank K H : ℚ) =
      (Module.finrank K E : ℚ) * (Module.finrank E H : ℚ) := by
    exact_mod_cast (Module.finrank_mul_finrank K E H).symm
  change ((degree (k := k) (K := H) (includeInStage (k := k) E H hEH c)).toAdd : ℚ) /
      (Module.finrank K H : ℚ) = _
  rw [hd, hn, mul_comm (Module.finrank E H : ℚ)]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := E) (M := H)).ne')

/-- Evaluation of rational degree on the concrete fixed-field comparison. -/
theorem ideleClassRationalDegree_abstractFixedClassEquiv (H : ClosedSubgroup Gal(Ω/K))
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) H (le_baseField H))) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H) :=
      abstractFixedField_finiteDimensional K Ω H hfinite
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω H)),
      ideleClassRationalDegree k K Ω (abstractFixedClassEquiv k K Ω H hfinite c).1 =
        ((degree (k := k) (K := abstractFixedField K Ω H) c.toMul).toAdd : ℚ) /
          (Module.finrank K (abstractFixedField K Ω H) : ℚ) := by
  intro hEfinite c
  rw [abstractFixedClassEquiv_coe]
  exact rationalDegree_ofIntermediate k K Ω (abstractFixedField K Ω H) c.toMul

end FunctionField
