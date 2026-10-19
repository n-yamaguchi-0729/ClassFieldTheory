/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.PurelyInseparableNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower
import Nyll.SchemeTheory.FunctionFields.Valuations.PurelyInseparable

/-!
# Idele-class norms for every finite function-field extension

The inseparable part has a unique place over each base place, and its completed
principal norm is the original field norm. Factoring through the maximal separable
subextension then proves the principal formula for an arbitrary finite extension.
The same all-place idele norm consequently descends to the existing class group.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

namespace IdeleGroup

/-- The all-place principal norm formula for purely inseparable finite extensions. -/
theorem norm_principalIdele_of_isPurelyInseparable [IsPurelyInseparable K L] (x : Lˣ) :
    norm (K := K) (L := L) (principalIdele k L x) =
      principalIdele k K (Units.map (Algebra.norm K) x) := by
  classical
  apply RestrictedProduct.ext
  intro v
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  let uniqueFiber : Unique ((w.restrict K).fiberOver L) :=
    { default := ⟨w, Place.restrict_mem_fiberOver w⟩
      uniq := fun u => by
        apply Subtype.ext
        apply Place.ext
        apply FieldArithmetic.Chapter06.PurelyInseparableValuation.restriction_injective
          (F := K) (E := L)
        change (u.val.restrict K).toValuationSubring =
          (w.restrict K).toValuationSubring
        exact congrArg Place.toValuationSubring
          ((Place.mem_fiberOver (w.restrict K)).mp u.property) }
  change normComponent (K := K) (L := L) (w.restrict K) (principalIdele k L x) = _
  rw [normComponent_apply, Fintype.prod_unique]
  exact localNorm_principal_of_isPurelyInseparable w x

omit [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] in
private theorem norm_principalIdele_of_separable_purelyInseparable_tower
    {S : Type} [Field S] [Algebra k S] [Algebra K S] [Algebra S L]
    [IsScalarTower k K S] [IsScalarTower k S L] [IsScalarTower K S L]
    [FiniteDimensional K S] [FiniteDimensional S L]
    [Algebra.IsSeparable K S] [IsPurelyInseparable S L]
    [Algebra (RatFunc k) S] [IsScalarTower k (RatFunc k) S] [FunctionField k S]
    [HasPrincipalDivisors k S] (x : Lˣ) :
    norm (K := K) (L := L) (principalIdele k L x) =
      principalIdele k K (Units.map (Algebra.norm K) x) := by
  have htower := norm_trans (k := k) (K := K) (L := S) (M := L)
    (principalIdele k L x)
  dsimp only at htower
  have hpure := norm_principalIdele_of_isPurelyInseparable (k := k) (K := S) (L := L) x
  have hsep := norm_principalIdele (k := k) (K := K) (L := S)
    (Units.map (Algebra.norm S) x)
  rw [← htower, hpure, hsep]
  apply congrArg (principalIdele k K)
  apply Units.ext
  exact Algebra.norm_norm (R := K) (S := S) (a := (x : L))

/-- The all-place norm of a principal idele is its field norm, without a
separability hypothesis on the finite function-field extension. -/
theorem norm_principalIdele_of_finite (x : Lˣ) :
    norm (K := K) (L := L) (principalIdele k L x) =
      principalIdele k K (Units.map (Algebra.norm K) x) := by
  let S : IntermediateField K L := separableClosure K L
  have hkSL : IsScalarTower k S L := IsScalarTower.to₁₃₄ k K S L
  have hSL : FiniteDimensional S L := FiniteDimensional.right K S L
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K S
  let aRS : Algebra (RatFunc k) S := presentation.val
  have hkRS : IsScalarTower k (RatFunc k) S := presentation.property.1
  have hfunctionS : FunctionField k S := presentation.property.2
  have hprincipalS : HasPrincipalDivisors k S :=
    (FunctionField.isCurveOver k S).toHasPrincipalDivisors
  exact norm_principalIdele_of_separable_purelyInseparable_tower (S := S) x

/-- Arbitrary finite function-field norms preserve the actual principal subgroup. -/
theorem norm_mem_principalSubgroup_of_finite {a : IdeleGroup k L}
    (ha : a ∈ principalSubgroup k L) :
    norm (K := K) (L := L) a ∈ principalSubgroup k K := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨Units.map (Algebra.norm K) x, (norm_principalIdele_of_finite x).symm⟩

end IdeleGroup

namespace IdeleClassGroup

/-- The existing all-place idele norm descended for every finite extension of
function fields, including its purely inseparable part. -/
def finiteNorm : IdeleClassGroup k L →* IdeleClassGroup k K :=
  QuotientGroup.map (IdeleGroup.principalSubgroup k L) (IdeleGroup.principalSubgroup k K)
    (IdeleGroup.norm (K := K) (L := L))
    (fun _ ha => IdeleGroup.norm_mem_principalSubgroup_of_finite ha)

/-- The finite-extension class norm is induced by the original idele norm. -/
@[simp]
theorem finiteNorm_mk (a : IdeleGroup k L) :
    finiteNorm (K := K) (L := L) (QuotientGroup.mk a) =
      QuotientGroup.mk (IdeleGroup.norm (K := K) (L := L) a) := rfl

/-- On separable extensions the general finite norm is the existing class norm. -/
theorem finiteNorm_eq_norm [Algebra.IsSeparable K L] :
    finiteNorm (k := k) (K := K) (L := L) = norm (k := k) (K := K) (L := L) := by
  apply MonoidHom.ext
  intro c
  refine QuotientGroup.induction_on c ?_
  intro a
  rfl

end IdeleClassGroup

end FunctionField
