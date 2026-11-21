/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FiniteClassGroupNorm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTopology

/-!
# Norm and degree from intrinsic function-field hypotheses

Essential finite type and transcendence degree one over a finite field supply
the rational-function-field presentation used in the proofs. The norm on
idele classes is induced by the all-place idele norm on the original fields.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve

namespace FunctionField

variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.EssFiniteType k K]

namespace IdeleGroup

/-- The actual idele norm preserves degree over the original finite base field. -/
theorem degree_norm_of_trdeg_eq_one (htrdeg : Algebra.trdeg k K = 1) (a : IdeleGroup k L) :
    degree (k := k) (K := K) (norm (K := K) a) = degree (k := k) (K := L) a := by
  obtain ⟨aRK, hTower, hFinite⟩ :=
    ClassFieldTheory.FunctionField.exists_ratFuncAlgebra_of_trdeg_eq_one htrdeg
  let : Algebra (RatFunc k) K := aRK
  have : IsScalarTower k (RatFunc k) K := hTower
  have : _root_.FunctionField k K := hFinite
  exact degree_norm_of_finite a

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- On a principal idele, the actual norm is given by the ordinary field norm. -/
theorem norm_principalIdele_of_trdeg_eq_one (htrdeg : Algebra.trdeg k K = 1) (x : Lˣ) :
    norm (K := K) (principalIdele k L x) =
      principalIdele k K (Units.map (Algebra.norm K) x) := by
  obtain ⟨aRK, hTower, hFinite⟩ :=
    ClassFieldTheory.FunctionField.exists_ratFuncAlgebra_of_trdeg_eq_one htrdeg
  let : Algebra (RatFunc k) K := aRK
  have : IsScalarTower k (RatFunc k) K := hTower
  have : _root_.FunctionField k K := hFinite
  exact norm_principalIdele_of_finite x

end IdeleGroup

namespace IdeleClassGroup

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual norm takes principal ideles to principal ideles in the intrinsic presentation. -/
theorem norm_preserves_principal_of_trdeg_eq_one (htrdeg : Algebra.trdeg k K = 1) :
    IdeleGroup.principalSubgroup k L ≤
      (IdeleGroup.principalSubgroup k K).comap (IdeleGroup.norm (K := K) (L := L)) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Units.map (Algebra.norm K) x,
    (IdeleGroup.norm_principalIdele_of_trdeg_eq_one htrdeg x).symm⟩

/-- The original idele norm on classes for a finite extension of an intrinsic function field. -/
def normOfTrdegEqOne (htrdeg : Algebra.trdeg k K = 1) :
    IdeleClassGroup k L →* IdeleClassGroup k K :=
  normOfPrincipal (norm_preserves_principal_of_trdeg_eq_one htrdeg)

@[simp]
theorem normOfTrdegEqOne_mk (htrdeg : Algebra.trdeg k K = 1) (a : IdeleGroup k L) :
    normOfTrdegEqOne htrdeg (mk a) = mk (IdeleGroup.norm (K := K) a) :=
  normOfPrincipal_mk (norm_preserves_principal_of_trdeg_eq_one htrdeg) a

theorem continuous_normOfTrdegEqOne (htrdeg : Algebra.trdeg k K = 1) :
    Continuous (normOfTrdegEqOne (L := L) htrdeg) :=
  continuous_normOfPrincipal (norm_preserves_principal_of_trdeg_eq_one htrdeg)

@[simp]
theorem degree_normOfTrdegEqOne (htrdeg : Algebra.trdeg k K = 1) (c : IdeleClassGroup k L) :
    degree (normOfTrdegEqOne htrdeg c) = degree c := by
  obtain ⟨a, rfl⟩ := mk_surjective c
  rw [normOfTrdegEqOne_mk, degree_mk, degree_mk]
  exact IdeleGroup.degree_norm_of_trdeg_eq_one htrdeg a

/-- The normalized norm formula uses the two actual full constant fields. -/
theorem fullConstants_mul_normalizedDegree_normOfTrdegEqOne
    (htrdeg : Algebra.trdeg k K = 1) (c : IdeleClassGroup k L) :
    (Module.finrank k (algebraicClosure k K) : ℤ) *
        (normalizedDegree (normOfTrdegEqOne htrdeg c)).toAdd =
      (Module.finrank k (algebraicClosure k L) : ℤ) * (normalizedDegree c).toAdd := by
  rw [fullConstants_mul_normalizedDegree, fullConstants_mul_normalizedDegree,
    degree_normOfTrdegEqOne]

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]

/-- Any supplied rational parameter gives the same homomorphism of idele classes. -/
theorem normOfTrdegEqOne_eq_finiteNorm (htrdeg : Algebra.trdeg k K = 1) :
    normOfTrdegEqOne (L := L) htrdeg = finiteNorm (K := K) (L := L) :=
  rfl

end IdeleClassGroup

end FunctionField
