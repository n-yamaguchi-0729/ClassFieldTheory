/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.PrimeIndexClassField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormAlgEquiv
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Mathlib.FieldTheory.IsSepClosed

/-!
# Prime-index class fields in any separable closure

The actual class field constructed in the canonical separable closure is
transported into a supplied separable closure. Its norm group is preserved
by the existing algebra-isomorphism invariance theorem.
-/

noncomputable section

namespace FunctionField

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K] [IsSepClosure K Ω]

/-- A prime-index open subgroup has an actual class field in any supplied
separable closure, with exactly its original norm image. -/
theorem exists_classField_of_prime_index_in_sepClosure
    (H : Subgroup (IdeleClassGroup k K)) [H.FiniteIndex]
    (hH : IsOpen (H : Set (IdeleClassGroup k K))) (hp : H.index.Prime) :
    ∃ A : FiniteGaloisIntermediateField K Ω, IsAbelianGalois K A ∧
      (have _ : AlgebraicCurve.HasPrincipalDivisors k A :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K A).toHasPrincipalDivisors
      (IdeleClassGroup.norm (k := k) (K := K) (L := A)).range = H) := by
  let akSep : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRSep : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKSep : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKSep : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRSep : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  obtain ⟨E, hEfinite, hEabelian, hEnorm⟩ :=
    exists_classField_of_prime_index k K H hH hp
  let φ : SeparableClosure K ≃ₐ[K] Ω := IsSepClosure.equiv K (SeparableClosure K) Ω
  let F : IntermediateField K Ω := E.map φ.toAlgHom
  let ψ : E ≃ₐ[K] F := E.equivMap φ.toAlgHom
  have hFfinite : FiniteDimensional K F := ψ.toLinearEquiv.finiteDimensional
  have hFabelian : IsAbelianGalois K F := IsAbelianGalois.of_algHom ψ.symm.toAlgHom
  have hEprincipal : AlgebraicCurve.HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  let A : FiniteGaloisIntermediateField K Ω := { toIntermediateField := F }
  refine ⟨A, hFabelian, ?_⟩
  intro hFprincipal
  exact (IdeleClassGroup.norm_range_eq_of_algEquiv (k := k) (K := K) ψ).symm.trans hEnorm

end FunctionField
