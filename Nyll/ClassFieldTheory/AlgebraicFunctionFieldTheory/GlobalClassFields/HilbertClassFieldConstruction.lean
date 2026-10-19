/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.Classification
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SplitRayQuotient
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.FiniteAbelianLocalExtension

/-!
# Construction of the class field with prescribed splitting

Ordinary-topology class-field classification realizes the zero-modulus ray
subgroup enlarged by the full local groups at a nonempty finite set of places.
The selected actual finite extension has exactly this prescribed norm image.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace FunctionField

open AlgebraicCurve

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- The actual finite abelian Hilbert class field in which the nonempty
finite set of prescribed places splits completely. -/
def hilbertClassField (S : Finset (Place k K)) (hS : S.Nonempty) :
    ClassFieldTheory.FiniteAbelianLocalExtension K :=
  (finiteAbelianFieldNormSubgroupOrderIso k K).symm
    (OrderDual.toDual
      ⟨⟨RayClass.splitRaySubgroup 0 S, RayClass.isOpen_splitRaySubgroup 0 S⟩,
        RayClass.finiteIndex_splitRaySubgroup 0 S hS⟩)

/-- The Hilbert class field has exactly the zero-modulus norm subgroup
with all local groups at the prescribed splitting places adjoined. -/
theorem hilbertClassField_norm (S : Finset (Place k K)) (hS : S.Nonempty) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    (IdeleClassGroup.norm (k := k) (K := K)
      (L := (hilbertClassField k K S hS).val)).range = RayClass.splitRaySubgroup 0 S := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  exact congrArg
    (fun U : {H : OpenSubgroup (IdeleClassGroup k K) // H.toSubgroup.FiniteIndex} =>
      U.val.toSubgroup)
    (finiteAbelianFieldNormSubgroupOrderIso_symm_norm k K
      ⟨⟨RayClass.splitRaySubgroup 0 S, RayClass.isOpen_splitRaySubgroup 0 S⟩,
        RayClass.finiteIndex_splitRaySubgroup 0 S hS⟩)

end FunctionField
