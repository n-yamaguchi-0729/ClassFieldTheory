/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormCompositum
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Conductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.ExtensionConductor

/-!
# Conductors of composita of finite abelian extensions

The actual compositum norm group is the intersection of the two norm groups.
The least effective conductor of that intersection is their componentwise
maximum. No existence theorem for arbitrary class fields is needed.
-/

noncomputable section

namespace FunctionField.RayClass

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The conductor of an actual finite abelian compositum is the componentwise
maximum of the conductors of its two fields. -/
theorem extensionConductor_sup
    (E F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    [FiniteDimensional K F] [IsAbelianGalois K F] :
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
    extensionConductor (k := k) (K := K) (L := ↥(E ⊔ F)) =
      extensionConductor (k := k) (K := K) (L := E) ⊔
        extensionConductor (k := k) (K := K) (L := F) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  simp only [extensionConductor, finiteAbelian_norm_range_sup]
  exact conductor_inf
    (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range
    (IdeleClassGroup.norm (k := k) (K := K) (L := F)).range
    (IdeleClassGroup.isOpen_norm_range (k := k) (K := K) (L := E))
    (IdeleClassGroup.isOpen_norm_range (k := k) (K := K) (L := F))

end FunctionField.RayClass
