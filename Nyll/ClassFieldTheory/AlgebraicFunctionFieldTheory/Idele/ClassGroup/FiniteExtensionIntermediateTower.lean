/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate

/-!
# Inclusion through arbitrary finite intermediate fields

The direct-limit inclusion respects actual idele-class base change between
finite intermediate fields. Both maps are compared in the same normal closure.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionLimit

open FiniteExtensionSystem

variable {k K Ω : Type*} [Field k] [PerfectField k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [FunctionField k K] [IsGalois K Ω]

/-- Actual inclusion through an intermediate field agrees in a containing Galois stage. -/
theorem includeInStage_baseChange (E F : IntermediateField K Ω)
    [FiniteDimensional K E] [FiniteDimensional K F] (hEF : E ≤ F)
    (H : FiniteGaloisIntermediateField K Ω) (hFH : F ≤ H) :
    let _ : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    let _ : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional E F := FiniteDimensional.right K E F
    let _ : Algebra.IsSeparable E F := Algebra.isSeparable_tower_top_of_isSeparable K E F
    ∀ c : IdeleClassGroup k E,
      includeInStage (k := k) F H hFH (baseChange (k := k) (K := E) (L := F) c) =
        includeInStage (k := k) E H (hEF.trans hFH) c := by
  intro aEF hKEF hkEF hEFfinite hEFsep c
  have hEH : E ≤ H := hEF.trans hFH
  let aEH : Algebra E H := (IntermediateField.inclusion hEH).toRingHom.toAlgebra
  let aFH : Algebra F H := (IntermediateField.inclusion hFH).toRingHom.toAlgebra
  have hKEH : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hKFH : IsScalarTower K F H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkEH : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkFH : IsScalarTower k F H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hEFH : IsScalarTower E F H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hEHfinite : FiniteDimensional E H := FiniteDimensional.right K E H
  have hFHfinite : FiniteDimensional F H := FiniteDimensional.right K F H
  have hEHgal : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  have hFHgal : IsGalois F H := IsGalois.tower_top_of_isGalois K F H
  exact baseChange_trans (k := k) (K := E) (L := F) (M := H) c

/-- The actual inclusion into the limit commutes with every finite intermediate inclusion. -/
theorem ofIntermediate_baseChange (E F : IntermediateField K Ω)
    [FiniteDimensional K E] [FiniteDimensional K F] (hEF : E ≤ F) :
    let _ : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
    let _ : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional E F := FiniteDimensional.right K E F
    let _ : Algebra.IsSeparable E F := Algebra.isSeparable_tower_top_of_isSeparable K E F
    ∀ c : IdeleClassGroup k E,
      ofIntermediate (k := k) F (baseChange (k := k) (K := E) (L := F) c) =
        ofIntermediate (k := k) E c := by
  intro aEF hKEF hkEF hEFfinite hEFsep c
  let H := normalClosureStage F
  have hFH : F ≤ H := IntermediateField.le_normalClosure F
  calc
    ofIntermediate (k := k) F (baseChange (k := k) (K := E) (L := F) c) =
        of (k := k) H (includeInStage (k := k) F H hFH
          (baseChange (k := k) (K := E) (L := F) c)) := ofIntermediate_eq_of F H hFH _
    _ = of (k := k) H (includeInStage (k := k) E H (hEF.trans hFH) c) :=
      congrArg (of (k := k) H) (includeInStage_baseChange E F hEF H hFH c)
    _ = ofIntermediate (k := k) E c := (ofIntermediate_eq_of E H (hEF.trans hFH) c).symm

end FunctionField.IdeleClassGroup.FiniteExtensionLimit
