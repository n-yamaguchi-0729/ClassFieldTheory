/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Order.DirectedInverseSystem
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.GaloisDescent

/-!
# The finite-extension system of function-field idele classes

The stages are the actual idele class groups of the finite Galois intermediate
fields of an ambient extension. Their curve and principal-divisor structures
follow from the ordinary function-field hypothesis on the base. Inclusion of
intermediate fields gives the existing completed base-change maps. Their tower
law and Galois descent make this a directed system of injective homomorphisms.

The ambient field is arbitrary. In particular, the same system applies to a
chosen separable closure without replacing its stages by abstract groups.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionSystem

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω]
    [FunctionField k K] [PerfectField k]

/-- The rational parameter and the constants act through the same ambient inclusion. -/
instance stageRatFuncTower (E : FiniteGaloisIntermediateField K Ω) :
    IsScalarTower k (RatFunc k) E :=
  IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply k (RatFunc k) Ω x)

/-- A finite stage remains a finite extension of the original rational function field. -/
instance stageFunctionField (E : FiniteGaloisIntermediateField K Ω) :
    FunctionField k E :=
  Module.Finite.trans K E

/-- The stage has the established curve structure, including principal divisors. -/
instance stageIsCurveOver (E : FiniteGaloisIntermediateField K Ω) :
    AlgebraicCurve.IsCurveOver k E :=
  FunctionField.isCurveOver k E

/-- The group at a finite Galois stage is its actual all-place idele class group. -/
abbrev stage (E : FiniteGaloisIntermediateField K Ω) := IdeleClassGroup k E

/-- The algebra structure between comparable stages is the actual field inclusion. -/
abbrev inclusionAlgebra {E F : FiniteGaloisIntermediateField K Ω} (h : E ≤ F) :
    Algebra E F :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- Inclusion of stages is compatible with the base-field scalar structure. -/
theorem inclusion_baseScalarTower {E F : FiniteGaloisIntermediateField K Ω} (h : E ≤ F) :
    let _ : Algebra E F := inclusionAlgebra h
    IsScalarTower K E F := by
  intro aEF
  exact IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

omit [Algebra (RatFunc k) K]
  [Algebra (RatFunc k) Ω] [IsScalarTower (RatFunc k) K Ω]
  [IsScalarTower k (RatFunc k) Ω] [FunctionField k K] [PerfectField k] in
/-- Inclusion of stages is compatible with the original constant-field structure. -/
theorem inclusion_scalarTower {E F : FiniteGaloisIntermediateField K Ω} (h : E ≤ F) :
    let _ : Algebra E F := inclusionAlgebra h
    IsScalarTower k E F := by
  intro aEF
  exact IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

/-- A comparable pair of finite stages is a finite field extension. -/
theorem inclusion_finiteDimensional {E F : FiniteGaloisIntermediateField K Ω} (h : E ≤ F) :
    let _ : Algebra E F := inclusionAlgebra h
    FiniteDimensional E F := by
  intro aEF
  have : IsScalarTower K E F := inclusion_baseScalarTower h
  exact FiniteDimensional.right K E F

/-- The extension between two finite Galois stages is again Galois. -/
theorem inclusion_isGalois {E F : FiniteGaloisIntermediateField K Ω} (h : E ≤ F) :
    let _ : Algebra E F := inclusionAlgebra h
    IsGalois E F := by
  intro aEF
  have : IsScalarTower K E F := inclusion_baseScalarTower h
  exact IsGalois.tower_top_of_isGalois K E F

/-- The transition homomorphism is the actual completed idele-class base change. -/
def transition (E F : FiniteGaloisIntermediateField K Ω) (h : E ≤ F) :
    stage (k := k) E →* stage (k := k) F :=
  let _aEF : Algebra E F := inclusionAlgebra h
  have : IsScalarTower k E F := inclusion_scalarTower (k := k) h
  have : FiniteDimensional E F := inclusion_finiteDimensional h
  have : IsGalois E F := inclusion_isGalois h
  IdeleClassGroup.baseChange (k := k) (K := E) (L := F)

/-- Each transition homomorphism is injective by the proved Galois descent theorem. -/
theorem transition_injective (E F : FiniteGaloisIntermediateField K Ω) (h : E ≤ F) :
    Function.Injective (transition (k := k) E F h) := by
  let aEF : Algebra E F := inclusionAlgebra h
  have : IsScalarTower k E F := inclusion_scalarTower (k := k) h
  have : FiniteDimensional E F := inclusion_finiteDimensional h
  have : IsGalois E F := inclusion_isGalois h
  exact IdeleClassGroup.baseChange_injective (k := k) (K := E) (L := F)

/-- A stage includes identically into itself. -/
@[simp]
theorem transition_self (E : FiniteGaloisIntermediateField K Ω) (c : stage (k := k) E) :
    transition (k := k) E E le_rfl c = c := by
  change IdeleClassGroup.baseChange (k := k) (K := E) (L := E) c = c
  exact IdeleClassGroup.baseChange_self c

/-- Transition through an intermediate stage agrees with direct inclusion. -/
theorem transition_trans (E F G : FiniteGaloisIntermediateField K Ω)
    (hEF : E ≤ F) (hFG : F ≤ G) (c : stage (k := k) E) :
    transition (k := k) F G hFG (transition (k := k) E F hEF c) =
      transition (k := k) E G (hEF.trans hFG) c := by
  let aEF : Algebra E F := inclusionAlgebra hEF
  let aFG : Algebra F G := inclusionAlgebra hFG
  let aEG : Algebra E G := inclusionAlgebra (hEF.trans hFG)
  have : IsScalarTower k E F := inclusion_scalarTower (k := k) hEF
  have : IsScalarTower k F G := inclusion_scalarTower (k := k) hFG
  have : IsScalarTower k E G := inclusion_scalarTower (k := k) (hEF.trans hFG)
  have : IsScalarTower E F G := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : FiniteDimensional E F := inclusion_finiteDimensional hEF
  have : FiniteDimensional F G := inclusion_finiteDimensional hFG
  have : FiniteDimensional E G := inclusion_finiteDimensional (hEF.trans hFG)
  have : IsGalois E F := inclusion_isGalois hEF
  have : IsGalois F G := inclusion_isGalois hFG
  have : IsGalois E G := inclusion_isGalois (hEF.trans hFG)
  exact IdeleClassGroup.baseChange_trans (k := k) (K := E) (L := F) (M := G) c

/-- The actual finite-stage idele class groups and inclusion maps form a directed system. -/
instance directedSystem :
    DirectedSystem (fun E : FiniteGaloisIntermediateField K Ω => stage (k := k) E)
      (fun E F h => transition (k := k) E F h) where
  map_self {i} c := transition_self i c
  map_map {m} {j} {i} hEF hFG c := transition_trans i j m hEF hFG c

end FunctionField.IdeleClassGroup.FiniteExtensionSystem
