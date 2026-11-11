/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReciprocity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionUnramified
public import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegExchange

/-!
# Exact orders along the original constant-stage transitions

Every actual finite constant stage is unramified over the original
function field. The original ramification tower formula therefore forces
every literal inclusion between two such stages to have index one as well.

Consequently the actual local ray inclusions preserve normalized integer
orders. The same holds for the existing native Artin-kernel transition,
including its original comparison of pulled-back boundary moduli.
No index or transition-order equality is supplied as an input.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve
open AlgebraicCurves.Places.Proofs
open Place_sum_ramificationIndex_mul_inertiaDeg_exchange.AlgebraicCurve.Place

namespace FunctionField.RayClass

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

local notation "Stage" => geometricArtinStageField k K Ω

/-- The original inclusion between any two ordered actual constant stages
has ramification index one at every original upper place. -/
theorem geometricArtinStage_ramificationIndex
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j) :
    let _ : Algebra (Stage i) (Stage j) := (IntermediateField.inclusion hij).toRingHom.toAlgebra
    have _ : IsScalarTower K (Stage i) (Stage j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsScalarTower k (Stage i) (Stage j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional (Stage i) (Stage j) := FiniteDimensional.right K (Stage i) (Stage j)
    ∀ w : Place k (Stage j), w.ramificationIndex (Stage i) = 1 := by
  intro aij hKij hkij hfinite w
  have ht :=
    ramificationIndex_eq_mul_ramificationIndex_restrict
      (F := K) (E := Stage i) w
  have hj : w.ramificationIndex K = 1 :=
    ramificationIndex_fullConstantDegreeStage k K Ω j.degree w
  have hi : (w.restrict (Stage i)).ramificationIndex K = 1 :=
    ramificationIndex_fullConstantDegreeStage k K Ω i.degree (w.restrict (Stage i))
  rw [hj, hi, mul_one] at ht
  exact ht.symm

/-- Literal inclusion of an original function between ordered constant
stages preserves its normalized order at every extending place. -/
theorem geometricArtinStage_ord_inclusion
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j) :
    let _ : Algebra (Stage i) (Stage j) := (IntermediateField.inclusion hij).toRingHom.toAlgebra
    have _ : IsScalarTower K (Stage i) (Stage j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsScalarTower k (Stage i) (Stage j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional (Stage i) (Stage j) := FiniteDimensional.right K (Stage i) (Stage j)
    ∀ (w : Place k (Stage j)) (x : Stage i),
      w.ord (IntermediateField.inclusion hij x) = (w.restrict (Stage i)).ord x := by
  intro aij hKij hkij hfinite w x
  change w.ord (algebraMap (Stage i) (Stage j) x) = _
  rw [w.ord_restrict, geometricArtinStage_ramificationIndex k K Ω i j hij w,
    Nat.cast_one, one_mul]

/-- The actual completion-induced map of reduced local ray factors
preserves every integer order along the original constant-stage tower. -/
theorem localRayFactorOrder_geometricArtinBaseChange
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j)
    (m : Modulus k (Stage i)) (hm : ∀ v, m v ≤ 1) :
    let _ : Algebra (Stage i) (Stage j) := (IntermediateField.inclusion hij).toRingHom.toAlgebra
    have _ : IsScalarTower K (Stage i) (Stage j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsScalarTower k (Stage i) (Stage j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional (Stage i) (Stage j) := FiniteDimensional.right K (Stage i) (Stage j)
    ∀ (w : Place k (Stage j)) (a : RayLocalFactor m (w.restrict (Stage i))),
      localRayFactorOrder (rayModulusBaseChange (Stage j) m) w
          (localRayBaseChange (L := Stage j) m hm w a) =
        localRayFactorOrder m (w.restrict (Stage i)) a := by
  intro aij hKij hkij hfinite w a
  apply Multiplicative.ext
  rw [localRayFactorOrder_baseChange,
    geometricArtinStage_ramificationIndex k K Ω i j hij w, Nat.cast_one, one_mul]

/-- The existing native Artin-kernel transition preserves original
normalized orders at every actual upper place. The transition is the
original restricted-ray inclusion followed by its literal modulus equality. -/
theorem geometricArtinTransition_order
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j) :
    let _ : Algebra (Stage i) (Stage j) := (IntermediateField.inclusion hij).toRingHom.toAlgebra
    have _ : IsScalarTower K (Stage i) (Stage j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsScalarTower k (Stage i) (Stage j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional (Stage i) (Stage j) := FiniteDimensional.right K (Stage i) (Stage j)
    ∀ (w : Place k (Stage j)) (a : GeometricArtinStageKernel k K Ω m i),
      restrictedRayOrder (rayModulusBaseChange (Stage j) m) w
          (geometricArtinTransition k K Ω m hm i j hij a).val =
        restrictedRayOrder (rayModulusBaseChange (Stage i) m) (w.restrict (Stage i)) a.val := by
  intro aij hKij hkij hfinite w a
  obtain ⟨x, rfl⟩ := (principalRestrictedArtinKernelEquiv
    (rayModulusBaseChange (Stage i) m) (rayModulusBaseChange_ne_zero m hmzero)).surjective a
  apply Multiplicative.ext
  rw [geometricArtinTransition_principal,
    restrictedRayOrder_principalRestrictedArtinKernelEquiv,
    restrictedRayOrder_principalRestrictedArtinKernelEquiv]
  · exact geometricArtinStage_ord_inclusion k K Ω i j hij w (x : Stage i)
  · exact hmzero

end FunctionField.RayClass
