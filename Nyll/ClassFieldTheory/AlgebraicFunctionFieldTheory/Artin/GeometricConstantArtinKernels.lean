/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Data.Finset.Image

/-!
# Exhaustion of geometric function units by native Artin kernels

Every finite set of units in the actual geometric constant extension comes
from one finite constant stage. At that stage, the original reciprocity kernel
recovers the function units. Composing that proved equivalence with the literal
intermediate-field inclusion gives an injective homomorphism containing all the
specified units in its image.

The function-field presentation and principal divisors at the stage are supplied
by the original finite extension. The only boundary requirement is that its
modulus is nonzero, as required to recover constants as well as principal divisors.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

private theorem intermediateField_inclusion_val
    {F : Type u} {A : Type v} [Field F] [Field A] [Algebra F A]
    (E B : IntermediateField F A) (h : E ≤ B) (x : E) :
    Subtype.val (IntermediateField.inclusion h x) = Subtype.val x := rfl

section Inclusions

variable (k : Type u) (K : Type v) (Ω : Type w)
    [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- The literal inclusion of a constructed finite constant stage into the geometric field. -/
def fullConstantStageGeometricInclusion (n : ℕ+) :
    fullConstantDegreeStage k K Ω n →ₐ[K] geometricConstantExtension k K Ω :=
  IntermediateField.inclusion
    (show (fullConstantDegreeStage k K Ω n).toIntermediateField ≤
      geometricConstantExtension k K Ω from fun x hx =>
        (mem_geometricConstantExtension_iff k K Ω x).mpr ⟨n, hx⟩)

/-- This inclusion keeps the original ambient field element. -/
theorem fullConstantStageGeometricInclusion_coe (n : ℕ+) :
    let E := fullConstantDegreeStage k K Ω n
    let i : E →ₐ[K] geometricConstantExtension k K Ω :=
      fullConstantStageGeometricInclusion k K Ω n
    ∀ x : E, Subtype.val (i x) = Subtype.val x := by
  intro E i x
  exact intermediateField_inclusion_val E.toIntermediateField
    (geometricConstantExtension k K Ω)
    (fun y hy => (mem_geometricConstantExtension_iff k K Ω y).mpr ⟨n, hy⟩) x

end Inclusions

variable (k : Type u) (K : Type v) (Ω : Type w) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- A single native finite-stage Artin kernel contains representatives for any
finite collection of actual geometric function units. Its map to geometric units
is injective and uses the original inclusion of fields. -/
theorem finite_geometricUnits_from_artinKernels
    (m : Modulus k K) (hm : m ≠ 0)
    (S : Finset (geometricConstantExtension k K Ω)ˣ) :
    ∃ n : ℕ+,
      let E := fullConstantDegreeStage k K Ω n
      let p := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K E
      let _ : Algebra (RatFunc k) E := p.val
      let _ : IsScalarTower k (RatFunc k) E := p.property.1
      let _ : FunctionField k E := p.property.2
      let _ : HasPrincipalDivisors k E :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
      let e := principalRestrictedArtinKernelEquiv (rayModulusBaseChange E m)
        (rayModulusBaseChange_ne_zero m hm)
      let f := (Units.map (fullConstantStageGeometricInclusion k K Ω n).toMonoidHom).comp
        e.symm.toMonoidHom
      Function.Injective f ∧ ∀ x ∈ S, ∃ a, f a = x := by
  classical
  let T : Finset Ω := S.image fun x : (geometricConstantExtension k K Ω)ˣ =>
    ((x : geometricConstantExtension k K Ω) : Ω)
  have hT : ∀ y ∈ T, y ∈ geometricConstantExtension k K Ω := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact (x : geometricConstantExtension k K Ω).property
  obtain ⟨n, hn⟩ := exists_fullConstantDegreeStage_containing_finset k K Ω T hT
  refine ⟨n, ?_⟩
  intro E p aRE hkRE hE hprincipal e f
  constructor
  · exact (Units.map_injective
      (fullConstantStageGeometricInclusion k K Ω n).injective).comp e.symm.injective
  · intro x hx
    have hxstage : ((x : geometricConstantExtension k K Ω) : Ω) ∈ E.toIntermediateField :=
      hn _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    let y : E := ⟨((x : geometricConstantExtension k K Ω) : Ω), hxstage⟩
    have hy : y ≠ 0 := by
      intro hzero
      apply Units.ne_zero x
      apply Subtype.ext
      exact congrArg (fun z : E => (z : Ω)) hzero
    let u : Eˣ := Units.mk0 y hy
    refine ⟨e u, ?_⟩
    have he : f (e u) =
        Units.map (fullConstantStageGeometricInclusion k K Ω n).toMonoidHom u :=
      congrArg (Units.map (fullConstantStageGeometricInclusion k K Ω n).toMonoidHom)
        (e.symm_apply_apply u)
    apply he.trans
    apply Units.ext
    apply Subtype.ext
    rfl

end FunctionField.RayClass
