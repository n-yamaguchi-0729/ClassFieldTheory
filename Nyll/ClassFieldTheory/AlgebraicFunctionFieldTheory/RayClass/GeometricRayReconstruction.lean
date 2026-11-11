/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernelTransport
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernelLocalization
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinBoundaryStages
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinTransitionOrders
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.GeometricRestrictedRayTransitions
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayReconstruction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.ReconstructedRayBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReconstruction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTransport
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayUnitSeparation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantTower

/-!
# Geometric multiplication from native constant-stage ray maps

At each original finite constant stage, local closure and arithmetic degree
determine the actual local and global ray maps. The original Artin squares and
place-restriction squares imply their compatibility with the literal native
kernel transitions. Ramification-index compatibility is proved from the actual
constant extensions; it is not an extra input.

The native-kernel direct limit then gives multiplication on the actual
geometric constant composita. The stage formula, all normalized orders, and
full boundary principal units refer to those same original maps.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve LocalClassFieldTheory

namespace FunctionField.RayClass

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors
  geometricLocalizationConstants geometricLocalizationConstantTower

variable (k₁ K₁ Ω₁ k₂ K₂ Ω₂ : Type*)
    [Field k₁] [Finite k₁] [Field K₁] [Field Ω₁]
    [Algebra k₁ K₁] [Algebra (RatFunc k₁) K₁]
    [IsScalarTower k₁ (RatFunc k₁) K₁] [FunctionField k₁ K₁]
    [Algebra K₁ Ω₁] [IsSepClosed Ω₁] [Algebra k₁ Ω₁] [IsScalarTower k₁ K₁ Ω₁]
    [Field k₂] [Finite k₂] [Field K₂] [Field Ω₂]
    [Algebra k₂ K₂] [Algebra (RatFunc k₂) K₂]
    [IsScalarTower k₂ (RatFunc k₂) K₂] [FunctionField k₂ K₂]
    [Algebra K₂ Ω₂] [IsSepClosed Ω₂] [Algebra k₂ Ω₂] [IsScalarTower k₂ K₂ Ω₂]
    (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
    (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
    (hb₁ : ∀ v : Place k₁ K₁, ∃ w : Place k₁ K₁, w ≠ v ∧ m₁ w ≠ 0)
    (hb₂ : ∀ v : Place k₂ K₂, ∃ w : Place k₂ K₂, w ≠ v ∧ m₂ w ≠ 0)

local notation "I" => GeometricArtinIndex k₁ K₁ Ω₁
local notation "q" => geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂
local notation "E₁" => geometricArtinStageField k₁ K₁ Ω₁
local notation "E₂" => geometricArtinStageField k₂ K₂ Ω₂
local notation "M₁" => fun i : I => rayModulusBaseChange (E₁ i) m₁
local notation "M₂" => fun i : I => rayModulusBaseChange (E₂ (q i)) m₂
local notation "A₁" => GeometricArtinStageKernel k₁ K₁ Ω₁ m₁
local notation "A₂" => GeometricArtinStageKernel k₂ K₂ Ω₂ m₂
local notation "b₁" => geometricRestrictedRayTransition k₁ K₁ Ω₁ m₁ hm₁
local notation "b₂" => geometricRestrictedRayTransition k₂ K₂ Ω₂ m₂ hm₂
local notation "t₁" => geometricArtinTransition k₁ K₁ Ω₁ m₁ hm₁
local notation "t₂" => geometricArtinTransition k₂ K₂ Ω₂ m₂ hm₂
local notation "hbE₁" => fun i : I => rayModulusBaseChange_other_boundary (L := E₁ i) m₁ hb₁
local notation "hbE₂" => fun i : I => rayModulusBaseChange_other_boundary (L := E₂ (q i)) m₂ hb₂

variable
    (v : ∀ i : (GeometricArtinIndex k₁ K₁ Ω₁), Place k₁ ((geometricArtinStageField k₁ K₁ Ω₁) i) ≃
      Place k₂ ((geometricArtinStageField k₂ K₂ Ω₂) ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂
      Ω₂) i)))
    (γ : ∀ i : (GeometricArtinIndex k₁ K₁ Ω₁),
      (localAbsoluteAbelianProfinite ((geometricArtinStageField k₁ K₁ Ω₁) i) ⧸ artinRaySubgroup
        (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁)) ≃*
        (localAbsoluteAbelianProfinite ((geometricArtinStageField k₂ K₂ Ω₂)
          ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂) i)) ⧸ artinRaySubgroup
          (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂ (geometricArtinIndexOrderIso k₁
          K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂)))
    (hclosure : ∀ (i : (GeometricArtinIndex k₁ K₁ Ω₁)) (w : Place k₁ ((geometricArtinStageField k₁
      K₁ Ω₁) i)) g,
      g ∈ (localRayAbsoluteArtin (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁)
        w).range.topologicalClosure ↔
        γ i g ∈ (localRayAbsoluteArtin (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂) (v i
          w)).range.topologicalClosure)
    (hdegree : ∀ (i : (GeometricArtinIndex k₁ K₁ Ω₁)) g, rayAbelianDegree (rayModulusBaseChange
      (geometricArtinStageField k₂ K₂ Ω₂ (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂) (γ
      i g) = rayAbelianDegree (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁) g)

/-- The actual finite-stage restricted-product map extracted from native
local closure and Frobenius-degree preservation. -/
def geometricReconstructedRestrictedRayEquiv (i : I) :
    RayRestrictedProduct (M₁ i) ≃* RayRestrictedProduct (M₂ i) :=
  reconstructedRestrictedRayEquiv (M₁ i) (M₂ i) (v i) (γ i)
    (hclosure i) (hdegree i) (hbE₁ i) (hbE₂ i)

/-- The finite-stage original Artin kernels are transported by restriction
of that same actual ray map. -/
def geometricReconstructedRayKernelEquiv (i : I) : A₁ i ≃* A₂ (q i) :=
  reconstructedRayKernelEquiv (M₁ i) (M₂ i) (v i) (γ i)
    (hclosure i) (hdegree i) (hbE₁ i) (hbE₂ i)

local notation "ρ" => geometricReconstructedRestrictedRayEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
  m₁ m₂ hb₁ hb₂ v γ hclosure hdegree
local notation "η" => geometricReconstructedRayKernelEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
  m₁ m₂ hb₁ hb₂ v γ hclosure hdegree

variable
    (hplaces : ∀ (i j : (GeometricArtinIndex k₁ K₁ Ω₁)) (hij : i ≤ j) (w : Place k₁
      ((geometricArtinStageField k₁ K₁ Ω₁) j)),
      geometricArtinStagePlaceRestrict k₂ K₂ Ω₂ ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂)
        i) ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂) j) ((geometricArtinIndexOrderIso k₁ K₁
        Ω₁ k₂ K₂ Ω₂).monotone hij) (v j w) =
        v i (geometricArtinStagePlaceRestrict k₁ K₁ Ω₁ i j hij w))
    (hartin : ∀ (i j : (GeometricArtinIndex k₁ K₁ Ω₁)) (hij : i ≤ j),
      (restrictedProductAbsoluteArtin (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
        (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)) m₂)).comp
          (((geometricReconstructedRestrictedRayEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hb₁ hb₂ v γ hclosure
            hdegree) j).toMonoidHom.comp ((geometricRestrictedRayTransition k₁ K₁ Ω₁ m₁ hm₁) i j
            hij)) =
        (restrictedProductAbsoluteArtin (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)) m₂)).comp
          (((geometricRestrictedRayTransition k₂ K₂ Ω₂ m₂ hm₂) ((geometricArtinIndexOrderIso k₁ K₁
            Ω₁ k₂ K₂ Ω₂) i) ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂) j)
            ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂).monotone hij)).comp
            ((geometricReconstructedRestrictedRayEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hb₁ hb₂ v γ
            hclosure hdegree) i).toMonoidHom))

include hplaces hartin

/-- The original Artin squares force compatibility of the original kernel
maps. Both ramification indices are one by the actual constant-stage theorem. -/
theorem geometricReconstructedRayKernelEquiv_transition
    (i j : I) (hij : i ≤ j) (a : A₁ i) :
    η j (t₁ i j hij a) = t₂ (q i) (q j) ((q).monotone hij) (η i a) := by
  let _ : Algebra (E₁ i) (E₁ j) := stageInclusionAlgebra k₁ K₁ Ω₁ i j hij
  have _ : IsScalarTower K₁ (E₁ i) (E₁ j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : IsScalarTower k₁ (E₁ i) (E₁ j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : FiniteDimensional (E₁ i) (E₁ j) := FiniteDimensional.right K₁ (E₁ i) (E₁ j)
  let _ : Algebra (E₂ (q i)) (E₂ (q j)) :=
    stageInclusionAlgebra k₂ K₂ Ω₂ (q i) (q j) ((q).monotone hij)
  have _ : IsScalarTower K₂ (E₂ (q i)) (E₂ (q j)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : IsScalarTower k₂ (E₂ (q i)) (E₂ (q j)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have _ : FiniteDimensional (E₂ (q i)) (E₂ (q j)) :=
    FiniteDimensional.right K₂ (E₂ (q i)) (E₂ (q j))
  have hsquare := reconstructedRestrictedRayEquiv_baseChange_of_modulus_eq
    (k₁ := k₁) (K₁ := E₁ i) (L₁ := E₁ j)
    (k₂ := k₂) (K₂ := E₂ (q i)) (L₂ := E₂ (q j))
    (M₁ i) (M₂ i) (M₁ j) (M₂ j)
    (rayModulusBaseChange_reduced m₁ hm₁) (rayModulusBaseChange_reduced m₂ hm₂)
    (rayModulusBaseChange_trans (L := E₁ i) (M := E₁ j) m₁)
    (rayModulusBaseChange_trans (L := E₂ (q i)) (M := E₂ (q j)) m₂)
    (v i) (v j) (γ i) (γ j) (hclosure i) (hdegree i) (hclosure j) (hdegree j)
    (hbE₁ i) (hbE₂ i) (hbE₁ j) (hbE₂ j) (hplaces i j hij)
    (fun w => (geometricArtinStage_ramificationIndex k₁ K₁ Ω₁ i j hij w).trans
      (geometricArtinStage_ramificationIndex k₂ K₂ Ω₂
        (q i) (q j) ((q).monotone hij) (v j w)).symm)
    (hartin i j hij)
  apply Subtype.ext
  simp only [geometricReconstructedRayKernelEquiv, reconstructedRayKernelEquiv_coe,
    geometricArtinTransition_coe]
  exact DFunLike.congr_fun hsquare a.val

variable (hz₁ : m₁ ≠ 0) (hz₂ : m₂ ≠ 0)

local notation "hη" => geometricReconstructedRayKernelEquiv_transition k₁ K₁ Ω₁ k₂ K₂ Ω₂
  m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin
local notation "G₁" => geometricConstantExtension k₁ K₁ Ω₁
local notation "G₂" => geometricConstantExtension k₂ K₂ Ω₂
local notation "C₁" => separableClosure k₁ Ω₁
local notation "C₂" => separableClosure k₂ Ω₂
local notation "a₁" => geometricArtinKernelEquiv k₁ K₁ Ω₁ m₁ hm₁ hz₁
local notation "a₂" => geometricArtinKernelEquiv k₂ K₂ Ω₂ m₂ hm₂ hz₂

/-- Multiplication on the actual geometric function units, obtained from
the original finite-stage ray maps and their proved native kernel squares. -/
def geometricReconstructedFunctionUnits : G₁ˣ ≃* G₂ˣ :=
  geometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη

/-- The same reconstructed multiplication on the actual geometric fields,
including zero. -/
def geometricReconstructedFunction : G₁ ≃* G₂ :=
  geometricArtinFunctionEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη

local notation "φˣ" => geometricReconstructedFunctionUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
  m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂
local notation "φ" => geometricReconstructedFunction k₁ K₁ Ω₁ k₂ K₂ Ω₂
  m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂

/-- Zero extension retains the same reconstructed actual geometric unit. -/
theorem geometricReconstructedFunction_apply_units (x : G₁ˣ) :
    φ (x : G₁) = (φˣ x : G₂) :=
  geometricArtinFunctionEquiv_apply_units k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη x

/-- Every actual finite-stage kernel keeps its original reconstructed value
under the geometric limit map. -/
theorem geometricReconstructedFunctionUnits_mk (i : I) (a : A₁ i) :
    φˣ (a₁ ⟦⟨i, a⟩⟧) = a₂ ⟦⟨q i, η i a⟩⟧ :=
  geometricArtinFunctionUnitsEquiv_mk k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη i a

/-- The geometric limit retains the exact finite-stage rational function,
not only its divisor or its class modulo constants. -/
theorem geometricReconstructedFunctionUnits_stage (i : I) (x : (E₁ i)ˣ) :
    φˣ (Units.map (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree).toMonoidHom x) =
      Units.map (fullConstantStageGeometricInclusion k₂ K₂ Ω₂ (q i).degree).toMonoidHom
        (reconstructedRayFunctionUnits (M₁ i) (M₂ i) (v i) (γ i)
          (hclosure i) (hdegree i) (hbE₁ i) (hbE₂ i)
          (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂) x) := by
  let P₁ := principalRestrictedArtinKernelEquiv (M₁ i) (rayModulusBaseChange_ne_zero m₁ hz₁)
  let P₂ := principalRestrictedArtinKernelEquiv (M₂ i) (rayModulusBaseChange_ne_zero m₂ hz₂)
  have hkernel : η i (P₁ x) = P₂
      (reconstructedRayFunctionUnits (M₁ i) (M₂ i) (v i) (γ i)
        (hclosure i) (hdegree i) (hbE₁ i) (hbE₂ i)
        (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂) x) := by
    apply Subtype.ext
    exact (reconstructedRayFunctionUnits_principal (M₁ i) (M₂ i) (v i) (γ i)
      (hclosure i) (hdegree i) (hbE₁ i) (hbE₂ i)
      (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂) x).symm
  have h := geometricReconstructedFunctionUnits_mk k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂ i (P₁ x)
  rw [hkernel] at h
  rw [geometricArtinKernelEquiv_principal, geometricArtinKernelEquiv_principal] at h
  exact h

/-- Zero extension retains every literal finite-stage function inclusion. -/
theorem geometricReconstructedFunction_stage (i : I) (x : E₁ i) :
    φ (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree x) =
      fullConstantStageGeometricInclusion k₂ K₂ Ω₂ (q i).degree
        (reconstructedRayFunction (M₁ i) (M₂ i) (v i) (γ i)
          (hclosure i) (hdegree i) (hbE₁ i) (hbE₂ i)
          (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂) x) := by
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp only [map_zero]
    change φ 0 = 0
    exact map_zero φ
  · change φ ((Units.map
        (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree).toMonoidHom u : G₁ˣ) : G₁) = _
    rw [geometricReconstructedFunction_apply_units, reconstructedRayFunction_apply_units]
    exact congrArg (fun z : G₂ˣ => (z : G₂))
      (geometricReconstructedFunctionUnits_stage k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂ i u)

/-- The original finite-stage function formulas determine the geometric
map uniquely, so its value is independent of every chosen stage representative. -/
theorem geometricReconstructedFunction_unique (ψ : G₁ ≃* G₂)
    (hψ : ∀ (i : I) (x : E₁ i),
      ψ (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree x) =
        fullConstantStageGeometricInclusion k₂ K₂ Ω₂ (q i).degree
          (reconstructedRayFunction (M₁ i) (M₂ i) (v i) (γ i)
            (hclosure i) (hdegree i) (hbE₁ i) (hbE₂ i)
            (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂) x)) :
    ψ = φ := by
  apply MulEquiv.ext
  intro x
  obtain ⟨n, hn⟩ := (mem_geometricConstantExtension_iff k₁ K₁ Ω₁ (x : Ω₁)).mp x.property
  let i : I := ⟨n⟩
  let y : E₁ i := ⟨(x : Ω₁), hn⟩
  have hy : fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree y = x := by
    apply Subtype.ext
    exact fullConstantStageGeometricInclusion_coe k₁ K₁ Ω₁ i.degree y
  rw [← hy]
  exact (hψ i y).trans
    (geometricReconstructedFunction_stage k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂ i y).symm

variable (vG : Place (separableClosure k₁ Ω₁) (geometricConstantExtension k₁ K₁ Ω₁) ≃ Place
  (separableClosure k₂ Ω₂) (geometricConstantExtension k₂ K₂ Ω₂))
    (hgeometricPlaces : ∀ (i : (GeometricArtinIndex k₁ K₁ Ω₁)) (W : Place (separableClosure k₁ Ω₁)
      (geometricConstantExtension k₁ K₁ Ω₁)),
      v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) =
        geometricArtinPlaceAtStage k₂ K₂ Ω₂ ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂) i)
          (vG W))

include hgeometricPlaces

/-- The actual geometric place correspondence and the finite ray orders give
preservation of every normalized integer valuation of the same field map. -/
theorem geometricReconstructedFunction_order (x : G₁) (W : Place C₁ G₁) :
    (vG W).ord (φ x) = W.ord x := by
  apply geometricArtinFunctionEquiv_order k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη vG _ x W
  intro i a V
  rw [← hgeometricPlaces i V]
  exact congrArg Multiplicative.toAdd
    (reconstructedRestrictedRayEquiv_order (M₁ i) (M₂ i) (v i) (γ i)
      (hclosure i) (hdegree i) (hbE₁ i) (hbE₂ i) a.val
      (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i V))

/-- The same geometric multiplication retains full residue value one at
every corresponding actual reduced boundary place. -/
theorem geometricReconstructedFunction_boundary
    (W : Place C₁ G₁)
    (hW₁ : m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ W) = 1)
    (hW₂ : m₂ (algebraicConstantPlaceRestrict (K := K₂) C₂ K₂ (vG W)) = 1)
    (x : G₁) : (vG W).HasValue (φ x) 1 ↔ W.HasValue x 1 := by
  apply geometricArtinFunctionEquiv_boundary k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη vG W hW₁ hW₂ _ x
  intro i a
  rw [← hgeometricPlaces i W]
  exact restrictedRayEquiv_apply_eq_one_iff (v i)
    (fun w => localRayEquivOfClosure (M₁ i) w (M₂ i) (v i w) (γ i)
      (hclosure i w) (hdegree i) (hbE₁ i w) (hbE₂ i (v i w)))
    a.val (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W)

end FunctionField.RayClass
