/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernelLocalization
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantTower
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Cofinal constant stages separating actual geometric boundary points

Distinct geometric places are distinguished by membership of an actual
function in their valuation rings. That function descends to a finite constant
stage. Its original inclusion then separates the restrictions of the places
at that stage and at every larger stage.

In particular, two distinct geometric boundary points give a cofinal family
of stages where every place has another positive boundary component. The
local Artin embedding criterion therefore does not require the boundary to
split over the original finite field.
-/

@[expose] public section


noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

/-- Two literal inclusions into a common intermediate field commute with
the inclusion between their source fields. -/
theorem intermediateField_inclusion_compat
    {B A : Type*} [Field B] [Field A] [Algebra B A]
    (E H G : IntermediateField B A) (hEH : E ≤ H)
    (iE : E →ₐ[B] G) (iH : H →ₐ[B] G)
    (hiE : ∀ x : E, Subtype.val (iE x) = Subtype.val x)
    (hiH : ∀ x : H, Subtype.val (iH x) = Subtype.val x) (x : E) :
    iH (IntermediateField.inclusion hEH x) = iE x := by
  apply Subtype.ext
  exact (hiH (IntermediateField.inclusion hEH x)).trans (hiE x).symm

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

local notation "E" => geometricArtinStageField k K Ω
local notation "G" => geometricConstantExtension k K Ω
local notation "C" => separableClosure k Ω

local instance geometricBoundaryConstants : Algebra C G :=
  constantAlgebra (K := K) C

local instance geometricBoundaryConstantTower : IsScalarTower k C G :=
  constantScalarTower (K := K) C

omit [Algebra k Ω] [IsScalarTower k K Ω] in
/-- Actual containment of finite constant stages is exactly divisibility of
their original degrees over the function field. -/
theorem geometricArtinIndex_le_iff_degree_dvd
    (i j : GeometricArtinIndex k K Ω) :
    i ≤ j ↔ (i.degree : ℕ) ∣ (j.degree : ℕ) := by
  constructor
  · intro hij
    have hd := IntermediateField.finrank_dvd_of_le_right
      (show (E i).toIntermediateField ≤ (E j).toIntermediateField from hij)
    change Module.finrank K (fullConstantDegreeStage k K Ω i.degree) ∣
      Module.finrank K (fullConstantDegreeStage k K Ω j.degree) at hd
    rw [finrank_fullConstantDegreeStage, finrank_fullConstantDegreeStage] at hd
    exact hd
  · exact fullConstantDegreeStage_mono k K Ω

/-- The actual finite-stage inclusion detects membership in the original
geometric valuation ring. -/
theorem geometricArtinPlaceAtStage_mem
    (i : GeometricArtinIndex k K Ω) (W : Place C G) (x : E i) :
    x ∈ (geometricArtinPlaceAtStage k K Ω i W).toValuationSubring ↔
      fullConstantStageGeometricInclusion k K Ω i.degree x ∈ W.toValuationSubring := by
  constructor
  · intro hx
    apply W.mem_toValuationSubring_of_ord_nonneg
    rw [geometricArtinPlaceAtStage_order]
    exact (geometricArtinPlaceAtStage k K Ω i W).ord_nonneg_of_mem hx
  · intro hx
    apply (geometricArtinPlaceAtStage k K Ω i W).mem_toValuationSubring_of_ord_nonneg
    rw [← geometricArtinPlaceAtStage_order k K Ω i W x]
    exact W.ord_nonneg_of_mem hx

private theorem geometricArtinStageInclusion_commutes
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j) (x : E i) :
    fullConstantStageGeometricInclusion k K Ω j.degree
        (IntermediateField.inclusion hij x) =
      fullConstantStageGeometricInclusion k K Ω i.degree x := by
  exact intermediateField_inclusion_compat
    (E i).toIntermediateField (E j).toIntermediateField (geometricConstantExtension k K Ω) hij
    (fullConstantStageGeometricInclusion k K Ω i.degree)
    (fullConstantStageGeometricInclusion k K Ω j.degree)
    (fullConstantStageGeometricInclusion_coe k K Ω i.degree)
    (fullConstantStageGeometricInclusion_coe k K Ω j.degree) x

private theorem geometricArtinPlaceAtStage_mem_inclusion
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j)
    (W : Place C G) (x : E i) :
    x ∈ (geometricArtinPlaceAtStage k K Ω i W).toValuationSubring ↔
      IntermediateField.inclusion hij x ∈
        (geometricArtinPlaceAtStage k K Ω j W).toValuationSubring := by
  exact (geometricArtinPlaceAtStage_mem k K Ω i W x).trans
    ((Iff.of_eq (congrArg (fun z : G => z ∈ W.toValuationSubring)
      (geometricArtinStageInclusion_commutes k K Ω i j hij x).symm)).trans
        (geometricArtinPlaceAtStage_mem k K Ω j W
          (IntermediateField.inclusion hij x)).symm)

/-- Equality of actual restrictions at a larger constant stage implies
equality at every smaller stage, using their literal function inclusions. -/
theorem geometricArtinPlaceAtStage_eq_of_le
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j)
    (W V : Place C G)
    (h : geometricArtinPlaceAtStage k K Ω j W =
      geometricArtinPlaceAtStage k K Ω j V) :
    geometricArtinPlaceAtStage k K Ω i W =
      geometricArtinPlaceAtStage k K Ω i V := by
  apply Place.ext
  apply SetLike.ext
  intro x
  exact (geometricArtinPlaceAtStage_mem_inclusion k K Ω i j hij W x).trans
    ((Iff.of_eq (congrArg (fun w : Place k (E j) =>
      IntermediateField.inclusion hij x ∈ w.toValuationSubring) h)).trans
        (geometricArtinPlaceAtStage_mem_inclusion k K Ω i j hij V x).symm)

/-- Above every actual constant stage, two distinct geometric places have
distinct restrictions at a constructed larger finite constant stage. -/
theorem exists_geometricArtinStage_separating
    (i : GeometricArtinIndex k K Ω) (W V : Place C G) (hWV : W ≠ V) :
    ∃ j : GeometricArtinIndex k K Ω, i ≤ j ∧
      geometricArtinPlaceAtStage k K Ω j W ≠
        geometricArtinPlaceAtStage k K Ω j V := by
  classical
  have hex : ∃ x : G, ¬ (x ∈ W.toValuationSubring ↔ x ∈ V.toValuationSubring) := by
    by_contra! h
    exact hWV (Place.ext (SetLike.ext h))
  obtain ⟨x, hx⟩ := hex
  obtain ⟨n, hn⟩ := (mem_geometricConstantExtension_iff k K Ω (x : Ω)).mp x.property
  obtain ⟨d, hi, hn'⟩ := fullConstantDegreeStage_directed k K Ω i.degree n
  let j : GeometricArtinIndex k K Ω := ⟨d⟩
  let y : E j := ⟨(x : Ω), hn' hn⟩
  have hy : fullConstantStageGeometricInclusion k K Ω j.degree y = x := by
    apply Subtype.ext
    exact fullConstantStageGeometricInclusion_coe k K Ω j.degree y
  refine ⟨j, hi, ?_⟩
  intro heq
  apply hx
  rw [← hy, ← geometricArtinPlaceAtStage_mem k K Ω j W y,
    ← geometricArtinPlaceAtStage_mem k K Ω j V y, heq]

/-- Two actual geometric boundary points supply another positive boundary
component at every place on every sufficiently large constant stage. -/
theorem exists_geometricArtinStage_other_boundary
    (m : Modulus k K) (i : GeometricArtinIndex k K Ω)
    (W V : Place C G) (hWV : W ≠ V)
    (hW : m (algebraicConstantPlaceRestrict (K := K) C K W) ≠ 0)
    (hV : m (algebraicConstantPlaceRestrict (K := K) C K V) ≠ 0) :
    ∃ j : GeometricArtinIndex k K Ω, i ≤ j ∧
      ∀ l : GeometricArtinIndex k K Ω, j ≤ l →
      ∀ v : Place k (E l), ∃ w : Place k (E l),
        w ≠ v ∧ rayModulusBaseChange (E l) m w ≠ 0 := by
  classical
  obtain ⟨j, hij, hsep⟩ := exists_geometricArtinStage_separating k K Ω i W V hWV
  refine ⟨j, hij, fun l hjl v => ?_⟩
  have hsep' : geometricArtinPlaceAtStage k K Ω l W ≠
      geometricArtinPlaceAtStage k K Ω l V := by
    intro h
    exact hsep (geometricArtinPlaceAtStage_eq_of_le k K Ω j l hjl W V h)
  have hW' : rayModulusBaseChange (E l) m (geometricArtinPlaceAtStage k K Ω l W) ≠ 0 := by
    rw [geometricArtinPlaceAtStage_modulus]
    exact hW
  have hV' : rayModulusBaseChange (E l) m (geometricArtinPlaceAtStage k K Ω l V) ≠ 0 := by
    rw [geometricArtinPlaceAtStage_modulus]
    exact hV
  by_cases hv : geometricArtinPlaceAtStage k K Ω l W = v
  · exact ⟨geometricArtinPlaceAtStage k K Ω l V,
      fun h => hsep' (hv.trans h.symm), hV'⟩
  · exact ⟨geometricArtinPlaceAtStage k K Ω l W, hv, hW'⟩

/-- Every actual geometric function unit has an original principal-kernel
representative beyond any specified stage where all local embeddings are
available. Both the function and the two geometric boundary points descend
through their original inclusions. -/
theorem exists_geometricArtin_good_boundary_representative
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i : GeometricArtinIndex k K Ω) (x : Gˣ)
    (W V : Place C G) (hWV : W ≠ V)
    (hW : m (algebraicConstantPlaceRestrict (K := K) C K W) ≠ 0)
    (hV : m (algebraicConstantPlaceRestrict (K := K) C K V) ≠ 0) :
    ∃ j : GeometricArtinIndex k K Ω, i ≤ j ∧
      (∀ v : Place k (E j), ∃ w : Place k (E j),
        w ≠ v ∧ rayModulusBaseChange (E j) m w ≠ 0) ∧
      ∃ a : GeometricArtinStageKernel k K Ω m j,
        geometricArtinKernelEquiv k K Ω m hm hmzero ⟦⟨j, a⟩⟧ = x := by
  obtain ⟨n, hn⟩ :=
    (mem_geometricConstantExtension_iff k K Ω ((x : G) : Ω)).mp (x : G).property
  obtain ⟨d, hid, hnd⟩ := fullConstantDegreeStage_directed k K Ω i.degree n
  let b : GeometricArtinIndex k K Ω := ⟨d⟩
  obtain ⟨j, hbj, hgood⟩ :=
    exists_geometricArtinStage_other_boundary k K Ω m b W V hWV hW hV
  let p := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K (E j)
  let _ : Algebra (RatFunc k) (E j) := p.val
  have _ : IsScalarTower k (RatFunc k) (E j) := p.property.1
  have _ : FunctionField k (E j) := p.property.2
  have _ : HasPrincipalDivisors k (E j) :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K (E j)).toHasPrincipalDivisors
  let y : E j := ⟨((x : G) : Ω), hbj (hnd hn)⟩
  have hy : y ≠ 0 := by
    intro hzero
    apply Units.ne_zero x
    apply Subtype.ext
    exact congrArg (fun z : E j => (z : Ω)) hzero
  let u : (E j)ˣ := Units.mk0 y hy
  refine ⟨j, (show i ≤ b from hid).trans hbj, hgood j le_rfl,
    principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E j) m)
      (rayModulusBaseChange_ne_zero m hmzero) u, ?_⟩
  rw [geometricArtinKernelEquiv_principal]
  apply Units.ext
  apply Subtype.ext
  exact fullConstantStageGeometricInclusion_coe k K Ω j.degree y

/-- Matching the positive degrees identifies the actual constant-stage
orders of two curves. The order identity is proved from actual field degrees,
so no correspondence of transition indices is assumed separately. -/
def geometricArtinIndexOrderIso
    (k' K' Ω' : Type*) [Field k'] [Finite k'] [Field K'] [Field Ω']
    [Algebra k' K'] [Algebra (RatFunc k') K'] [IsScalarTower k' (RatFunc k') K']
    [FunctionField k' K'] [Algebra K' Ω'] [IsSepClosed Ω']
    [Algebra k' Ω'] [IsScalarTower k' K' Ω'] :
    GeometricArtinIndex k K Ω ≃o GeometricArtinIndex k' K' Ω' where
  toFun i := ⟨i.degree⟩
  invFun j := ⟨j.degree⟩
  left_inv i := by cases i; rfl
  right_inv j := by cases j; rfl
  map_rel_iff' := by
    intro i j
    rw [geometricArtinIndex_le_iff_degree_dvd,
      geometricArtinIndex_le_iff_degree_dvd]
    rfl

end FunctionField.RayClass
