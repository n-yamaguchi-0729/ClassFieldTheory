/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricConstantKernelComparison
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricConstantArtinKernels
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The geometric limit of the native Artin kernels

The transition maps in this directed system are the original restricted-ray
base changes, followed by equality of the pulled-back boundary moduli. Their
direct limit is multiplicatively equivalent to the units of the actual
geometric constant extension. On each finite stage the equivalence sends a
principal kernel element to the original included function.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

private theorem equiv_inverse_naturality
    {A B C X Y : Type*} [Monoid A] [Monoid B] [Monoid C] [Monoid X] [Monoid Y]
    (eA : A ≃* X) (eB : B ≃* Y) (f : X →* Y)
    (iA : A →* C) (iB : B →* C) (j : A →* B)
    (hf : ∀ x, f (eA x) = eB (j x)) (hi : ∀ x, iB (j x) = iA x) (a : X) :
    iB (eB.symm (f a)) = iA (eA.symm a) := by
  obtain ⟨x, rfl⟩ := eA.surjective a
  rw [hf, eB.symm_apply_apply, eA.symm_apply_apply]
  exact hi x

private theorem units_map_inclusion_compat
    {B A : Type*} [Field B] [Field A] [Algebra B A]
    (E H G : IntermediateField B A) (hEH : E ≤ H)
    (iE : E →ₐ[B] G) (iH : H →ₐ[B] G)
    (hiE : ∀ x : E, Subtype.val (iE x) = Subtype.val x)
    (hiH : ∀ x : H, Subtype.val (iH x) = Subtype.val x) (x : Eˣ) :
    Units.map iH.toMonoidHom (Units.map (IntermediateField.inclusion hEH).toMonoidHom x) =
      Units.map iE.toMonoidHom x := by
  apply Units.ext
  apply Subtype.ext
  exact (hiH (IntermediateField.inclusion hEH (x : E))).trans (hiE (x : E)).symm

/-- Positive constant-extension degrees, ordered below by inclusion of their
actual intermediate fields. The index remains small because its only datum is
a positive natural number; the three field parameters have independent universes. -/
structure GeometricArtinIndex (k : Type u) (K : Type v) (Ω : Type w) : Type where
  /-- The positive degree of the actual constant-field extension. -/
  degree : ℕ+

instance (k : Type u) (K : Type v) (Ω : Type w) : Nonempty (GeometricArtinIndex k K Ω) := ⟨⟨1⟩⟩

variable (k : Type u) (K : Type v) (Ω : Type w) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- The original finite constant field at an index. -/
def geometricArtinStageField (i : GeometricArtinIndex k K Ω) :
    FiniteGaloisIntermediateField K Ω :=
  fullConstantDegreeStage k K Ω i.degree

instance : Preorder (GeometricArtinIndex k K Ω) :=
  Preorder.lift fun i => (geometricArtinStageField k K Ω i).toIntermediateField

instance : IsDirectedOrder (GeometricArtinIndex k K Ω) where
  directed i j := by
    obtain ⟨n, hi, hj⟩ := fullConstantDegreeStage_directed k K Ω i.degree j.degree
    exact ⟨⟨n⟩, hi, hj⟩

local notation "E" => geometricArtinStageField k K Ω

/- The presentation is always induced from the same rational parameter of K.
These local instances are not registered as alternative global presentations. -/
local instance stageRatFuncAlgebra (i : GeometricArtinIndex k K Ω) :
    Algebra (RatFunc k) (E i) :=
  (ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K (E i)).val

local instance stageRatFuncTower (i : GeometricArtinIndex k K Ω) :
    IsScalarTower k (RatFunc k) (E i) :=
  (ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K (E i)).property.1

local instance stageFunctionField (i : GeometricArtinIndex k K Ω) :
    FunctionField k (E i) :=
  (ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K (E i)).property.2

local instance stagePrincipalDivisors (i : GeometricArtinIndex k K Ω) :
    HasPrincipalDivisors k (E i) :=
  (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K (E i)).toHasPrincipalDivisors

/-- The kernel of the original absolute Artin map at a finite constant stage. -/
abbrev GeometricArtinStageKernel (m : Modulus k K) (i : GeometricArtinIndex k K Ω) : Type w :=
  ↥((restrictedProductAbsoluteArtin (rayModulusBaseChange (E i) m)).ker)

/-- Inclusion of a native kernel into the actual geometric function units. -/
def geometricArtinStageToUnits (m : Modulus k K) (hmzero : m ≠ 0)
    (i : GeometricArtinIndex k K Ω) :
    GeometricArtinStageKernel k K Ω m i →* (geometricConstantExtension k K Ω)ˣ :=
  (Units.map (fullConstantStageGeometricInclusion k K Ω i.degree).toMonoidHom).comp
    (principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E i) m)
      (rayModulusBaseChange_ne_zero m hmzero)).symm.toMonoidHom

/-- The map on each stage retains the literal function-field inclusion. -/
theorem geometricArtinStageToUnits_principal (m : Modulus k K) (hmzero : m ≠ 0)
    (i : GeometricArtinIndex k K Ω) (x : (E i)ˣ) :
    geometricArtinStageToUnits k K Ω m hmzero i
        (principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E i) m)
          (rayModulusBaseChange_ne_zero m hmzero) x) =
      Units.map (fullConstantStageGeometricInclusion k K Ω i.degree).toMonoidHom x :=
  congrArg (Units.map (fullConstantStageGeometricInclusion k K Ω i.degree).toMonoidHom)
    ((principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E i) m)
      (rayModulusBaseChange_ne_zero m hmzero)).symm_apply_apply x)

/-- A finite-stage kernel embeds in the actual geometric units. -/
theorem geometricArtinStageToUnits_injective (m : Modulus k K) (hmzero : m ≠ 0)
    (i : GeometricArtinIndex k K Ω) :
    Function.Injective (geometricArtinStageToUnits k K Ω m hmzero i) :=
  (Units.map_injective (fullConstantStageGeometricInclusion k K Ω i.degree).injective).comp
    (principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E i) m)
      (rayModulusBaseChange_ne_zero m hmzero)).symm.injective

/-- The stage algebra is induced by the literal inclusion of the intermediate fields. -/
@[instance_reducible]
def stageInclusionAlgebra (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j) :
    Algebra (E i) (E j) :=
  (IntermediateField.inclusion hij).toRingHom.toAlgebra

omit [Algebra k Ω] [IsScalarTower k K Ω] in
private theorem stageInclusion_units (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j) :
    let _ : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
    ∀ x : (E i)ˣ, Units.map (algebraMap (E i) (E j)) x =
      Units.map (IntermediateField.inclusion hij).toMonoidHom x := by
  intro aij x
  apply Units.ext
  apply Subtype.ext
  rfl

/-- The actual restricted-ray transition on kernels, with only the equality of
the iterated and direct boundary pullbacks applied afterwards. -/
def geometricArtinTransition (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j) :
    GeometricArtinStageKernel k K Ω m i →* GeometricArtinStageKernel k K Ω m j := by
  let _ : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
  have _ : IsScalarTower K (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have _ : IsScalarTower k (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have _ : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
  exact (principalArtinKernelCongr
    (rayModulusBaseChange_trans (L := E i) (M := E j) m)).toMonoidHom.comp
      (principalArtinKernelBaseChange (L := E j) (rayModulusBaseChange (E i) m)
        (rayModulusBaseChange_reduced m hm))

/-- The native transition takes a principal representative to the same function
under the literal intermediate-field inclusion. -/
theorem geometricArtinTransition_principal (m : Modulus k K)
    (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j) (x : (E i)ˣ) :
    geometricArtinTransition k K Ω m hm i j hij
        (principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E i) m)
          (rayModulusBaseChange_ne_zero m hmzero) x) =
      principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E j) m)
        (rayModulusBaseChange_ne_zero m hmzero)
        (Units.map (IntermediateField.inclusion hij).toMonoidHom x) := by
  let _ : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
  have _ : IsScalarTower K (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have _ : IsScalarTower k (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have _ : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
  have ht := nativeTransition_principal
    (k := k) (K := K) («E» := E i) (H := E j) m hm hmzero x
  have hu := stageInclusion_units k K Ω i j hij x
  have hfinal := ht.trans
    (congrArg (principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E j) m)
      (rayModulusBaseChange_ne_zero m hmzero)) hu)
  simpa only [geometricArtinTransition, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    using hfinal

/-- The original transitions commute with the actual geometric inclusions. -/
theorem geometricArtinStageToUnits_transition (m : Modulus k K)
    (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i j : GeometricArtinIndex k K Ω) (hij : i ≤ j)
    (a : GeometricArtinStageKernel k K Ω m i) :
    geometricArtinStageToUnits k K Ω m hmzero j
        (geometricArtinTransition k K Ω m hm i j hij a) =
      geometricArtinStageToUnits k K Ω m hmzero i a := by
  let eI := principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E i) m)
    (rayModulusBaseChange_ne_zero m hmzero)
  let eJ := principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E j) m)
    (rayModulusBaseChange_ne_zero m hmzero)
  let uI := Units.map (fullConstantStageGeometricInclusion k K Ω i.degree).toMonoidHom
  let uJ := Units.map (fullConstantStageGeometricInclusion k K Ω j.degree).toMonoidHom
  let uIJ := Units.map (IntermediateField.inclusion hij).toMonoidHom
  have hinc : ∀ x : (E i)ˣ, uJ (uIJ x) = uI x :=
    units_map_inclusion_compat (E i).toIntermediateField (E j).toIntermediateField
      (geometricConstantExtension k K Ω) hij
      (fullConstantStageGeometricInclusion k K Ω i.degree)
      (fullConstantStageGeometricInclusion k K Ω j.degree)
      (fullConstantStageGeometricInclusion_coe k K Ω i.degree)
      (fullConstantStageGeometricInclusion_coe k K Ω j.degree)
  exact equiv_inverse_naturality eI eJ (geometricArtinTransition k K Ω m hm i j hij)
    uI uJ uIJ (geometricArtinTransition_principal k K Ω m hm hmzero i j hij) hinc a

/-- The native maps form a directed system. Coherence is checked after the
injective inclusions of their original function representatives. -/
theorem geometricArtinDirectedSystem (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) :
    DirectedSystem (GeometricArtinStageKernel k K Ω m)
      (fun ⦃i j⦄ hij a => geometricArtinTransition k K Ω m hm i j hij a) where
  map_self := by
    intro i a
    apply geometricArtinStageToUnits_injective k K Ω m hmzero _
    exact geometricArtinStageToUnits_transition k K Ω m hm hmzero _ _ le_rfl a
  map_map := by
    intro l j i hij hjl a
    apply geometricArtinStageToUnits_injective k K Ω m hmzero _
    rw [geometricArtinStageToUnits_transition, geometricArtinStageToUnits_transition,
      geometricArtinStageToUnits_transition]

/-- Direct limit of the native finite-stage absolute-Artin kernels. -/
def GeometricArtinKernel (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) : Type w :=
  let _ := geometricArtinDirectedSystem k K Ω m hm hmzero
  DirectLimit (GeometricArtinStageKernel k K Ω m) (geometricArtinTransition k K Ω m hm)

instance geometricArtinKernelCommGroup
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) :
    CommGroup (GeometricArtinKernel k K Ω m hm hmzero) := by
  let _ := geometricArtinDirectedSystem k K Ω m hm hmzero
  exact inferInstanceAs
    (CommGroup (DirectLimit (GeometricArtinStageKernel k K Ω m)
      (geometricArtinTransition k K Ω m hm)))

/-- The map from the native kernel limit to the actual geometric function units. -/
def geometricArtinKernelToUnits (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) :
    GeometricArtinKernel k K Ω m hm hmzero →* (geometricConstantExtension k K Ω)ˣ := by
  let _ := geometricArtinDirectedSystem k K Ω m hm hmzero
  let f := geometricArtinTransition k K Ω m hm
  let g := geometricArtinStageToUnits k K Ω m hmzero
  have hg : ∀ i j hij a, g i a = g j (f i j hij a) :=
    fun i j hij a => (geometricArtinStageToUnits_transition k K Ω m hm hmzero i j hij a).symm
  exact
    { toFun := DirectLimit.lift f (fun i => g i) hg
      map_one' := DirectLimit.lift_one g hg
      map_mul' := DirectLimit.lift_mul g hg }

/-- The limit map evaluates a native representative by the original finite-stage map. -/
theorem geometricArtinKernelToUnits_mk (m : Modulus k K)
    (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i : GeometricArtinIndex k K Ω) (a : GeometricArtinStageKernel k K Ω m i) :
    geometricArtinKernelToUnits k K Ω m hm hmzero ⟦⟨i, a⟩⟧ =
      geometricArtinStageToUnits k K Ω m hmzero i a := rfl

/-- Common-stage injectivity makes the map out of the actual direct limit injective. -/
theorem geometricArtinKernelToUnits_injective (m : Modulus k K)
    (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) :
    Function.Injective (geometricArtinKernelToUnits k K Ω m hm hmzero) := by
  let _ := geometricArtinDirectedSystem k K Ω m hm hmzero
  exact DirectLimit.lift_injective (geometricArtinTransition k K Ω m hm)
    (fun i => geometricArtinStageToUnits k K Ω m hmzero i)
    (fun i j hij a => (geometricArtinStageToUnits_transition k K Ω m hm hmzero i j hij a).symm)
    (geometricArtinStageToUnits_injective k K Ω m hmzero)

/-- Every actual geometric function descends to a native finite-stage kernel. -/
theorem geometricArtinKernelToUnits_surjective (m : Modulus k K)
    (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) :
    Function.Surjective (geometricArtinKernelToUnits k K Ω m hm hmzero) := by
  intro x
  obtain ⟨n, hn⟩ := (mem_geometricConstantExtension_iff k K Ω
    ((x : geometricConstantExtension k K Ω) : Ω)).mp
      (x : geometricConstantExtension k K Ω).property
  let i : GeometricArtinIndex k K Ω := ⟨n⟩
  let _ : HasPrincipalDivisors k (E i) := stagePrincipalDivisors k K Ω i
  let y : E i := ⟨((x : geometricConstantExtension k K Ω) : Ω), hn⟩
  have hy : y ≠ 0 := by
    intro hzero
    apply Units.ne_zero x
    apply Subtype.ext
    exact congrArg (fun z : E i => (z : Ω)) hzero
  let u : (E i)ˣ := Units.mk0 y hy
  refine ⟨⟦⟨i, principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E i) m)
    (rayModulusBaseChange_ne_zero m hmzero) u⟩⟧, ?_⟩
  rw [geometricArtinKernelToUnits_mk, geometricArtinStageToUnits_principal]
  apply Units.ext
  apply Subtype.ext
  rfl

/-- The actual geometric function units are the direct limit of the original
finite-stage Artin kernels with their original restricted-ray transitions. -/
def geometricArtinKernelEquiv (m : Modulus k K)
    (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) :
    GeometricArtinKernel k K Ω m hm hmzero ≃* (geometricConstantExtension k K Ω)ˣ :=
  MulEquiv.ofBijective (geometricArtinKernelToUnits k K Ω m hm hmzero)
    ⟨geometricArtinKernelToUnits_injective k K Ω m hm hmzero,
      geometricArtinKernelToUnits_surjective k K Ω m hm hmzero⟩

/-- The equivalence preserves each original function, including its constant factor. -/
theorem geometricArtinKernelEquiv_principal (m : Modulus k K)
    (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (i : GeometricArtinIndex k K Ω) (x : (E i)ˣ) :
    geometricArtinKernelEquiv k K Ω m hm hmzero
        ⟦⟨i, principalRestrictedArtinKernelEquiv (rayModulusBaseChange (E i) m)
          (rayModulusBaseChange_ne_zero m hmzero) x⟩⟧ =
      Units.map (fullConstantStageGeometricInclusion k K Ω i.degree).toMonoidHom x :=
  geometricArtinStageToUnits_principal k K Ω m hmzero i x

end FunctionField.RayClass
