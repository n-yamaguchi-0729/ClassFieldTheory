/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldNormResidueNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import Nyll.ValuedFieldTheory.LocalField.NormUnits

/-!
# Continuous fixed-field naturality diagrams

The algebraic norm--restriction and transfer--inclusion diagrams are upgraded
here to diagrams of continuous homomorphisms.  Every finite fixed field uses
the spectral norm extended from the original local field.  Thus no source is
made discrete merely to obtain continuity.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open scoped NNReal ValuativeRel
open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- The quotient topology on the algebraic abelianization.  Its underlying
quotient is opaque to typeclass search, so expose the canonical topology
locally while constructing the continuous finite maps. -/
local instance abelianizationQuotientTopologicalSpace
    (G : Type*) [Group G] [TopologicalSpace G] :
    TopologicalSpace (Group.Abelianization G) := by
  change TopologicalSpace (G ⧸ commutator G)
  exact QuotientGroup.instTopologicalSpace (commutator G)

/-! ## Multiplicative forms of the algebraic arrows -/

/-- The fixed-field norm-residue symbol on the native multiplicative unit
group.  This is the multiplicative form of
`abstractFixedFieldNormResidueSymbol`. -/
noncomputable def abstractFixedFieldNormResidueMonoidHom
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    (abstractFixedField k Ω K)ˣ →*
      Group.Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K) :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldNormResidueSymbol
      k Ω D v hcf K L hLK)

/-- The ordinary fixed-field norm on native multiplicative unit groups. -/
def abstractFixedFieldNormUnitsMonoidHom
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    (abstractRelativeFixedField k Ω hK'K)ˣ →*
      (abstractFixedField k Ω K)ˣ :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldNormUnits k Ω K K' hK'K)

/-- Inclusion of native multiplicative fixed-field unit groups. -/
def abstractFixedFieldUnitsInclusionMonoidHom
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    (abstractFixedField k Ω K)ˣ →*
      (abstractFixedField k Ω K')ˣ :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldUnitsInclusion k Ω K K' hK'K)

/-- Restriction on native multiplicative finite abelianizations. -/
noncomputable def abstractFixedFieldAbelianizedRestrictionMonoidHom
    (K K' L L' : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Group.Abelianization
        Gal(abstractRelativeFixedField k Ω hL'K' /
          abstractFixedField k Ω K') →*
      Group.Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K) :=
  MonoidHom.toAdditive.symm
    (abstractFixedFieldAbelianizedRestriction
      k Ω K K' L L' hLK hL'K' hK'K hL'L)

/-! ## The norm kernel -/

/-- Under the concrete fixed-unit equivalence, the finite abstract norm
subgroup pulls back to the ordinary field-norm subgroup. -/
theorem abstractFixedFieldUnitsEquiv_finiteNormSubgroup_preimage
    [IsSepClosed Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    (finiteNormSubgroup (galoisAmbientUnitsRep k Ω)
        K L hLK).comap
      (abstractFixedFieldUnitsEquivGaloisFixed
        k Ω K).toAddMonoidHom =
      additiveNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let uK := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  let uL := abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK
  ext x
  constructor
  · intro hx
    change uK x ∈ finiteNormSubgroup
      (galoisAmbientUnitsRep k Ω) K L hLK at hx
    rcases hx with ⟨b, hb⟩
    let y : Additive (abstractRelativeFixedField k Ω hLK)ˣ :=
      uL.symm b
    have hy : uL y = b := uL.apply_symm_apply b
    have hnorm :=
      relativeNorm_abstractFixedFieldUnit_eq_normUnits
        k Ω K L hLK (Additive.toMul y)
    rw [show Additive.ofMul (Additive.toMul y) = y by rfl, hy] at hnorm
    change Additive.toMul x ∈ (LocalFieldTheory.normUnits
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)).range
    refine ⟨Additive.toMul y, ?_⟩
    apply Additive.ofMul.injective
    apply uK.injective
    exact hnorm.symm.trans hb
  · intro hx
    change Additive.toMul x ∈ (LocalFieldTheory.normUnits
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)).range at hx
    rcases hx with ⟨y, hy⟩
    change uK x ∈ finiteNormSubgroup
      (galoisAmbientUnitsRep k Ω) K L hLK
    refine ⟨uL (Additive.ofMul y), ?_⟩
    rw [relativeNorm_abstractFixedFieldUnit_eq_normUnits
      k Ω K L hLK y]
    exact congrArg uK (congrArg Additive.ofMul hy)

/-- The kernel of the additive fixed-field norm-residue symbol is the
ordinary norm subgroup, written additively. -/
theorem abstractFixedFieldNormResidueSymbol_ker
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    [IsSepClosed Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    (abstractFixedFieldNormResidueSymbol
      k Ω D v hcf K L hLK).ker =
      additiveNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  let A := galoisAmbientUnitsRep k Ω
  let KF : FiniteAbstractField (Gal(Ω / k)) :=
    ⟨K, hKabsolute⟩
  let E : FiniteGaloisSubextension K :=
    ⟨L, hLK, hnormal, hfinite⟩
  let q := abstractExtensionQuotientEquivGaloisGroup
    k Ω K L hLK hnormal
  let e := (D.normResidueSymbol A v hcf KF E).trans
    (MulEquiv.toAdditive q.abelianizationCongr)
  let uK := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  calc
    (abstractFixedFieldNormResidueSymbol
        k Ω D v hcf K L hLK).ker =
        (finiteNormSubgroup A K L hLK).comap
          uK.toAddMonoidHom := by
      ext x
      change e
          (finiteNormClass A K L hLK (uK x)) = 0 ↔
        uK x ∈ finiteNormSubgroup A K L hLK
      rw [e.map_eq_zero_iff]
      exact finiteNormClass_eq_zero_iff A K L hLK (uK x)
    _ = additiveNormSubgroup
          (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK) :=
      abstractFixedFieldUnitsEquiv_finiteNormSubgroup_preimage
        k Ω K L hLK

/-- The kernel of the multiplicative fixed-field norm-residue homomorphism
is the ordinary norm subgroup. -/
theorem abstractFixedFieldNormResidueMonoidHom_ker
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    [IsSepClosed Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    (abstractFixedFieldNormResidueMonoidHom
      k Ω D v hcf K L hLK).ker =
      localNormSubgroup
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  change (abstractFixedFieldNormResidueSymbol
    k Ω D v hcf K L hLK).ker.toSubgroup = _
  rw [abstractFixedFieldNormResidueSymbol_ker
    k Ω D v hcf K L hLK]
  rfl

/-- The spectral norm on a finite fixed field, with its finite-dimensional
witness supplied by the same absolute quotient as the reciprocity maps.
The relative fixed-field presentation has the same underlying field, so it
uses this provider as well. -/
@[reducible]
noncomputable def abstractFixedFieldSpectralNormedField
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (K : ClosedSubgroup (Gal(Ω/k)))
    (hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K (le_baseField K))) :
    NontriviallyNormedField (abstractFixedField k Ω K) := by
  let : FiniteDimensional k (abstractFixedField k Ω K) :=
    abstractFixedField_finiteDimensional k Ω K hKabsolute
  exact finiteExtensionSpectralNormedField k (abstractFixedField k Ω K)

/-! ## Continuous arrows -/

/-- The fixed-field norm-residue symbol, bundled as a genuinely continuous
homomorphism for the spectral topology on the source field. -/
noncomputable def abstractFixedFieldNormResidueMap
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [IsSepClosed Ω]
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    let _normed : NontriviallyNormedField (abstractFixedField k Ω K) :=
      abstractFixedFieldSpectralNormedField k Ω K hKabsolute
    (abstractFixedField k Ω K)ˣ →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K) := by
  intro _normed
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  letI : FiniteDimensional k F :=
    abstractFixedField_finiteDimensional k Ω K hKabsolute
  letI : CompleteSpace F := finiteExtensionSpectralCompleteSpace k F
  letI : ValuativeRel F := finiteExtensionSpectralValuativeRel k F
  letI : IsNonarchimedeanLocalField F :=
    finiteExtensionSpectralIsNonarchimedeanLocalField k F
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  letI : DiscreteTopology (Group.Abelianization Gal(E / F)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let f := abstractFixedFieldNormResidueMonoidHom
    k Ω D v hcf K L hLK
  refine { f with continuous_toFun := ?_ }
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one,
    @nhds_discrete (Group.Abelianization Gal(E / F)) _ _, Filter.tendsto_pure]
  have hopen : IsOpen (f.ker : Set Fˣ) := by
    rw [abstractFixedFieldNormResidueMonoidHom_ker
      k Ω D v hcf K L hLK]
    exact localNormSubgroup_isOpen F E
  exact hopen.mem_nhds f.ker.one_mem

/-- Forgetting continuity recovers the specified algebraic homomorphism. -/
@[simp] theorem abstractFixedFieldNormResidueMap_toMonoidHom
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    [IsSepClosed Ω]
    (D : DegreeData (Gal(Ω/k)))
    (v : ValuationData D (galoisAmbientUnitsRep k Ω))
    (hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω))
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup K L hLK).Normal]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    let _ : NontriviallyNormedField
        (abstractFixedField k Ω K) :=
      abstractFixedFieldSpectralNormedField k Ω K hKabsolute
    (abstractFixedFieldNormResidueMap k Ω D v hcf K L hLK).toMonoidHom =
      abstractFixedFieldNormResidueMonoidHom k Ω D v hcf K L hLK := rfl

/-- Norm on units is continuous for the two normed structures induced from a common base. -/
theorem normUnits_continuous_of_normedAlgebra_tower
    (k : Type*) (F : Type*) (F' : Type*)
    [NontriviallyNormedField k] [NontriviallyNormedField F] [NontriviallyNormedField F']
    [NormedAlgebra k F] [NormedAlgebra k F'] [Algebra F F'] [IsScalarTower k F F']
    [FiniteDimensional k F] [FiniteDimensional F F'] [CompleteSpace k] [CompleteSpace F] :
    Continuous (LocalFieldTheory.normUnits F F') := by
  let : ContinuousSMul F F' := continuousSMul_of_algebraMap F F' (by
    change Continuous (IsScalarTower.toAlgHom k F F')
    exact (IsScalarTower.toAlgHom k F F').toLinearMap.continuous_of_finiteDimensional)
  exact normUnits_continuous_of_finiteDimensional F F'

/-- The ordinary norm on fixed-field units, continuously bundled for the
two spectral topologies extended from the original local field. -/
noncomputable def abstractFixedFieldNormUnitsMap
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K'
          (le_baseField K'))]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)] :
    let _normed : NontriviallyNormedField (abstractFixedField k Ω K) :=
      abstractFixedFieldSpectralNormedField k Ω K hKabsolute
    let _normed' : NontriviallyNormedField (abstractRelativeFixedField k Ω hK'K) :=
      abstractFixedFieldSpectralNormedField k Ω K' hK'absolute
    (abstractRelativeFixedField k Ω hK'K)ˣ →ₜ*
      (abstractFixedField k Ω K)ˣ := by
  intro _normed _normed'
  let F : Type := abstractFixedField k Ω K
  let F' : Type := abstractRelativeFixedField k Ω hK'K
  let nF : NontriviallyNormedField F := _normed
  let nF' : NontriviallyNormedField F' := _normed'
  let aFF' : Algebra F F' := (abstractRelativeFixedField k Ω hK'K).algebra
  let hFk : FiniteDimensional k F :=
    abstractFixedField_finiteDimensional k Ω K hKabsolute
  let : FiniteDimensional k F' :=
    abstractFixedField_finiteDimensional k Ω K' hK'absolute
  let hFinite : FiniteDimensional F F' :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K K' hK'K hKabsolute hK'Kfinite
  let cF : CompleteSpace F := finiteExtensionSpectralCompleteSpace k F
  let nk : NontriviallyNormedField k := localFieldNontriviallyNormedField k
  let : IsUltrametricDist k := localFieldIsUltrametricDist k
  let ck : CompleteSpace k := inferInstance
  let naF : NormedAlgebra k F := spectralNorm.normedAlgebra k F
  let naF' : NormedAlgebra k F' := spectralNorm.normedAlgebra k F'
  let hTower : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq' rfl
  let f := abstractFixedFieldNormUnitsMonoidHom
    k Ω K K' hK'K
  refine { f with continuous_toFun := ?_ }
  exact @normUnits_continuous_of_normedAlgebra_tower k F F' nk nF nF'
    naF naF' aFF' hTower hFk hFinite ck cF

/-- Forgetting continuity recovers the specified algebraic homomorphism. -/
@[simp] theorem abstractFixedFieldNormUnitsMap_toMonoidHom
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K'
          (le_baseField K'))]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K K' hK'K)] :
    let _ : NontriviallyNormedField
        (abstractFixedField k Ω K) :=
      abstractFixedFieldSpectralNormedField k Ω K hKabsolute
    let _ : NontriviallyNormedField
        (abstractRelativeFixedField k Ω hK'K) :=
      abstractFixedFieldSpectralNormedField k Ω K' hK'absolute
    (abstractFixedFieldNormUnitsMap k Ω K K' hK'K).toMonoidHom =
      abstractFixedFieldNormUnitsMonoidHom k Ω K K' hK'K := rfl

/-- Inclusion of fixed-field units, continuously bundled for the two
spectral topologies extended from the original local field. -/
noncomputable def abstractFixedFieldUnitsInclusionMap
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K'
          (le_baseField K'))] :
    let _normed : NontriviallyNormedField (abstractFixedField k Ω K) :=
      abstractFixedFieldSpectralNormedField k Ω K hKabsolute
    let _normed' : NontriviallyNormedField (abstractFixedField k Ω K') :=
      abstractFixedFieldSpectralNormedField k Ω K' hK'absolute
    (abstractFixedField k Ω K)ˣ →ₜ*
      (abstractFixedField k Ω K')ˣ := by
  intro _normed _normed'
  let F := abstractFixedField k Ω K
  let F' := abstractFixedField k Ω K'
  letI : FiniteDimensional k F :=
    abstractFixedField_finiteDimensional k Ω K hKabsolute
  letI : FiniteDimensional k F' :=
    abstractFixedField_finiteDimensional k Ω K' hK'absolute
  letI : NontriviallyNormedField k :=
    localFieldNontriviallyNormedField k
  letI : IsUltrametricDist k := localFieldIsUltrametricDist k
  letI : CompleteSpace k := inferInstance
  letI : NormedSpace k F := spectralNorm.normedSpace k F
  letI : NormedSpace k F' := spectralNorm.normedSpace k F'
  let f := abstractFixedFieldUnitsInclusionMonoidHom
    k Ω K K' hK'K
  refine { f with continuous_toFun := ?_ }
  exact Continuous.units_map _
    (IntermediateField.inclusion
      (abstractFixedField_le k Ω hK'K)).toLinearMap.continuous_of_finiteDimensional

/-- Forgetting continuity recovers the specified algebraic homomorphism. -/
@[simp] theorem abstractFixedFieldUnitsInclusionMap_toMonoidHom
    [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (K K' : ClosedSubgroup (Gal(Ω/k)))
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K'
          (le_baseField K'))] :
    let _ : NontriviallyNormedField
        (abstractFixedField k Ω K) :=
      abstractFixedFieldSpectralNormedField k Ω K hKabsolute
    let _ : NontriviallyNormedField
        (abstractFixedField k Ω K') :=
      abstractFixedFieldSpectralNormedField k Ω K' hK'absolute
    (abstractFixedFieldUnitsInclusionMap k Ω K K' hK'K).toMonoidHom =
      abstractFixedFieldUnitsInclusionMonoidHom k Ω K K' hK'K := rfl

/-- Abelianized restriction, continuously bundled for the finite native
Krull quotient topologies. -/
noncomputable def abstractFixedFieldAbelianizedRestrictionMap
    (K K' L L' : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K'
          (le_baseField K'))] :
    Group.Abelianization
        Gal(abstractRelativeFixedField k Ω hL'K' /
          abstractFixedField k Ω K') →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k Ω hLK /
          abstractFixedField k Ω K) := by
  let F' := abstractFixedField k Ω K'
  let E' := abstractRelativeFixedField k Ω hL'K'
  letI : FiniteDimensional F' E' :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K' L' hL'K' hK'absolute hL'K'finite
  letI : IsGalois F' E' :=
    abstractRelativeFixedField_isGalois
      k Ω K' L' hL'K' hL'normal
  letI : DiscreteTopology (Group.Abelianization Gal(E' / F')) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let f := abstractFixedFieldAbelianizedRestrictionMonoidHom
    k Ω K K' L L' hLK hL'K' hK'K hL'L
  exact { f with continuous_toFun := continuous_of_discreteTopology }

/-- Forgetting continuity recovers the specified algebraic homomorphism. -/
@[simp] theorem abstractFixedFieldAbelianizedRestrictionMap_toMonoidHom
    (K K' L L' : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K')]
    [hK'absolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K'
          (le_baseField K'))] :
    (abstractFixedFieldAbelianizedRestrictionMap k Ω K K' L L' hLK hL'K' hK'K hL'L).toMonoidHom =
      abstractFixedFieldAbelianizedRestrictionMonoidHom k Ω K K' L L' hLK hL'K' hK'K hL'L := rfl

/-- Abelianized transfer, continuously bundled for the finite native Krull
quotient topologies. -/
noncomputable def abstractFixedFieldAbelianizedTransferMap
    (K K' L : ClosedSubgroup (Gal(Ω/k)))
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K))]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    let : (extensionSubgroup K' L hLK').Normal :=
      transferNormNaturality_intermediateExtension_normal
        K K' L hLK' hK'K
    let : Finite
        (K'.toSubgroup ⧸ extensionSubgroup K' L hLK') :=
      FiniteGaloisSubextension.finite_extension_over_intermediate
        (hLK'.trans hK'K) hK'K hLK'
    Group.Abelianization
        Gal(abstractRelativeFixedField k Ω
            (hLK'.trans hK'K) /
          abstractFixedField k Ω K) →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k Ω hLK' /
          abstractFixedField k Ω K') := by
  intro sharedOwner1 sharedOwner2
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω
    (hLK'.trans hK'K)
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L (hLK'.trans hK'K) hKabsolute hLfinite
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      k Ω K L (hLK'.trans hK'K) hLnormal
  letI : DiscreteTopology (Group.Abelianization Gal(E / F)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  let f := abstractFixedFieldAbelianizedTransferMonoidHom
    k Ω K K' L hLK' hK'K
  exact { f with continuous_toFun := continuous_of_discreteTopology }

/-- Forgetting continuity recovers the specified algebraic homomorphism. -/
@[simp] theorem abstractFixedFieldAbelianizedTransferMap_toMonoidHom
    (K K' L : ClosedSubgroup (Gal(Ω/k)))
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (extensionSubgroup K L (hLK'.trans hK'K)).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸
        extensionSubgroup K L (hLK'.trans hK'K))]
    [hKabsolute : Finite
      ((baseField (Gal(Ω/k))).toSubgroup ⧸
        extensionSubgroup (baseField (Gal(Ω/k))) K
          (le_baseField K))] :
    (abstractFixedFieldAbelianizedTransferMap k Ω K K' L hLK' hK'K).toMonoidHom =
      abstractFixedFieldAbelianizedTransferMonoidHom k Ω K K' L hLK' hK'K := rfl

/-! ## Continuous norm--restriction square -/

namespace LocalFixedFieldNormRestrictionSquare

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The standard spectral norm at the `lowerBase` endpoint of this diagram. -/
@[reducible]
noncomputable def lowerBaseSpectralNormedField
    (T : LocalFixedFieldNormRestrictionSquare k) :
    NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
  abstractFixedFieldSpectralNormedField k (SeparableClosure k) T.lowerBase
    T.lowerAbsoluteFinite

/-- The standard spectral norm at the `upperBase` endpoint of this diagram. -/
@[reducible]
noncomputable def upperBaseSpectralNormedField
    (T : LocalFixedFieldNormRestrictionSquare k) :
    NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.upperBase) :=
  abstractFixedFieldSpectralNormedField k (SeparableClosure k) T.upperBase
    (upperAbsoluteFinite T)

/-- The lower horizontal norm-residue arrow as a continuous homomorphism. -/
noncomputable def lowerNormResidueMap
    (T : LocalFixedFieldNormRestrictionSquare k) :
    let _lowerNormed : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.lowerBase) := T.lowerBaseSpectralNormedField
    (abstractFixedField k (SeparableClosure k) T.lowerBase)ˣ →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
            T.lowerTop_le_lowerBase /
          abstractFixedField k (SeparableClosure k) T.lowerBase) := by
  intro _lowerNormed
  letI := T.lowerNormal
  letI := T.lowerFinite
  letI := T.lowerAbsoluteFinite
  exact abstractFixedFieldNormResidueMap
    k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.lowerBase T.lowerTop T.lowerTop_le_lowerBase

/-- Forgetting continuity recovers the lower algebraic norm-residue map. -/
@[simp] theorem lowerNormResidueMap_toMonoidHom
    (T : LocalFixedFieldNormRestrictionSquare k) :
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      T.lowerBaseSpectralNormedField
    (lowerNormResidueMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (lowerNormResidueSymbol T) := rfl

/-- The upper horizontal norm-residue arrow as a continuous homomorphism. -/
noncomputable def upperNormResidueMap
    (T : LocalFixedFieldNormRestrictionSquare k) :
    let _upperNormed : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.upperBase) := T.upperBaseSpectralNormedField
    (abstractFixedField k (SeparableClosure k) T.upperBase)ˣ →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
            T.upperTop_le_upperBase /
          abstractFixedField k (SeparableClosure k) T.upperBase) := by
  intro _upperNormed
  letI := T.upperNormal
  letI := T.upperFinite
  letI := upperAbsoluteFinite T
  exact abstractFixedFieldNormResidueMap
    k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.upperBase T.upperTop T.upperTop_le_upperBase

/-- Forgetting continuity recovers the upper algebraic norm-residue map. -/
@[simp] theorem upperNormResidueMap_toMonoidHom
    (T : LocalFixedFieldNormRestrictionSquare k) :
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.upperBase) :=
      T.upperBaseSpectralNormedField
    (upperNormResidueMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (upperNormResidueSymbol T) := rfl

/-- The vertical ordinary norm arrow as a continuous homomorphism. -/
noncomputable def normUnitsMap
    (T : LocalFixedFieldNormRestrictionSquare k) :
    let _lowerNormed : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.lowerBase) := T.lowerBaseSpectralNormedField
    let _upperNormed : NontriviallyNormedField
      (abstractRelativeFixedField k (SeparableClosure k)
        T.upperBase_le_lowerBase) := T.upperBaseSpectralNormedField
    (abstractRelativeFixedField k (SeparableClosure k)
        T.upperBase_le_lowerBase)ˣ →ₜ*
      (abstractFixedField k (SeparableClosure k) T.lowerBase)ˣ := by
  intro _lowerNormed _upperNormed
  letI := T.lowerAbsoluteFinite
  letI := upperAbsoluteFinite T
  letI := T.baseFinite
  exact abstractFixedFieldNormUnitsMap
    k (SeparableClosure k)
    T.lowerBase T.upperBase T.upperBase_le_lowerBase

/-- Forgetting continuity recovers the algebraic norm on units. -/
@[simp] theorem normUnitsMap_toMonoidHom
    (T : LocalFixedFieldNormRestrictionSquare k) :
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      T.lowerBaseSpectralNormedField
    let _ : NontriviallyNormedField
        (abstractRelativeFixedField k (SeparableClosure k) T.upperBase_le_lowerBase) :=
      T.upperBaseSpectralNormedField
    (normUnitsMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (normUnits T) := rfl

/-- The vertical abelianized restriction arrow as a continuous
homomorphism. -/
noncomputable def abelianizedRestrictionMap
    (T : LocalFixedFieldNormRestrictionSquare k) :
    Group.Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k) T.upperTop_le_upperBase /
          abstractFixedField k (SeparableClosure k) T.upperBase) →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k) T.lowerTop_le_lowerBase /
          abstractFixedField k (SeparableClosure k) T.lowerBase) := by
  letI := T.lowerNormal
  letI := T.upperNormal
  letI := T.upperFinite
  letI := upperAbsoluteFinite T
  exact abstractFixedFieldAbelianizedRestrictionMap
    k (SeparableClosure k)
    T.lowerBase T.upperBase T.lowerTop T.upperTop
    T.lowerTop_le_lowerBase T.upperTop_le_upperBase
    T.upperBase_le_lowerBase T.upperTop_le_lowerTop

/-- Forgetting continuity recovers algebraic abelianized restriction. -/
@[simp] theorem abelianizedRestrictionMap_toMonoidHom
    (T : LocalFixedFieldNormRestrictionSquare k) :
    (abelianizedRestrictionMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (abelianizedRestriction T) := rfl

/-- Norm--restriction naturality as a commuting square of continuous
homomorphisms. -/
theorem norm_restriction_commutes_continuous
    (T : LocalFixedFieldNormRestrictionSquare k) :
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.lowerBase) :=
      T.lowerBaseSpectralNormedField
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.upperBase) :=
      T.upperBaseSpectralNormedField
    let _ : NontriviallyNormedField
        (abstractRelativeFixedField k (SeparableClosure k) T.upperBase_le_lowerBase) :=
      T.upperBaseSpectralNormedField
    (abelianizedRestrictionMap T).comp (upperNormResidueMap T) =
      (lowerNormResidueMap T).comp (normUnitsMap T) := by
  intro _lowerNormed _upperNormed _relativeNormed
  apply ContinuousMonoidHom.ext
  intro x
  change (abelianizedRestrictionMap T).toMonoidHom ((upperNormResidueMap T).toMonoidHom x) =
    (lowerNormResidueMap T).toMonoidHom ((normUnitsMap T).toMonoidHom x)
  let restriction := MonoidHom.toAdditive.symm (abelianizedRestriction T)
  let lower := MonoidHom.toAdditive.symm (lowerNormResidueSymbol T)
  let upper := MonoidHom.toAdditive.symm (upperNormResidueSymbol T)
  let norm := MonoidHom.toAdditive.symm (normUnits T)
  calc
    _ = restriction ((upperNormResidueMap T).toMonoidHom x) :=
      DFunLike.congr_fun (abelianizedRestrictionMap_toMonoidHom T) _
    _ = restriction (upper x) :=
      congrArg restriction (DFunLike.congr_fun (upperNormResidueMap_toMonoidHom T) x)
    _ = lower (norm x) := congrArg Additive.toMul
      (DFunLike.congr_fun (norm_restriction_commutes T) (Additive.ofMul x))
    _ = lower ((normUnitsMap T).toMonoidHom x) :=
      congrArg lower (DFunLike.congr_fun (normUnitsMap_toMonoidHom T) x).symm
    _ = _ := (DFunLike.congr_fun (lowerNormResidueMap_toMonoidHom T) _).symm

end LocalFixedFieldNormRestrictionSquare

/-! ## Continuous transfer--inclusion square -/

namespace LocalFixedFieldTransferTower

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- The standard spectral norm at the `base` endpoint of this diagram. -/
@[reducible]
noncomputable def baseSpectralNormedField
    (T : LocalFixedFieldTransferTower k) :
    NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.base) :=
  abstractFixedFieldSpectralNormedField k (SeparableClosure k) T.base
    T.baseAbsoluteFinite

/-- The standard spectral norm at the `intermediate` endpoint of this diagram. -/
@[reducible]
noncomputable def intermediateSpectralNormedField
    (T : LocalFixedFieldTransferTower k) :
    NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.intermediate) :=
  abstractFixedFieldSpectralNormedField k (SeparableClosure k) T.intermediate
    (intermediateAbsoluteFinite T)

/-- The total horizontal norm-residue arrow as a continuous homomorphism. -/
noncomputable def baseNormResidueMap
    (T : LocalFixedFieldTransferTower k) :
    let _baseNormed : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.base) := T.baseSpectralNormedField
    (abstractFixedField k (SeparableClosure k) T.base)ˣ →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
            (T.top_le_intermediate.trans T.intermediate_le_base) /
          abstractFixedField k (SeparableClosure k) T.base) := by
  intro _baseNormed
  letI := T.totalNormal
  letI := T.totalFinite
  letI := T.baseAbsoluteFinite
  exact abstractFixedFieldNormResidueMap
    k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.base T.top
    (T.top_le_intermediate.trans T.intermediate_le_base)

/-- Forgetting continuity recovers the total algebraic norm-residue map. -/
@[simp] theorem baseNormResidueMap_toMonoidHom
    (T : LocalFixedFieldTransferTower k) :
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      T.baseSpectralNormedField
    (baseNormResidueMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (baseNormResidueSymbol T) := rfl

/-- The intermediate horizontal norm-residue arrow as a continuous
homomorphism. -/
noncomputable def intermediateNormResidueMap
    (T : LocalFixedFieldTransferTower k) :
    let _intermediateNormed : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      T.intermediateSpectralNormedField
    (abstractFixedField k (SeparableClosure k) T.intermediate)ˣ →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
            T.top_le_intermediate /
          abstractFixedField k (SeparableClosure k) T.intermediate) := by
  intro _intermediateNormed
  letI := intermediateNormal T
  letI := intermediateFinite T
  letI := intermediateAbsoluteFinite T
  exact abstractFixedFieldNormResidueMap
    k (SeparableClosure k)
    (localResidueDatum k) (localHenselianValuation k)
    (separableClosureUnits_isClassFormation k)
    T.intermediate T.top T.top_le_intermediate

/-- Forgetting continuity recovers the intermediate norm-residue map. -/
@[simp] theorem intermediateNormResidueMap_toMonoidHom
    (T : LocalFixedFieldTransferTower k) :
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      T.intermediateSpectralNormedField
    (intermediateNormResidueMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (intermediateNormResidueSymbol T) := rfl

/-- The vertical inclusion of fixed-field units as a continuous
homomorphism. -/
noncomputable def unitsInclusionMap
    (T : LocalFixedFieldTransferTower k) :
    let _baseNormed : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.base) := T.baseSpectralNormedField
    let _intermediateNormed : NontriviallyNormedField
      (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      T.intermediateSpectralNormedField
    (abstractFixedField k (SeparableClosure k) T.base)ˣ →ₜ*
      (abstractFixedField k (SeparableClosure k) T.intermediate)ˣ := by
  intro _baseNormed _intermediateNormed
  letI := T.baseAbsoluteFinite
  letI := intermediateAbsoluteFinite T
  exact abstractFixedFieldUnitsInclusionMap
    k (SeparableClosure k)
    T.base T.intermediate T.intermediate_le_base

/-- Forgetting continuity recovers algebraic inclusion of fixed-field units. -/
@[simp] theorem unitsInclusionMap_toMonoidHom
    (T : LocalFixedFieldTransferTower k) :
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      T.baseSpectralNormedField
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      T.intermediateSpectralNormedField
    (unitsInclusionMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (unitsInclusion T) := rfl

/-- The vertical abelianized transfer arrow as a continuous homomorphism. -/
noncomputable def abelianizedTransferMap
    (T : LocalFixedFieldTransferTower k) :
    Group.Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k)
          (T.top_le_intermediate.trans T.intermediate_le_base) /
          abstractFixedField k (SeparableClosure k) T.base) →ₜ*
      Group.Abelianization
        Gal(abstractRelativeFixedField k (SeparableClosure k) T.top_le_intermediate /
          abstractFixedField k (SeparableClosure k) T.intermediate) := by
  letI := T.totalNormal
  letI := T.totalFinite
  letI := T.baseAbsoluteFinite
  exact abstractFixedFieldAbelianizedTransferMap
    k (SeparableClosure k)
    T.base T.intermediate T.top
    T.top_le_intermediate T.intermediate_le_base

/-- Forgetting continuity recovers algebraic abelianized transfer. -/
@[simp] theorem abelianizedTransferMap_toMonoidHom
    (T : LocalFixedFieldTransferTower k) :
    (abelianizedTransferMap T).toMonoidHom =
      MonoidHom.toAdditive.symm (abelianizedTransfer T) := rfl

/-- Transfer--inclusion naturality as a commuting square of continuous
homomorphisms. -/
theorem transfer_inclusion_commutes_continuous
    (T : LocalFixedFieldTransferTower k) :
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.base) :=
      T.baseSpectralNormedField
    let _ : NontriviallyNormedField
        (abstractFixedField k (SeparableClosure k) T.intermediate) :=
      T.intermediateSpectralNormedField
    (abelianizedTransferMap T).comp (baseNormResidueMap T) =
      (intermediateNormResidueMap T).comp (unitsInclusionMap T) := by
  intro _baseNormed _intermediateNormed
  apply ContinuousMonoidHom.ext
  intro x
  change (abelianizedTransferMap T).toMonoidHom ((baseNormResidueMap T).toMonoidHom x) =
    (intermediateNormResidueMap T).toMonoidHom ((unitsInclusionMap T).toMonoidHom x)
  let transfer := MonoidHom.toAdditive.symm (abelianizedTransfer T)
  let base := MonoidHom.toAdditive.symm (baseNormResidueSymbol T)
  let intermediate := MonoidHom.toAdditive.symm (intermediateNormResidueSymbol T)
  let inclusion := MonoidHom.toAdditive.symm (unitsInclusion T)
  calc
    _ = transfer ((baseNormResidueMap T).toMonoidHom x) :=
      DFunLike.congr_fun (abelianizedTransferMap_toMonoidHom T) _
    _ = transfer (base x) :=
      congrArg transfer (DFunLike.congr_fun (baseNormResidueMap_toMonoidHom T) x)
    _ = intermediate (inclusion x) := congrArg Additive.toMul
      (DFunLike.congr_fun (transfer_inclusion_commutes T) (Additive.ofMul x))
    _ = intermediate ((unitsInclusionMap T).toMonoidHom x) :=
      congrArg intermediate (DFunLike.congr_fun (unitsInclusionMap_toMonoidHom T) x).symm
    _ = _ := (DFunLike.congr_fun (intermediateNormResidueMap_toMonoidHom T) _).symm

end LocalFixedFieldTransferTower

end LocalClassFieldTheory
