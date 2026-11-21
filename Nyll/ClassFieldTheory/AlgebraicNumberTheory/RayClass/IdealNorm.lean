/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FinitePlaceContraction

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNormCore
public import Mathlib.Algebra.Group.Subgroup.Map
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNormExponentMap
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization
public import Nyll.ValuedFieldTheory.LocalField.NormUnits
public import Nyll.ValuedFieldTheory.Valuation.Completion.AbsoluteValueExtensions
public import Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition

/-!
# Norms of ideals prime to a modulus

For a finite extension `L / K`, the norm of a prime of `L`
above `v` is `v` raised to the inertia degree.  Extending this rule
multiplicatively gives the genuine norm on nonzero fractional ideals.

If `m` is a modulus of `K`, a modulus upstairs is chosen deeply enough
at every prime above `m` that local norms preserve the prescribed
higher-unit conditions.  The norm therefore restricts to the groups of
fractional ideals prime to these moduli.  Its image, together with the
principal ray ideals, is the norm-defined ideal group
`N_{L/K} J_L^m P_K^m`.
-/



@[expose] public section

universe u v w

open scoped BigOperators NumberField Topology
open ClassFieldTheory
open NumberField IsDedekindDomain

noncomputable section

namespace RayClass

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- At a prime `W` above `v`, a sufficiently deep higher-unit group
has norm contained in the higher-unit group prescribed by `m` at `v`.
This is the source of the lifted modulus used for ideal norms. -/
theorem exists_localHigherUnitGroup_le_norm_preimage
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    let v := _root_.finitePlaceBelow (K := K) W
    let : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
      (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
    ∃ n : ℕ,
      ClassFieldTheory.rayLocalHigherUnitGroup W n ≤
        (ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v)).comap
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion L)) := by
  intro v sharedOwner2
  classical
  let : IsScalarTower
      K (v.adicCompletion K) (W.adicCompletion L) :=
    _root_.finitePlaceAdicCompletionMap_isScalarTower K L v ⟨W, rfl⟩
  let : ContinuousSMul
      (v.adicCompletion K) (W.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (by
      change Continuous
        (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩)
      exact
        _root_.finitePlaceAdicCompletionMap_continuous
          K L v ⟨W, rfl⟩)
  let : FiniteDimensional
      (v.adicCompletion K) (W.adicCompletion L) :=
    inferInstance
  let : NontriviallyNormedField (v.adicCompletion K) :=
    NontriviallyNormedField.ofNormNeOne (by
      obtain ⟨ϖ, hϖ⟩ :=
        IsDiscreteValuationRing.exists_irreducible
          (v.adicCompletionIntegers K)
      refine ⟨(ϖ : v.adicCompletion K), ?_, ?_⟩
      · intro h
        exact hϖ.ne_zero (Subtype.ext h)
      · exact ne_of_lt (local_irreducible_norm_lt_one v hϖ))
  let U : Set (W.adicCompletion L)ˣ :=
    (LocalFieldTheory.normUnits
      (v.adicCompletion K) (W.adicCompletion L)) ⁻¹'
        (ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ)
  have hTarget :
      (ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ) ∈
        𝓝 (1 : (v.adicCompletion K)ˣ) :=
    (ClassFieldTheory.isOpen_rayLocalHigherUnitGroup v (m.finitePart v)).mem_nhds
      (ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v)).one_mem
  have hU : U ∈ 𝓝 (1 : (W.adicCompletion L)ˣ) := by
    have hcont :=
      LocalFieldTheory.normUnits_continuous_of_finiteDimensional
        (v.adicCompletion K) (W.adicCompletion L)
    have hTarget' :
        (ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ) ∈
          𝓝 (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion L) 1) := by
      simpa using hTarget
    simpa [U] using hcont.continuousAt hTarget'
  obtain ⟨n, hn⟩ :=
    exists_localHigherUnitGroup_subset W hU
  refine ⟨n, ?_⟩
  intro x hx
  exact hn hx

open scoped Classical in
omit [FiniteDimensional K L] in
/-- The positive local depth used at `W` in the lifted modulus.  It is
zero precisely away from the inverse image of the support of `m`. -/
noncomputable def idealNormLiftedModulusExponent
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) : ℕ :=
  if _ :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support then
    Nat.find
        (exists_localHigherUnitGroup_le_norm_preimage
          (K := K) (L := L) m W) + 1
  else
    0

omit [FiniteDimensional K L] in
theorem idealNormLiftedModulusExponent_pos
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support) :
    0 < idealNormLiftedModulusExponent
      (K := K) (L := L) m W := by
  rw [idealNormLiftedModulusExponent, dite_eq_left hW]
  exact Nat.zero_lt_succ _

omit [FiniteDimensional K L] in
/-- The chosen positive depth still has the required local norm
property. -/
theorem localHigherUnitGroup_idealNormLiftedModulusExponent_le
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support) :
    let v := _root_.finitePlaceBelow (K := K) W
    let : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
      (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
    ClassFieldTheory.rayLocalHigherUnitGroup W
        (idealNormLiftedModulusExponent
          (K := K) (L := L) m W) ≤
      (ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v)).comap
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.adicCompletion L)) := by
  intro v sharedOwner2
  classical
  rw [idealNormLiftedModulusExponent, dite_eq_left hW]
  exact
    (ClassFieldTheory.rayLocalHigherUnitGroup_antitone W (Nat.le_succ _)).trans
      (Nat.find_spec
        (exists_localHigherUnitGroup_le_norm_preimage
          (K := K) (L := L) m W))

omit [FiniteDimensional K L] in
/-- At a prime above the support, the selected positive depth is at most the
successor of every depth having the required local norm property. -/
theorem idealNormLiftedModulusExponent_min
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support)
    (r : ℕ)
    (hr :
      let v := _root_.finitePlaceBelow (K := K) W
      letI : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
        (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
      ClassFieldTheory.rayLocalHigherUnitGroup W r ≤
        (ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v)).comap
          (LocalFieldTheory.normUnits
            (v.adicCompletion K) (W.adicCompletion L))) :
    idealNormLiftedModulusExponent (K := K) (L := L) m W ≤ r + 1 := by
  classical
  let v := _root_.finitePlaceBelow (K := K) W
  let : Algebra (v.adicCompletion K) (W.adicCompletion L) :=
    (_root_.finitePlaceAdicCompletionMap K L v ⟨W, rfl⟩).toAlgebra
  rw [idealNormLiftedModulusExponent, dite_eq_left hW]
  exact Nat.add_le_add_right
    (Nat.find_min'
      (exists_localHigherUnitGroup_le_norm_preimage
        (K := K) (L := L) m W) hr) 1

omit [FiniteDimensional K L] in
/-- Away from the pulled-back support, the lifted exponent is zero. -/
@[simp]
theorem idealNormLiftedModulusExponent_eq_zero_of_not_mem
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L))
    (hW :
      _root_.finitePlaceBelow (K := K) W ∉ m.finitePart.support) :
    idealNormLiftedModulusExponent (K := K) (L := L) m W = 0 := by
  rw [idealNormLiftedModulusExponent, dite_eq_right hW]

omit [FiniteDimensional K L] in
/-- The finite set of primes upstairs lying over the support of `m`. -/
def idealNormLiftedSupport (m : Modulus K) :
    Set (HeightOneSpectrum (𝓞 L)) :=
  {W |
    _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support}

omit [FiniteDimensional K L] in
/-- The inverse image of the finite support of a modulus is finite. -/
theorem idealNormLiftedSupport_finite (m : Modulus K) :
    (idealNormLiftedSupport (K := K) (L := L) m).Finite := by
  exact
    _root_.Set.Finite.preimage_finitePlaceBelow
      (K := K) (L := L) m.finitePart.support.finite_toSet

/-- A modulus upstairs whose local higher-unit conditions are carried
by the field norm into the conditions of `m`. -/
noncomputable def idealNormLiftedModulus
    (m : Modulus K) : Modulus L :=
  Modulus.ofFinite <|
    Finsupp.onFinset
      (idealNormLiftedSupport_finite
        (K := K) (L := L) m).toFinset
      (idealNormLiftedModulusExponent
        (K := K) (L := L) m)
      (by
        intro W hW
        rw [Set.Finite.mem_toFinset]
        by_contra hbelow
        apply hW
        rw [idealNormLiftedModulusExponent, dite_eq_right]
        exact hbelow)

omit [FiniteDimensional K L] in
@[simp]
theorem idealNormLiftedModulus_apply
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    (idealNormLiftedModulus (K := K) (L := L) m).finitePart W =
      idealNormLiftedModulusExponent
        (K := K) (L := L) m W :=
  rfl

omit [FiniteDimensional K L] in
@[simp]
theorem mem_idealNormLiftedModulus_support_iff
    (m : Modulus K)
    (W : HeightOneSpectrum (𝓞 L)) :
    W ∈ (idealNormLiftedModulus
        (K := K) (L := L) m).finitePart.support ↔
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support := by
  rw [Finsupp.mem_support_iff, idealNormLiftedModulus_apply]
  by_cases hW :
      _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support
  · rw [idealNormLiftedModulusExponent, dite_eq_left hW]
    exact ⟨fun _ => hW, fun _ => Nat.succ_ne_zero _⟩
  · simp [idealNormLiftedModulusExponent, hW]

omit [FiniteDimensional K L] in
/-- The chosen local depths have exactly the support of the ordinary norm domain. -/
theorem primeToModulusIdeals_idealNormLiftedModulus (m : Modulus K) :
    primeToModulusIdeals (idealNormLiftedModulus (K := K) (L := L) m) =
      primeToModulusIdealNormDomain (L := L) m := by
  apply Subgroup.ext
  intro I
  change (∀ W, W ∈ (idealNormLiftedModulus (K := K) (L := L) m).finitePart.support →
      FractionalIdeal.count L W (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 0) ↔
    (∀ W, _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support →
      FractionalIdeal.count L W (I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = 0)
  simp only [mem_idealNormLiftedModulus_support_iff]

/-- Identify the lifted-modulus ideal group with the canonical norm domain. -/
noncomputable def idealNormLiftedDomainEquiv (m : Modulus K) :
    primeToModulusIdeals (idealNormLiftedModulus (K := K) (L := L) m) ≃*
      primeToModulusIdealNormDomain (L := L) m :=
  MulEquiv.subgroupCongr (primeToModulusIdeals_idealNormLiftedModulus m)

/-- The exponent of the fractional ideal attached to an idèle is its
finite local order. -/
@[simp]
theorem _root_.IdeleGroup.count_fractionalIdeal
    (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        (IdeleGroup.fractionalIdeal a :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (FiniteIdeleGroup.localOrder v
        (IdeleGroup.finiteComponent v a)).toAdd := by
  change
    FractionalIdeal.count K v
        (((NumberFieldFractionalIdealGroup.factorization (K := K))
          (FiniteIdeleGroup.valuationVector (IdeleGroup.finiteCoordinates a)) :
            NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      _
  rw [NumberFieldFractionalIdealGroup.count_factorization]
  rfl

/-- The genuine ideal norm is the fractional-ideal image of the
ordinary idèle norm. -/
theorem _root_.IdeleGroup.fractionalIdeal_ideleNorm
    (a : IdeleGroup L) :
    IdeleGroup.fractionalIdeal (IdeleGroup.norm K L a) =
      ClassFieldTheory.fractionalIdealNorm K L
        (IdeleGroup.fractionalIdeal a) := by
  classical
  apply NumberFieldFractionalIdealGroup.ext_count
  intro v
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    adicAbv_isNontrivial v
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v
  let :=
    AlgebraicNumberTheory.Valuations.completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv
      (AlgebraicNumberTheory.Valuations.AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v},
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (_root_.finitePlaceAdicCompletionMap K L v W).toAlgebra
  rw [IdeleGroup.count_fractionalIdeal,
    count_fractionalIdealNorm]
  rw [IdeleGroup.finiteComponent_norm_eq_prod]
  rw [map_prod, toAdd_prod]
  change
    (∑ W : {W : HeightOneSpectrum (𝓞 L) //
        _root_.finitePlaceBelow (K := K) W = v},
      (FiniteIdeleGroup.localOrder v
        (LocalFieldTheory.normUnits
          (v.adicCompletion K) (W.1.adicCompletion L)
          (IdeleGroup.finiteComponent W.1 a))).toAdd) =
      _
  rw [idealNormExponentMap_apply_eq_sum_above]
  apply Finset.sum_congr rfl
  intro W _hW
  rw [FiniteIdeleGroup.localOrder_normUnits K L v W]
  rw [NumberFieldFractionalIdealGroup.countVector_apply,
    IdeleGroup.count_fractionalIdeal]

/-- The finite component of an idèle prime to the lifted modulus has
norm satisfying the finite prime-to conditions of the base modulus. -/
theorem finite_norm_mem_finitePrimeToModulusSubgroup
    (m : Modulus K)
    (a : idelePrimeToModulusSubgroup
      (idealNormLiftedModulus (K := K) (L := L) m)) :
    (IdeleGroup.finiteCoordinates (IdeleGroup.norm K L (a : IdeleGroup L))) ∈
      finitePrimeToModulusSubgroup m := by
  classical
  intro v hv
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    adicAbv_isNontrivial v
  let eAbove :=
    finitePlaceExtensionEquivAbove
      (K := K) (L := L) v
  let :=
    AlgebraicNumberTheory.Valuations.completionTensorDecomposition_extensionFintype
      (K := K) (L := L) vK hvK
  let : Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v} :=
    Fintype.ofEquiv
      (AlgebraicNumberTheory.Valuations.AbsoluteValueExtension vK L) eAbove
  let : ∀ W : {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v},
      Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
    fun W =>
      (_root_.finitePlaceAdicCompletionMap K L v W).toAlgebra
  change IdeleGroup.finiteComponent v
      (IdeleGroup.norm K L (a : IdeleGroup L)) ∈
        ClassFieldTheory.rayLocalHigherUnitGroup v (m.finitePart v)
  rw [IdeleGroup.finiteComponent_norm_eq_prod]
  apply Subgroup.prod_mem
  rintro ⟨W, rfl⟩ _
  have hnorm :=
    localHigherUnitGroup_idealNormLiftedModulusExponent_le
      (K := K) (L := L) m W hv
  have hmem := hnorm
    (a.property.2 W
      ((mem_idealNormLiftedModulus_support_iff
        (K := K) (L := L) m W).2 hv))
  let : Algebra
      ((_root_.finitePlaceBelow (K := K) W).adicCompletion K)
      (W.adicCompletion L) :=
    (_root_.finitePlaceAdicCompletionMap K L
      (_root_.finitePlaceBelow (K := K) W) ⟨W, rfl⟩).toAlgebra
  change
    LocalFieldTheory.normUnits
      ((_root_.finitePlaceBelow (K := K) W).adicCompletion K)
      (W.adicCompletion L)
      (IdeleGroup.finiteComponent W (a : IdeleGroup L)) ∈
        ClassFieldTheory.rayLocalHigherUnitGroup
          (_root_.finitePlaceBelow (K := K) W)
          (m.finitePart (_root_.finitePlaceBelow (K := K) W)) at hmem
  exact hmem


end RayClass
