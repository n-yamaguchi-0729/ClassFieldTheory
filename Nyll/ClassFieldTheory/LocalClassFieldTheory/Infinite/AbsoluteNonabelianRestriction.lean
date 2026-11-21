/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.EmbeddedAbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction

/-!
# Finite Galois projections of absolute local reciprocity

The commutator fixed field identifies the actual abelianized finite
restriction with the finite Artin symbol, including when the extension is
nonabelian.
-/

@[expose] public section

open scoped IsMulCommutative ValuativeRel

noncomputable section

namespace LocalClassFieldTheory

open ClassFieldTower.Martinet.Shafarevich FunctionField LocalFieldTheory ProCGroups.Abelian

universe u v

namespace Universe

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsGalois K L]

/-- Finite local reciprocity on the original Galois group in its Krull
topology, obtained from the actual absolute Artin map and embedded restriction. -/
noncomputable def localArtinMapOfEmbedding (i : L →ₐ[K] SeparableClosure K) :
    Kˣ →ₜ* TopologicalAbelianization Gal(L/K) :=
  (TopologicalAbelianization.map (embeddedFiniteRestrictionContinuous K L i)).comp
    (separableAbsoluteLocalArtinMap K)

/-- Embedded restriction on absolute abelianization uses the same coordinate
for every embedding of the original finite Galois extension. -/
theorem localArtinMapOfEmbedding_eq
    (i j : L →ₐ[K] SeparableClosure K) :
    localArtinMapOfEmbedding K L i = localArtinMapOfEmbedding K L j := by
  obtain ⟨α, hα⟩ := AlgebraicNumberTheory.exists_separableClosureEmbeddingComparisonAutomorphism i j
  let G := Gal(SeparableClosure K/K)
  let q := TopologicalAbelianization.mk G
  let p (k : L →ₐ[K] SeparableClosure K) :=
    TopologicalAbelianization.map (embeddedFiniteRestrictionContinuous K L k)
  ext x
  change p i (separableAbsoluteLocalArtinMap K x) = p j (separableAbsoluteLocalArtinMap K x)
  generalize separableAbsoluteLocalArtinMap K x = z
  obtain ⟨σ, rfl⟩ := TopologicalAbelianization.surjective_mk G z
  have hq : q (α * σ * α⁻¹) = q σ := by
    rw [map_mul, map_mul, map_inv, mul_right_comm (q α) (q σ), mul_inv_cancel, one_mul]
  have hr : embeddedFiniteRestriction K L j (α * σ * α⁻¹) =
      embeddedFiniteRestriction K L i σ := by
    apply AlgEquiv.ext
    intro y
    apply j.injective
    calc
      j (embeddedFiniteRestriction K L j (α * σ * α⁻¹) y) =
          (α * σ * α⁻¹) (j y) := embeddedFiniteRestriction_commutes K L j _ y
      _ = α (σ (α.symm (j y))) := rfl
      _ = α (σ (i y)) := by rw [← hα y, α.symm_apply_apply]
      _ = α (i (embeddedFiniteRestriction K L i σ y)) :=
        congrArg α (embeddedFiniteRestriction_commutes K L i σ y).symm
      _ = _ := hα _
  calc
    p i (q σ) = TopologicalAbelianization.mk _ (embeddedFiniteRestriction K L i σ) := rfl
    _ = p j (q (α * σ * α⁻¹)) := congrArg (TopologicalAbelianization.mk _) hr.symm
    _ = p j (q σ) := congrArg (p j) hq

/-- Finite Galois Artin reciprocity, with no embedding required as input. -/
noncomputable def localArtinMap : Kˣ →ₜ* TopologicalAbelianization Gal(L/K) :=
  localArtinMapOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)

theorem localArtinMap_eq_ofEmbedding (i : L →ₐ[K] SeparableClosure K) :
    localArtinMap K L = localArtinMapOfEmbedding K L i :=
  localArtinMapOfEmbedding_eq K L _ i

/-- The finite coordinate of the absolute restriction uses ordinary
abelianization after identifying the two quotients of the finite group. -/
theorem localArtinMapOfEmbedding_toAbelianization
    (i : L →ₐ[K] SeparableClosure K) (x : Kˣ) :
    (topologicalAbelianization_finite_equiv K L).symm (localArtinMapOfEmbedding K L i x) =
      absoluteAbelianizedRestrictionOfEmbedding K L i (separableAbsoluteLocalArtinMap K x) := by
  have h (z : localAbsoluteAbelianProfinite K) :
      (topologicalAbelianization_finite_equiv K L).symm
          (TopologicalAbelianization.map (embeddedFiniteRestrictionContinuous K L i) z) =
        absoluteAbelianizedRestrictionOfEmbedding K L i z := by
    refine QuotientGroup.induction_on z fun σ => ?_
    rw [absoluteAbelianizedRestrictionOfEmbedding_mk]
    change (topologicalAbelianization_finite_equiv K L).symm
        (TopologicalAbelianization.mk _ (embeddedFiniteRestriction K L i σ)) =
      Group.Abelianization.of (embeddedFiniteRestriction K L i σ)
    apply (topologicalAbelianization_finite_equiv K L).injective
    rw [MulEquiv.apply_symm_apply]
    exact (QuotientGroup.quotientMulEquivOfEq_mk
      (commutator_topologicalClosure_eq (Gal(L/K))).symm
      (embeddedFiniteRestriction K L i σ)).symm
  exact h (separableAbsoluteLocalArtinMap K x)

/-- Surjectivity follows from density of absolute reciprocity and discreteness
of the actual finite Galois abelianization. -/
theorem localArtinMapOfEmbedding_surjective (i : L →ₐ[K] SeparableClosure K) :
    Function.Surjective (localArtinMapOfEmbedding K L i) := by
  let p := TopologicalAbelianization.map (embeddedFiniteRestrictionContinuous K L i)
  have hp : Function.Surjective p :=
    TopologicalAbelianization.surjective_map_of_surjective _
      (embeddedFiniteRestriction_surjective K L i)
  have hd : DenseRange (localArtinMapOfEmbedding K L i) :=
    hp.denseRange.comp (separableAbsoluteLocalArtinMap_denseRange K) p.continuous
  let : DiscreteTopology (TopologicalAbelianization Gal(L/K)) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  intro y
  obtain ⟨x, hx⟩ := hd.exists_mem_open (isOpen_discrete {y}) ⟨y, rfl⟩
  exact ⟨x, Set.mem_singleton_iff.mp hx⟩

end Universe

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

private theorem abelianizationMap_of_composed_restriction
    {A B C : Type*} [Group A] [Group B] [Group C] (r : A →* B) (t : B →* C)
    (s : A →* C) (e : Group.Abelianization B ≃* C) (hr : Function.Surjective r)
    (he : ∀ a, e (Group.Abelianization.of (r a)) = s a)
    (hcomp : ∀ a, s a = t (r a)) (z : Group.Abelianization B) :
    Group.Abelianization.of (e z) = Group.Abelianization.map t z := by
  have hs : Function.Surjective (Group.Abelianization.of.comp r) :=
    QuotientGroup.mk_surjective.comp hr
  obtain ⟨a, rfl⟩ := hs z
  change Group.Abelianization.of (e (Group.Abelianization.of (r a))) =
    Group.Abelianization.map t (Group.Abelianization.of (r a))
  rw [he, Group.Abelianization.map_of, hcomp]

/-- An actual finite Galois projection of absolute local reciprocity is the
existing finite Artin value in the abelianization. -/
theorem separableAbsoluteLocalArtinMap_abelianizedRestriction
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] (a : Kˣ) :
    absoluteAbelianizedRestriction K E (separableAbsoluteLocalArtinMap K a) =
      localArtinMonoidHom K E a := by
  let Ω := SeparableClosure K
  let r : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  let q : Gal(Ω/K) →* Group.Abelianization Gal(E/K) := Group.Abelianization.of.comp r
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := E) (E := Ω)
  have hq : Function.Surjective q := QuotientGroup.mk_surjective.comp hr
  have hker := restrictionAbelianization_ker_closed_open K E
  let S : ClosedSubgroup Gal(Ω/K) := ⟨q.ker, hker.1⟩
  let : S.toSubgroup.Normal := inferInstanceAs q.ker.Normal
  let M : IntermediateField K Ω := IntermediateField.fixedField S.toSubgroup
  let : FiniteDimensional K M := by
    apply (InfiniteGalois.isOpen_iff_finite (K := Ω) M).mp
    change IsOpen ((IntermediateField.fixedField S.toSubgroup).fixingSubgroup : Set Gal(Ω/K))
    rw [InfiniteGalois.fixingSubgroup_fixedField S]
    exact hker.2
  let : IsGalois K M := IsGalois.of_fixedField_normal_subgroup S.toSubgroup
  let eQ : (Gal(Ω/K) ⧸ q.ker) ≃* Group.Abelianization Gal(E/K) :=
    QuotientGroup.quotientKerEquivOfSurjective q hq
  let eG : (Gal(Ω/K) ⧸ S.toSubgroup) ≃* Gal(M/K) :=
    InfiniteGalois.normalAutEquivQuotient S
  let e : Group.Abelianization Gal(E/K) ≃* Gal(M/K) := eQ.symm.trans eG
  let : IsAbelianGalois K M :=
    { toIsGalois := inferInstance
      toIsMulCommutative := e.surjective.isMulCommutative }
  have he (σ : Gal(Ω/K)) : e (q σ) = AlgEquiv.restrictNormalHom M σ := by
    change eG (eQ.symm (eQ (QuotientGroup.mk σ))) = _
    rw [eQ.symm_apply_apply]
    exact InfiniteGalois.normalAutEquivQuotient_apply S σ
  have hfix : E.fixingSubgroup ≤ S.toSubgroup := by
    intro σ hσ
    have hs : r σ = 1 := by
      apply MonoidHom.mem_ker.mp
      change σ ∈ (AlgEquiv.restrictNormalHom E).ker
      rwa [IntermediateField.restrictNormalHom_ker]
    change Group.Abelianization.of (r σ) = 1
    rw [hs, map_one]
  have hME : M ≤ E := (IntermediateField.fixedField_le hfix).trans
    (InfiniteGalois.fixedField_fixingSubgroup E).le
  let : Algebra M E := (M.inclusion hME).toRingHom.toAlgebra
  let : IsScalarTower K M E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let : IsScalarTower M E Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let rEM : Gal(E/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  have hfinite := abelianizationMap_of_composed_restriction r rEM
    (AlgEquiv.restrictNormalHom M) e hr he
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply M E)
  have habs (z : localAbsoluteAbelianProfinite K) :
      e (absoluteAbelianizedRestriction K E z) = absoluteAbelianRestriction K M z := by
    refine QuotientGroup.induction_on z fun σ => ?_
    rw [absoluteAbelianizedRestriction_mk, absoluteAbelianRestriction_mk]
    exact he σ
  apply e.injective
  rw [habs, separableAbsoluteLocalArtinMap_restriction K M]
  have hNative : abelianLocalArtinMap K M a = abelianLocalArtinMonoidHom K M a :=
    DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom K M) a
  rw [hNative]
  apply (Group.Abelianization.equivOfComm (H := Gal(M/K))).injective
  change Group.Abelianization.of (abelianLocalArtinMonoidHom K M a) =
    Group.Abelianization.of (e (localArtinMonoidHom K E a))
  let z := localArtinMonoidHom K E a
  have hTower : Group.Abelianization.map rEM z = localArtinMonoidHom K M a :=
    localArtinMonoidHom_restrict_tower K M E a
  have hComm : Group.Abelianization.of (abelianLocalArtinMonoidHom K M a) =
      localArtinMonoidHom K M a :=
    (Group.Abelianization.equivOfComm (H := Gal(M/K))).apply_symm_apply _
  exact hComm.trans ((hfinite z).trans hTower).symm

/-- Projection through any chosen embedding gives the finite Artin map on
the original extension and its own Galois abelianization. -/
theorem separableAbsoluteLocalArtinMap_abelianizedRestrictionOfEmbedding
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) (a : Kˣ) :
    absoluteAbelianizedRestrictionOfEmbedding K L i (separableAbsoluteLocalArtinMap K a) =
      localArtinMonoidHom K L a := by
  let E := finiteGaloisFieldRangeOfEmbedding K L i
  let e := finiteGaloisFieldRangeEquivOfEmbedding K L i
  change (AlgEquiv.autCongr e).abelianizationCongr.symm
    (absoluteAbelianizedRestriction K E (separableAbsoluteLocalArtinMap K a)) = _
  rw [separableAbsoluteLocalArtinMap_abelianizedRestriction K E,
    ← localArtinMonoidHom_autCongr K L E e a, MulEquiv.symm_apply_apply]

/-- The continuous map on the original finite Galois group agrees with the
existing arithmetic Artin symbol. -/
theorem localArtinMapOfEmbedding_eq_localArtinMonoidHom
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) (x : Kˣ) :
    (topologicalAbelianization_finite_equiv K L).symm (Universe.localArtinMapOfEmbedding K L i x) =
      localArtinMonoidHom K L x :=
  (Universe.localArtinMapOfEmbedding_toAbelianization K L i x).trans
    (separableAbsoluteLocalArtinMap_abelianizedRestrictionOfEmbedding K L i x)

end LocalClassFieldTheory
