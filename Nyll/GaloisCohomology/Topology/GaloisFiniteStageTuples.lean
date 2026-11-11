/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.GaloisFiniteStageFunctions
public import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Topology.LocallyConstant.Basic
public import Nyll.ProCGroups.Cohomology.ContinuousMapFiniteStage

/-!
# Finite Galois stages for finite tuples

A continuous discrete-valued function on any finite power of an absolute
Galois group factors through one finite Galois field. This extends the
two-coordinate result to the arbitrary degrees needed for cohomology.
-/

@[expose] public section

noncomputable section
open scoped Topology
open ProCGroups ProCGroups.ProC

namespace GaloisCohomology

universe u v w t
section GaloisExtension

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω]

/-- A finite tuple of Galois elements has one common finite Galois stage
for every continuous finite-valued function. -/
theorem exists_finiteGalois_factor_continuous_tuple
    {ι : Type t} [Finite ι]
    {Y : Type w} [TopologicalSpace Y] [Finite Y] [DiscreteTopology Y]
    (z : (ι → Gal(Ω/K)) → Y) (hz : Continuous z) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (zE : (ι → Gal(E/K)) → Y),
      ∀ a : ι → Gal(Ω/K), zE (fun i => AlgEquiv.restrictNormalHom E (a i)) = z a := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨U, zU, _hzU, hfac⟩ :=
    ClassFieldTower.Cohomology.exists_openNormalSubgroupInClass_factor_continuousMap_finite
      FiniteGroupClass.allFinite_formation hasOpenNormalBasisInClass_allFinite z hz
  let j (i : ι) : Gal(Ω/K) →ₜ* (ι → Gal(Ω/K)) :=
    { toMonoidHom := MonoidHom.mulSingle (fun _ : ι => Gal(Ω/K)) i
      continuous_toFun := continuous_mulSingle (A := fun _ : ι => Gal(Ω/K)) i }
  let V : Set Gal(Ω/K) :=
    ⋂ i : ι, (j i) ⁻¹' ((U.1 : Subgroup (ι → Gal(Ω/K))) : Set (ι → Gal(Ω/K)))
  have hVopen : IsOpen V := isOpen_iInter_of_finite
    (fun i => (openNormalSubgroup_isOpen U.1).preimage (j i).continuous)
  have hVone : (1 : Gal(Ω/K)) ∈ V := by
    apply Set.mem_iInter.mpr
    intro i
    change j i 1 ∈ (U.1 : Subgroup (ι → Gal(Ω/K)))
    rw [map_one]
    exact Subgroup.one_mem _
  obtain ⟨E, hE⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
    (k := K) (K := Ω) V).mp (hVopen.mem_nhds hVone)
  let r : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective Ω
  let q := OpenNormalSubgroupInClass.quotientProj U
  let c : (ι → E.fixingSubgroup) →* (ι → Gal(Ω/K)) :=
    MonoidHom.pi (fun i => E.fixingSubgroup.subtype.comp
      (Pi.evalMonoidHom (fun _ : ι => E.fixingSubgroup) i))
  have hqc : q.toMonoidHom.comp c = 1 := by
    apply MonoidHom.pi_ext
    intro i x
    have hc : c (Pi.mulSingle i x) = Pi.mulSingle i x.val := by
      funext k
      change (Pi.mulSingle (M := fun _ : ι => E.fixingSubgroup) i x k).val =
        Pi.mulSingle (M := fun _ : ι => Gal(Ω/K)) i x.val k
      by_cases hk : k = i
      · subst k
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · simp only [Pi.mulSingle, Function.update_of_ne hk, Pi.one_apply]
        rfl
    change q (c (Pi.mulSingle i x)) = 1
    rw [hc]
    have hx : j i x.val ∈ (U.1 : Subgroup (ι → Gal(Ω/K))) :=
      Set.mem_iInter.mp (hE x.property) i
    have heq : q (j i x.val) = q 1 :=
      OpenNormalSubgroupInClass.quotientProj_eq_quotientProj_iff.mpr
        (by simpa only [div_one] using hx)
    exact heq.trans (map_one q)
  have hrel {σ τ : Gal(Ω/K)} (hστ : r σ = r τ) :
      σ / τ ∈ E.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    change r (σ / τ) = 1
    rw [div_eq_mul_inv, map_mul, map_inv, hστ, mul_inv_cancel]
  have hfactor (a b : ι → Gal(Ω/K)) (hab : ∀ i, r (a i) = r (b i)) :
      z a = z b := by
    rw [congrFun hfac a, congrFun hfac b]
    apply congrArg zU
    apply OpenNormalSubgroupInClass.quotientProj_eq_quotientProj_iff.mpr
    have hq : q (a / b) = 1 :=
      congrArg (fun f : (ι → E.fixingSubgroup) →* _ =>
        f (fun i => ⟨a i / b i, hrel (hab i)⟩)) hqc
    have heq : q (a / b) = q 1 := hq.trans (map_one q).symm
    simpa only [div_one] using
      (OpenNormalSubgroupInClass.quotientProj_eq_quotientProj_iff.mp heq)
  refine ⟨E, fun a => z (fun i => (hr (a i)).choose), ?_⟩
  intro a
  exact hfactor _ a (fun i => (hr (r (a i))).choose_spec)

/-- Compactness also gives finite-stage factorization for arbitrary discrete targets. -/
theorem exists_finiteGalois_factor_continuous_tuple_discrete
    {ι : Type t} [Finite ι]
    {Y : Type w} [TopologicalSpace Y] [DiscreteTopology Y]
    (z : (ι → Gal(Ω/K)) → Y) (hz : Continuous z) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (zE : (ι → Gal(E/K)) → Y),
      ∀ a : ι → Gal(Ω/K), zE (fun i => AlgEquiv.restrictNormalHom E (a i)) = z a := by
  have hfin : (Set.range z).Finite := (isCompact_range hz).finite_of_discrete
  have : Finite (Set.range z) := hfin.to_subtype
  let z' : (ι → Gal(Ω/K)) → Set.range z := fun a => ⟨z a, ⟨a, rfl⟩⟩
  have hz' : Continuous z' := hz.subtype_mk (fun a => ⟨a, rfl⟩)
  obtain ⟨E, zE, hE⟩ := exists_finiteGalois_factor_continuous_tuple z' hz'
  exact ⟨E, fun a => (zE a).val, fun a => congrArg Subtype.val (hE a)⟩

end GaloisExtension

/-- A continuous discrete-valued function on a finite power of an arbitrary
absolute Galois group factors through an actual finite Galois subfield of its
algebraic closure. Restriction to the separable closure supplies the Galois
ambient extension; the resulting stage is then mapped into the original closure. -/
theorem exists_finiteGalois_factor_absolute_tuple_discrete
    (K : Type u) [Field K]
    {ι : Type t} [Finite ι]
    {Y : Type w} [TopologicalSpace Y] [DiscreteTopology Y]
    (z : (ι → Gal(AlgebraicClosure K/K)) → Y) (hz : Continuous z) :
    ∃ (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (zM : (ι → Gal(M/K)) → Y),
      ∀ a : ι → Gal(AlgebraicClosure K/K),
        zM (fun i => AlgEquiv.restrictNormalHom M (a i)) = z a := by
  let c := ValuationTheory.Completion.separableClosureAutContinuousEquiv K
  let z' : (ι → Gal(SeparableClosure K/K)) → Y :=
    fun a => z (fun i => c.symm (a i))
  have hz' : Continuous z' :=
    hz.comp (continuous_pi fun i => c.symm.continuous.comp (continuous_apply i))
  obtain ⟨E, zE, hE⟩ := exists_finiteGalois_factor_continuous_tuple_discrete z' hz'
  let j : SeparableClosure K →ₐ[K] AlgebraicClosure K :=
    (separableClosure K (AlgebraicClosure K)).val
  let M₀ : IntermediateField K (AlgebraicClosure K) := E.toIntermediateField.map j
  let e₀ : E ≃ₐ[K] M₀ := IntermediateField.equivMap E.toIntermediateField j
  let M : FiniteGaloisIntermediateField K (AlgebraicClosure K) :=
    { toIntermediateField := M₀
      finiteDimensional := LinearEquiv.finiteDimensional e₀.toLinearEquiv
      isGalois := IsGalois.of_algEquiv e₀ }
  have : IsGalois K M.toIntermediateField := M.isGalois
  let e : E ≃ₐ[K] M := e₀
  have he (x : E) : (e x : AlgebraicClosure K) = j (x : SeparableClosure K) :=
    IntermediateField.coe_equivMap_apply E.toIntermediateField j x
  have hact (σ : Gal(AlgebraicClosure K/K)) (x : E) :
      (e (AlgEquiv.restrictNormalHom E (c σ) x) : AlgebraicClosure K) =
        σ (e x : AlgebraicClosure K) := by
    rw [he, he]
    exact (congrArg j (AlgEquiv.restrictNormalHom_apply E.toIntermediateField
      (c σ) x)).trans
        (ValuationTheory.Completion.separableClosureAutContinuousEquiv_apply K σ x)
  have hrestrict (σ : Gal(AlgebraicClosure K/K)) :
      AlgEquiv.autCongr e.symm (AlgEquiv.restrictNormalHom M σ) =
        AlgEquiv.restrictNormalHom E (c σ) := by
    apply AlgEquiv.ext
    intro x
    change e.symm (AlgEquiv.restrictNormalHom M σ (e x)) =
      AlgEquiv.restrictNormalHom E (c σ) x
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact (AlgEquiv.restrictNormalHom_apply M.toIntermediateField σ (e x)).trans
      (hact σ x).symm
  refine ⟨M, fun a => zE (fun i => AlgEquiv.autCongr e.symm (a i)), ?_⟩
  intro a
  calc
    zE (fun i => AlgEquiv.autCongr e.symm
        (AlgEquiv.restrictNormalHom M (a i))) =
        zE (fun i => AlgEquiv.restrictNormalHom E (c (a i))) :=
      congrArg zE (funext (fun i => hrestrict (a i)))
    _ = z' (fun i => c (a i)) := hE (fun i => c (a i))
    _ = z a := congrArg z (funext (fun i => c.symm_apply_apply (a i)))

end GaloisCohomology
