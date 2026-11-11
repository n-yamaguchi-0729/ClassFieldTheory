/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Tsen.GaloisH2OfTsen
public import Nyll.GaloisCohomology.Kummer.FiniteKummerAbsoluteLift
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.Cyclic.IntegralCoefficientCohomology
public import Nyll.GaloisCohomology.Topology.GaloisFiniteStageTuples
public import Nyll.GaloisCohomology.ArtinSchreier.CohomologyVanishing
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.FinitePGroupCoefficientVanishing
public import Nyll.GaloisCohomology.Topology.ContinuousRestrictionEquiv
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
public import Nyll.GaloisCohomology.Kummer.Concrete.SeparableGaloisClosureConjugation
public import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
public import Nyll.AlgebraicCurves.FunctionFields.Tsen.NormSurjectiveOfTsen
public import Nyll.GaloisCohomology.Topology.ContinuousH2FiniteIndexTrace
public import Nyll.GaloisCohomology.Topology.FiniteInvariantCoefficients
public import Nyll.GaloisCohomology.Topology.FiniteCoefficientPrimeDevissage
public import Nyll.GaloisCohomology.Topology.FiniteCoefficientCochains
public import Nyll.GaloisCohomology.Topology.ContinuousCoinducedDimensionShift
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Tactic.Abel
public import Nyll.GaloisCohomology.ProP.TrivialZModP
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness
public import Nyll.GaloisCohomology.Topology.TrivialDegreeTwoCocycles

/-!
# Continuous mod-p two-cocycle primitives over curve function fields

A continuous finite-valued cocycle descends to an actual finite Galois
intermediate field. Tsen supplies vanishing of its actual field-unit H²
class. The existing Hilbert-90 and Kummer correction gives a continuous
mod-p primitive on the absolute Galois group when p differs from the
characteristic. In characteristic p, the existing Artin–Schreier primitive
is transported from the separable closure. Open subgroups are also treated
through the separable closure, including for imperfect function fields.

This proves an absolute-Galois statement. It does not assert the still
separate comparison with higher étale cohomology of a curve.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped Topology

namespace AlgebraicCurve

open ClassFieldTower.Martinet.Shafarevich

private theorem ulift_twoCocycle_transport
    {G H A : Type*} [Group G] [Group H] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (c : G × G → ULift.{u} A)
    (hc : ∀ s t u : G,
      c (s * t, u) + c (s, t) = c (t, u) + c (s, t * u))
    (s t u : H) :
    (c (e.symm s, e.symm (t * u))).down + (c (e.symm t, e.symm u)).down =
      (c (e.symm (s * t), e.symm u)).down + (c (e.symm s, e.symm t)).down := by
  rw [map_mul e.symm s t, map_mul e.symm t u]
  have h := congrArg (fun a : ULift.{u} A => a.down)
    (hc (e.symm s) (e.symm t) (e.symm u))
  change (c (e.symm s * e.symm t, e.symm u)).down +
      (c (e.symm s, e.symm t)).down =
    (c (e.symm t, e.symm u)).down +
      (c (e.symm s, e.symm t * e.symm u)).down at h
  exact (add_comm _ _).trans h.symm

private theorem ulift_twoCocycle_primitive_transport
    {G H A : Type*} [Group G] [Group H] [AddCommGroup A]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (c : G × G → ULift.{u} A) (d : H → A)
    (hd : ∀ s t : H,
      d t - d (s * t) + d s = (c (e.symm s, e.symm t)).down)
    (s t : G) :
    ULift.up (d (e t)) + ULift.up (d (e s)) - ULift.up (d (e (s * t))) =
      c (s, t) := by
  apply ULift.ext
  change d (e t) + d (e s) - d (e (s * t)) = (c (s, t)).down
  have h := hd (e s) (e t)
  rw [e.symm_apply_apply s, e.symm_apply_apply t] at h
  rw [map_mul e s t]
  calc
    d (e t) + d (e s) - d (e s * e t) =
        d (e t) - d (e s * e t) + d (e s) := by abel
    _ = (c (s, t)).down := h

/-- Every continuous mod-p two-cocycle on the actual absolute Galois
group of a curve function field in arbitrary characteristic is a continuous
coboundary. No finite-stage norm or vanishing hypothesis is required. -/
theorem exists_continuous_modP_twoCocycle_primitive_of_transcendental_of_finiteDimensional
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (c : C(Field.absoluteGaloisGroup F × Field.absoluteGaloisGroup F,
      ULift.{u} (ZMod (p : ℕ))))
    (hc : ∀ s t u : Field.absoluteGaloisGroup F,
      c (s * t, u) + c (s, t) = c (t, u) + c (s, t * u)) :
    ∃ a : C(Field.absoluteGaloisGroup F, ULift.{u} (ZMod (p : ℕ))),
      ∀ s t, a t + a s - a (s * t) = c (s, t) := by
  classical
  by_cases hpK : ((p : ℕ) : K) = 0
  · have : CharP K (p : ℕ) :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : (p : ℕ).Prime)).mpr hpK
    have : CharP F (p : ℕ) :=
      charP_of_injective_algebraMap (algebraMap K F).injective (p : ℕ)
    let e : Field.absoluteGaloisGroup F ≃ₜ* Gal(SeparableClosure F/F) :=
      ValuationTheory.Completion.separableClosureAutContinuousEquiv F
    let z : Gal(SeparableClosure F/F) → Gal(SeparableClosure F/F) → ZMod (p : ℕ) :=
      fun s t => (c (e.symm s, e.symm t)).down
    have hz : ∀ s t u, z s (t * u) + z t u = z (s * t) u + z s t := by
      exact ulift_twoCocycle_transport e c hc
    have hzc : IsLocallyConstant
        (fun st : Gal(SeparableClosure F/F) × Gal(SeparableClosure F/F) => z st.1 st.2) :=
      (IsLocallyConstant.iff_continuous _).mpr
        (continuous_uliftDown.comp
          (c.continuous.comp (e.symm.continuous.prodMap e.symm.continuous)))
    obtain ⟨d, hdcont, hd⟩ :=
      ArtinSchreierTheory.exists_zmod_primitive_of_two_cocycle (p : ℕ) z hz hzc
    refine ⟨⟨fun s => ULift.up (d (e s)),
      continuous_uliftUp.comp (hdcont.continuous.comp e.continuous)⟩, ?_⟩
    intro s t
    exact ulift_twoCocycle_primitive_transport e c d hd s t
  have : NeZero ((p : ℕ) : K) := ⟨hpK⟩
  let c' : (Bool → Gal(AlgebraicClosure F/F)) → ULift.{u} (ZMod (p : ℕ)) :=
    fun a => c (a false, a true)
  obtain ⟨E, zE, hfac'⟩ :=
    GaloisCohomology.exists_finiteGalois_factor_absolute_tuple_discrete F c'
      (c.continuous.comp ((continuous_apply false).prodMk (continuous_apply true)))
  let cE : Gal(E/F) → Gal(E/F) → ULift.{u} (ZMod (p : ℕ)) :=
    fun s t => zE (fun b => cond b t s)
  have hfac (s t : Gal(AlgebraicClosure F/F)) :
      cE (AlgEquiv.restrictNormalHom E s) (AlgEquiv.restrictNormalHom E t) =
        c (s, t) := by
    have he : (fun b => AlgEquiv.restrictNormalHom E (cond b t s)) =
        (fun b => cond b (AlgEquiv.restrictNormalHom E t)
          (AlgEquiv.restrictNormalHom E s)) := by
      funext b
      cases b <;> rfl
    have h := hfac' (fun b => cond b t s)
    change zE (fun b => AlgEquiv.restrictNormalHom E (cond b t s)) = c (s, t) at h
    rw [he] at h
    exact h
  let r : Gal(AlgebraicClosure F/F) →* Gal(E/F) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective _
  have hcE (s t u : Gal(E/F)) :
      cE (s * t) u + cE s t = cE t u + cE s (t * u) := by
    obtain ⟨s', rfl⟩ := hr s
    obtain ⟨t', rfl⟩ := hr t
    obtain ⟨u', rfl⟩ := hr u
    rw [← map_mul r, ← map_mul r]
    change cE (AlgEquiv.restrictNormalHom E (s' * t'))
        (AlgEquiv.restrictNormalHom E u') +
      cE (AlgEquiv.restrictNormalHom E s') (AlgEquiv.restrictNormalHom E t') =
      cE (AlgEquiv.restrictNormalHom E t') (AlgEquiv.restrictNormalHom E u') +
      cE (AlgEquiv.restrictNormalHom E s')
        (AlgEquiv.restrictNormalHom E (t' * u'))
    rw [hfac, hfac, hfac, hfac]
    exact hc s' t' u'
  let A := (IntegralGroupCohomology.coefficientFunctor Gal(E/F)).obj
    (Rep.trivial ℤ Gal(E/F) (ULift.{u} (ZMod (p : ℕ))))
  let z : groupCohomology.cocycles₂ A :=
    ⟨fun st => cE st.1 st.2,
      (groupCohomology.mem_cocycles₂_iff _).mpr hcE⟩
  have hmu : (primitiveRoots (p : ℕ) F).Nonempty := by
    have : NeZero (p : ℕ) := ⟨p.ne_zero⟩
    obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (p : ℕ)
    exact ⟨algebraMap K F zeta,
      (mem_primitiveRoots p.pos).mpr
        (hzeta.map_of_injective (algebraMap K F).injective)⟩
  let zu := groupCohomology.mapCocycles₂ (MonoidHom.id Gal(E/F))
    ((IntegralGroupCohomology.coefficientFunctor Gal(E/F)).map
      (finiteKummerCoefficientRepHom F E p hmu)) z
  have hz : groupCohomology.H2π (ClassFieldTower.Cohomology.liftedGaloisUnitsRep F E) zu = 0 :=
    liftedGaloisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional K x hx hfin E _
  obtain ⟨b, hb⟩ : ∃ b : Gal(E/F) → Additive Eˣ,
      (groupCohomology.d₁₂ (ClassFieldTower.Cohomology.liftedGaloisUnitsRep F E)).hom b = zu.1 :=
    (groupCohomology.H2π_eq_zero_iff zu).mp hz
  obtain ⟨a, ha⟩ := exists_absoluteZModP_primitive_of_finiteKummerUnit_boundary
    F p E hmu cE (fun s => (b s).toMul) (by
      intro s t
      have h := congrArg Additive.toMul (congrFun hb (s, t))
      change Units.map (s : E →* E) (b t).toMul / (b (s * t)).toMul * (b s).toMul =
        (finiteKummerCoefficientAddHom F E p hmu (cE s t)).toMul at h
      simpa only [div_mul_eq_mul_div] using h)
  refine ⟨a, ?_⟩
  intro s t
  rw [ha]
  exact hfac s t

/-- Actual continuous degree-two cohomology with trivial mod-p coefficients
vanishes for the absolute Galois group of the curve function field. -/
theorem absoluteGalois_continuousH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (v : ClassFieldTower.Cohomology.continuousCohomologyZModPLifted
      (p : ℕ) (Field.absoluteGaloisGroup F) 2) : v = 0 := by
  have : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace Gal(AlgebraicClosure F/F))
  exact TopRep.TrivialDegreeTwoCocycles.continuousH2_eq_zero_of_primitive
    (ClassFieldTower.Cohomology.trivialZModPLifted (p : ℕ)
      (Field.absoluteGaloisGroup F))
    (fun _ _ => rfl)
    (fun c hc =>
      exists_continuous_modP_twoCocycle_primitive_of_transcendental_of_finiteDimensional
        K x hx hfin p c hc) v

/-- Actual integral continuous degree-two cohomology with trivial mod-p
additive coefficients vanishes for the curve function field, using the
same geometric Tsen primitive as for finite-field scalar coefficients. -/
theorem absoluteGalois_integralContinuousH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (v : continuousCohomology 2
      (ClassFieldTower.Cohomology.trivialIntegralZModPLifted
        (p : ℕ) (Field.absoluteGaloisGroup F))) : v = 0 := by
  have : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace Gal(AlgebraicClosure F/F))
  exact TopRep.TrivialDegreeTwoCocycles.continuousH2_eq_zero_of_primitive
    (ClassFieldTower.Cohomology.trivialIntegralZModPLifted (p : ℕ)
      (Field.absoluteGaloisGroup F))
    (fun _ _ => rfl)
    (fun c hc =>
      exists_continuous_modP_twoCocycle_primitive_of_transcendental_of_finiteDimensional
        K x hx hfin p c hc) v

/-- Geometric Tsen vanishing extends to actual finite mod-p integral
coefficients whose absolute Galois action image is a p-group. -/
theorem absoluteGalois_finiteIntegralH2_isZero_of_pGroup_image
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (X : TopRep.{u} ℤ (Field.absoluteGaloisGroup F))
    [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2))
    (hpX : ∀ v : X, (p : ℕ) • v = 0)
    (hρ : let _ : Module ℤ X := X.hV2
      IsPGroup (p : ℕ) X.ρ.toRepresentation.asGroupHom.range) :
    CategoryTheory.Limits.IsZero
      (((TopRep.continuousModuleComplexFunctor
        (Field.absoluteGaloisGroup F)).obj X).homology 2) := by
  have : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace Gal(AlgebraicClosure F/F))
  apply TopRep.continuousModuleH2_isZero_of_pGroup_image
    (Field.absoluteGaloisGroup F) (p : ℕ) ?_ X hX hpX hρ
  apply TopRep.continuousModuleComplex_isZero_of_cohomology_eq_zero
  intro v
  exact absoluteGalois_integralContinuousH2_eq_zero_of_transcendental_of_finiteDimensional
    K x hx hfin p v

/-- Actual finite mod-p cohomology vanishes on an open function-field
Galois subgroup when the coefficient action image is a p-group. -/
theorem openAbsoluteGalois_finiteIntegralH2_eq_zero_of_pGroup_image
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (H : OpenSubgroup (Field.absoluteGaloisGroup F))
    (X : TopRep.{u} ℤ ↥(H : Subgroup (Field.absoluteGaloisGroup F)))
    [Finite X] [DiscreteTopology X]
    (hX : Continuous
      (fun gx : ↥(H : Subgroup (Field.absoluteGaloisGroup F)) × X =>
        X.ρ gx.1 gx.2))
    (hpX : ∀ v : X, (p : ℕ) • v = 0)
    (hρ : let _ : Module ℤ X := X.hV2
      IsPGroup (p : ℕ) X.ρ.toRepresentation.asGroupHom.range)
    (v : continuousCohomology 2 X) : v = 0 := by
  let c := ValuationTheory.Completion.separableClosureAutContinuousEquiv F
  let H' : OpenSubgroup Gal(SeparableClosure F/F) :=
    { toSubgroup := H.toSubgroup.map c.toMonoidHom
      isOpen' := by
        change IsOpen (c '' (H : Set (Field.absoluteGaloisGroup F)))
        exact c.toHomeomorph.isOpenMap _ H.isOpen }
  let eH : ↥(H : Subgroup (Field.absoluteGaloisGroup F)) ≃ₜ*
      ↥(H' : Subgroup Gal(SeparableClosure F/F)) :=
    { toMulEquiv := c.toMulEquiv.subgroupMap H.toSubgroup
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact c.continuous.comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact c.symm.continuous.comp continuous_subtype_val }
  obtain ⟨E, hE, ⟨e₀⟩⟩ :=
    KummerTheory.exists_finiteIntermediateField_openSubgroup_equiv H'
  have : FiniteDimensional F E := hE
  let : Algebra K E := ((algebraMap F E).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsSepClosure E (SeparableClosure F) := ⟨inferInstance, inferInstance⟩
  let e : Field.absoluteGaloisGroup E ≃ₜ*
      ↥(H : Subgroup (Field.absoluteGaloisGroup F)) :=
    ((eH.trans e₀).trans
      (KummerTheory.separableAbsoluteGaloisClosureEquiv E (SeparableClosure F))).symm
  obtain ⟨y, hy, hyfin, _⟩ :=
    exists_separating_transcendental_over_finite_extension K x hx hfin E
  let Y : TopRep.{u} ℤ (Field.absoluteGaloisGroup E) :=
    TopRep.res e.toMonoidHom X
  have hY : Continuous
      (fun gy : Field.absoluteGaloisGroup E × Y => Y.ρ gy.1 gy.2) :=
    hX.comp (e.continuous.prodMap continuous_id)
  let : Module ℤ X := X.hV2
  have hρY : IsPGroup (p : ℕ) Y.ρ.toRepresentation.asGroupHom.range := by
    have hle : Y.ρ.toRepresentation.asGroupHom.range ≤
        X.ρ.toRepresentation.asGroupHom.range := by
      rintro a ⟨g, rfl⟩
      refine ⟨e g, ?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro z
      rfl
    exact hρ.of_injective (Subgroup.inclusion hle)
      (fun a b hab => Subtype.ext
        (congrArg (fun z : X.ρ.toRepresentation.asGroupHom.range =>
          (z : Units (Module.End ℤ X))) hab))
  have hzero := absoluteGalois_finiteIntegralH2_isZero_of_pGroup_image
    K y hy hyfin p Y hY hpX hρY
  let i := TopRep.continuousModuleHomologyIso (Field.absoluteGaloisGroup E) Y 2
  have hvanish (w : continuousCohomology 2 Y) : w = 0 := by
    have hid : 𝟙 (((TopRep.continuousModuleComplexFunctor
        (Field.absoluteGaloisGroup E)).obj Y).homology 2) = 0 :=
      hzero.eq_of_src _ _
    have hw : i.inv w = 0 :=
      CategoryTheory.ConcreteCategory.congr_hom hid (i.inv w)
    calc
      w = i.hom (i.inv w) :=
        (CategoryTheory.ConcreteCategory.congr_hom i.inv_hom_id w).symm
      _ = 0 := by rw [hw]; exact map_zero i.hom.hom
  apply ContinuousCohomology.restriction_equiv_injective e X 2
  exact (hvanish _).trans
    (map_zero (ContinuousCohomology.map
      (e : Field.absoluteGaloisGroup E →ₜ*
        ↥(H : Subgroup (Field.absoluteGaloisGroup F)))
      (𝟙 Y) 2).hom).symm

/-- Geometric Tsen vanishing for all actual finite integral coefficient
representations killed by p, with no restriction on their Galois action. -/
theorem absoluteGalois_finiteIntegralH2_eq_zero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (X : TopRep.{u} ℤ (Field.absoluteGaloisGroup F))
    [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2))
    (hpX : ∀ v : X, (p : ℕ) • v = 0)
    (v : continuousCohomology 2 X) : v = 0 := by
  have : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  let : Module ℤ X := X.hV2
  obtain ⟨H, hindex, hρ⟩ :=
    TopRep.exists_openSubgroup_primeToIndex_pGroup_image
      ℤ (Field.absoluteGaloisGroup F) X hX (p : ℕ)
  apply ContinuousCohomology.H2_eq_zero_of_primeToIndex_open_restriction
    X H (p : ℕ) hpX hindex ?_ v
  intro w
  exact openAbsoluteGalois_finiteIntegralH2_eq_zero_of_pGroup_image
    K x hx hfin p H (TopRep.res H.toSubgroup.subtype X)
    (hX.comp (continuous_subtype_val.prodMap continuous_id)) hpX hρ w

/-- Tsen vanishing in degree two for every actual finite discrete integral
coefficient representation of the function field's absolute Galois group. -/
theorem absoluteGalois_finiteContinuousModuleH2_isZero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (X : TopRep.{u} ℤ (Field.absoluteGaloisGroup F))
    [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2)) :
    CategoryTheory.Limits.IsZero
      (((TopRep.continuousModuleComplexFunctor
        (Field.absoluteGaloisGroup F)).obj X).homology 2) := by
  have : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  apply TopRep.continuousModuleH2_isZero_of_prime_coefficients
    (Field.absoluteGaloisGroup F) ?_ X hX
  intro p hp A hAfinite hAdiscrete hA hpA
  let q : ℕ+ := ⟨p, hp.out.pos⟩
  have : Fact (q : ℕ).Prime := ⟨hp.out⟩
  apply TopRep.continuousModuleComplex_isZero_of_cohomology_eq_zero
    (Field.absoluteGaloisGroup F) A 2
  exact absoluteGalois_finiteIntegralH2_eq_zero_of_tsen K x hx hfin
    q A hA hpA

/-- All continuous cohomology in degrees at least two vanishes for actual
discrete coefficients of bounded torsion over the function field.
The finite-coefficient and dimension-shifting steps use actual cochains. -/
theorem absoluteGalois_boundedContinuousModule_isZero_of_tsen
    (K : Type u) [Field K] [IsAlgClosed K]
    {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (X : TopRep.{u} ℤ (Field.absoluteGaloisGroup F))
    [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2))
    (m : ℤ) (hm0 : m ≠ 0) (hm : ∀ v : X, m • v = 0) (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (((TopRep.continuousModuleComplexFunctor
        (Field.absoluteGaloisGroup F)).obj X).homology (n + 2)) := by
  have : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  apply TopRep.continuousModule_isZero_of_degreeTwo
    (Field.absoluteGaloisGroup F) X m ?_ hX hm n
  intro Y hYdiscrete hY hmY
  apply TopRep.continuousModule_isZero_of_finite_coefficients
    (Field.absoluteGaloisGroup F) Y hY m hm0 hmY 1
  intro A hAfinite hAdiscrete hA _hmA
  exact absoluteGalois_finiteContinuousModuleH2_isZero_of_tsen K x hx hfin A hA

end AlgebraicCurve
