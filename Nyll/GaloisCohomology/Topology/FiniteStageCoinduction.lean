/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Coinduced
public import Nyll.GaloisCohomology.Topology.DiscreteCoefficientQuotient
public import Nyll.GaloisCohomology.Topology.OpenSubgroupCoinduction

/-! # Lift of finite-stage coinduction to a continuous quotient map -/

@[expose] public section

open CategoryTheory ContRepresentation TopRep

noncomputable section

namespace TopRep

universe u

/-- An equivariant additive equivalence of discrete integral coefficients
gives an isomorphism of the actual continuous representations. -/
def discreteIntegralCoefficientIso {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B : TopRep.{u} ℤ G} [DiscreteTopology A] [DiscreteTopology B]
    (e : A ≃+ B) (he : ∀ g a, e (A.ρ g a) = B.ρ g (e a)) : A ≅ B := by
  let : Module ℤ A := A.hV2
  let : Module ℤ B := B.hV2
  let eₗ : A ≃ₗ[ℤ] B := e.toIntLinearEquiv (modM := A.hV2) (modM₂ := B.hV2)
  let f : ContIntertwiningMap A.ρ B.ρ :=
    { toContinuousLinearMap :=
        ⟨eₗ.toLinearMap, continuous_of_discreteTopology (f := eₗ.toLinearMap)⟩
      isIntertwining' := fun g => ContinuousLinearMap.ext (he g) }
  let f' : ContIntertwiningMap B.ρ A.ρ :=
    { toContinuousLinearMap :=
        ⟨eₗ.symm.toLinearMap, continuous_of_discreteTopology (f := eₗ.symm.toLinearMap)⟩
      isIntertwining' := fun g => ContinuousLinearMap.ext fun b => by
        apply e.injective
        change e (e.symm (B.ρ g b)) = e (A.ρ g (e.symm b))
        rw [e.apply_symm_apply, he, e.apply_symm_apply] }
  exact
    { hom := ConcreteCategory.ofHom (C := TopRep ℤ G) f
      inv := ConcreteCategory.ofHom (C := TopRep ℤ G) f'
      hom_inv_id := by
        apply TopRep.hom_ext
        apply ContIntertwiningMap.ext
        apply ContinuousLinearMap.ext
        intro a
        exact e.symm_apply_apply a
      inv_hom_id := by
        apply TopRep.hom_ext
        apply ContIntertwiningMap.ext
        apply ContinuousLinearMap.ext
        intro b
        exact e.apply_symm_apply b }

variable {G Q : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [IsTopologicalGroup Q]
    (r : G →ₜ* Q) (S : OpenSubgroup Q)

/-- The actual inverse image of an open subgroup at the finite stage. -/
abbrev finiteStageOpenSubgroup : OpenSubgroup G :=
  S.comap r.toMonoidHom r.continuous

/-- The quotient map on the actual inverse-image subgroup. -/
def finiteStageSubgroupMap : ↥(finiteStageOpenSubgroup r S).toSubgroup →ₜ* ↥S.toSubgroup where
  toMonoidHom := MonoidHom.codRestrict
    (r.toMonoidHom.comp (finiteStageOpenSubgroup r S).toSubgroup.subtype)
    S.toSubgroup (fun s => s.property)
  continuous_toFun := (r.continuous.comp continuous_subtype_val).subtype_mk _

variable (A : TopRep.{u} ℤ (↥S.toSubgroup)) [DiscreteTopology A]

/-- Restriction of the given finite coefficient along the actual subgroup quotient. -/
abbrev finiteStageRestrictedCoefficient :
    TopRep.{u} ℤ (↥(finiteStageOpenSubgroup r S).toSubgroup) :=
  TopRep.res (finiteStageSubgroupMap r S).toMonoidHom A

/-- The original finite coinduced representation equipped with the discrete topology. -/
abbrev finiteStageDiscreteCoinducedCoefficient : TopRep.{u} ℤ Q := by
  let : Module ℤ A := A.hV2
  let ρ : Representation ℤ ↥S.toSubgroup A := A.ρ.toRepresentation
  let X := Representation.coindV S.toSubgroup.subtype ρ
  let : Module ℤ X := X.module
  exact discreteCoefficientTopRep ℤ Q
    (Rep.of (X := X) (Representation.coind S.toSubgroup.subtype ρ))

/-- Continuous coinduction on the ambient group from the actual restricted stage. -/
abbrev finiteStageAmbientCoinducedCoefficient : TopRep.{u} ℤ G :=
  openCoinduced (finiteStageOpenSubgroup r S) (finiteStageRestrictedCoefficient r S A)

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
/-- The subgroup action is continuous because it factors through the discrete stage. -/
theorem finiteStageSubgroupAction_continuous :
    Continuous (fun ga : ↥(finiteStageOpenSubgroup r S).toSubgroup ×
        finiteStageRestrictedCoefficient r S A => (finiteStageRestrictedCoefficient r S A).ρ
      ga.1 ga.2) := by
  let f : (↥S.toSubgroup) × A → A := fun sa => A.ρ sa.1 sa.2
  have hf : Continuous f := continuous_of_discreteTopology
  exact hf.comp (((finiteStageSubgroupMap r S).continuous.comp continuous_fst).prodMk
    continuous_snd)

/-- Composition with the quotient is the canonical map on coinduced coefficients. -/
def finiteStageCoinducedLift : finiteStageDiscreteCoinducedCoefficient S A →ₗ[ℤ]
    finiteStageAmbientCoinducedCoefficient r S A := by
  let F₀ (f : (finiteStageDiscreteCoinducedCoefficient S A)) : C(G, A) := ⟨fun g => f.val (r g),
    (continuous_of_discreteTopology (f := f.val)).comp r.continuous⟩
  have hF (f : finiteStageDiscreteCoinducedCoefficient S A)
      (h : ↥(finiteStageOpenSubgroup r S).toSubgroup) (g : G) :
      F₀ f ((h : G) * g) = ((finiteStageRestrictedCoefficient r S A)).ρ h (F₀ f g) := by
    change f.val (r ((h : G) * g)) = A.ρ (finiteStageSubgroupMap r S h) (f.val (r g))
    rw [map_mul]
    exact f.property (finiteStageSubgroupMap r S h) (r g)
  exact
    { toFun := fun f => ⟨F₀ f, hF f⟩
      map_add' := fun _ _ => Subtype.ext (ContinuousMap.ext (fun _ => rfl))
      map_smul' := fun _ _ => Subtype.ext (ContinuousMap.ext (fun _ => rfl)) }

omit [IsTopologicalGroup Q] [DiscreteTopology A] in
/-- Invariant continuous functions descend along a surjective finite quotient. -/
theorem finiteStageCoinducedLift_bijective (hr : Function.Surjective r) :
    Function.Bijective (finiteStageCoinducedLift r S A) := by
  let F₀ := finiteStageCoinducedLift r S A
  constructor
  · intro a b hab
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := hr q
    exact congrArg (fun f : (finiteStageAmbientCoinducedCoefficient r S A) => f.val g) hab
  · intro f
    have hdesc (g g' : G) (h : r g = r g') : f.val g = f.val g' := by
      have hz : r (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
      let u : ↥(finiteStageOpenSubgroup r S).toSubgroup :=
        ⟨g * g'⁻¹, show r (g * g'⁻¹) ∈ S from hz ▸ S.one_mem⟩
      have hu : finiteStageSubgroupMap r S u = 1 := Subtype.ext hz
      have hf := f.property u g'
      change f.val (g * g'⁻¹ * g') = A.ρ (finiteStageSubgroupMap r S u) (f.val g') at hf
      rw [mul_assoc, inv_mul_cancel, mul_one, hu, map_one] at hf
      exact hf
    let s (q : Q) := Classical.choose (hr q)
    have hs (q : Q) : r (s q) = q := Classical.choose_spec (hr q)
    let a (q : Q) := f.val (s q)
    have ha (g : G) : a (r g) = f.val g := hdesc (s (r g)) g (hs _)
    have hc (t : ↥S.toSubgroup) (q : Q) : a ((t : Q) * q) = A.ρ t (a q) := by
      let u : ↥(finiteStageOpenSubgroup r S).toSubgroup :=
        ⟨s t, show r (s t) ∈ S from (hs t).symm ▸ t.property⟩
      have hu : finiteStageSubgroupMap r S u = t := Subtype.ext (hs t)
      have hf := f.property u (s q)
      change f.val (s t * s q) = A.ρ (finiteStageSubgroupMap r S u) (a q) at hf
      calc
        a ((t : Q) * q) = a (r (s t * s q)) := by rw [map_mul, hs t, hs q]
        _ = f.val (s t * s q) := ha _
        _ = A.ρ t (a q) := hf.trans (congrArg (fun v => A.ρ v (a q)) hu)
    refine ⟨⟨a, hc⟩, Subtype.ext (ContinuousMap.ext ?_)⟩
    exact ha

/-- Pullback along a surjective continuous quotient sends actual finite
coinduction to actual continuous coinduction on the inverse-image subgroup. -/
def finiteStageCoinductionIso [CompactSpace G] (hr : Function.Surjective r) :
    TopRep.res r.toMonoidHom (finiteStageDiscreteCoinducedCoefficient S A) ≅
      finiteStageAmbientCoinducedCoefficient r S A := by
  let A₀ := TopRep.res r.toMonoidHom (finiteStageDiscreteCoinducedCoefficient S A)
  let e := LinearEquiv.ofBijective (finiteStageCoinducedLift r S A)
    (finiteStageCoinducedLift_bijective r S A hr)
  let : DiscreteTopology (finiteStageAmbientCoinducedCoefficient r S A) :=
    openCoinduced_discrete (finiteStageOpenSubgroup r S) (finiteStageRestrictedCoefficient r S A)
      (finiteStageSubgroupAction_continuous r S A)
  have he (g : G) (a : A₀) :
      e (A₀.ρ g a) = (finiteStageAmbientCoinducedCoefficient r S A).ρ g (e a) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change a.val (r t * r g) = a.val (r (t * g))
    rw [map_mul]
  exact discreteIntegralCoefficientIso e.toAddEquiv he

end TopRep
