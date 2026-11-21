/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.Cohomology
public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction
public import Nyll.GaloisCohomology.Kummer.LiftedFiniteGaloisTowerUnitsH2
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.Kummer.UnitsCohomologyCongr
public import Nyll.GaloisCohomology.GroupTheory.H2EquivariantEquivalence
public import Nyll.GaloisCohomology.Topology.DiscreteGroupH2

/-! # Comparing finite continuous and ordinary relative Brauer groups -/

@[expose] public section

noncomputable section
namespace ClassFieldTheory.Brauer

open CategoryTheory TopRep ContinuousCohomology ClassFieldTower.Cohomology

universe u v w

/-- The finite continuous and ordinary field-unit models use the identical
action and carry the original degree-two classes across the comparison. -/
def continuousRelativeUnitsH2Equiv (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    continuousCohomology 2 (galoisUnitsRep K L) ≃+
      groupCohomology (liftedGaloisUnitsRep K L) 2 :=
  ContinuousCohomology.discreteIntegralH2Equiv (galoisUnitsRep K L)

/-- An algebra equivalence between finite extensions identifies their
original continuous relative classes, in independent field universes. -/
def continuousRelativeUnitsH2Congr
    (K : Type u) (L : Type v) (M : Type w) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L] [FiniteDimensional K M]
    (e : L ≃ₐ[K] M) :
    continuousCohomology 2 (galoisUnitsRep K L) ≃+ continuousCohomology 2 (galoisUnitsRep K M) := by
  let f : liftedGaloisUnitsRep K L ≃+ liftedGaloisUnitsRep K M :=
    (Units.mapEquiv e.toMulEquiv).toAdditive
  let h := groupCohomology.equivariantH2AddEquiv (AlgEquiv.autCongr e) f
    (unitsMapEquiv_action K L M e)
  exact (continuousRelativeUnitsH2Equiv K L).trans
    (h.trans (continuousRelativeUnitsH2Equiv K M).symm)

section EquivariantUnits

variable {A : Type v} {B : Type w} {L M : Type u} [Field A] [Field B] [Field L] [Field M]
    [Algebra A L] [Algebra B M]
    (r : Gal(M/B) →ₜ* Gal(L/A)) (i : L →+* M)
    (hi : ∀ (σ : Gal(M/B)) (x : L), i (r σ x) = σ (i x))

/-- The original equivariant map of units over the lifted integer coefficients. -/
def liftedGaloisUnitsMap : Rep.res r.toMonoidHom (liftedGaloisUnitsRep A L) ⟶
    liftedGaloisUnitsRep B M := by
  apply Rep.ofHom
  refine ⟨(ModuleCat.coefficientRingAddHom (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
    (M := ModuleCat.of ℤ (Additive Lˣ)) (N := ModuleCat.of ℤ (Additive Mˣ))
    (Units.map i.toMonoidHom).toAdditive).hom, ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  apply Units.ext
  exact hi σ ((show Additive Lˣ from a).toMul : L)

theorem liftedGaloisUnitsMap_apply (a : Additive Lˣ) :
    (liftedGaloisUnitsMap r i hi).hom a = Additive.ofMul (Units.map i.toMonoidHom a.toMul) :=
  rfl

variable [FiniteDimensional A L] [FiniteDimensional B M]

/-- The comparison preserves any actual equivariant map of finite field units. -/
theorem continuousRelativeUnitsH2Equiv_map (x : continuousCohomology 2 (galoisUnitsRep A L)) :
    continuousRelativeUnitsH2Equiv B M ((ContinuousCohomology.map r (galoisUnitsMap r i hi) 2) x) =
      groupCohomology.map r.toMonoidHom (liftedGaloisUnitsMap r i hi) 2
        (continuousRelativeUnitsH2Equiv A L x) := by
  let X := galoisUnitsRep A L
  let Y := galoisUnitsRep B M
  let φ := galoisUnitsMap r i hi
  let ψ : Rep.res r.toMonoidHom (underlyingIntegralRep X) ⟶ underlyingIntegralRep Y :=
    liftedGaloisUnitsMap r i hi
  obtain ⟨z, rfl⟩ := π_surjective X 2 x
  have hπ : ContinuousCohomology.map r φ 2 (π X 2 z) = π Y 2 (cocyclesMap r φ 2 z) :=
    ConcreteCategory.congr_hom (π_map r φ 2) z
  change discreteIntegralH2Hom Y (ContinuousCohomology.map r φ 2 (π X 2 z)) =
    groupCohomology.map r.toMonoidHom ψ 2 (discreteIntegralH2Hom X (π X 2 z))
  rw [hπ, discreteIntegralH2Hom_π, discreteIntegralH2Hom_π, groupCohomology.H2π_comp_map_apply]
  apply congrArg (groupCohomology.H2π (underlyingIntegralRep Y))
  apply groupCohomology.cocycles₂_ext
  intro a b
  change dehomogenizeIntegralTwo Y (cocyclesMap r φ 2 z) (a, b) =
    ψ (dehomogenizeIntegralTwo X z (r a, r b))
  rw [dehomogenizeIntegralTwo_apply, dehomogenizeIntegralTwo_apply, mappedRelativeCocycle_apply]
  let z₀ := (homogeneousCochains X).iCycles 2 z
  have h₁ : r (1 : Gal(M/B)) = 1 := map_one r
  have h₂ : r (a * b) = r a * r b := map_mul r a b
  have harg : z₀.val (r 1) (r a) (r (a * b)) = z₀.val 1 (r a) (r a * r b) := by
    rw [h₁, h₂]
  exact (congrArg (fun s : X => φ s) harg).trans rfl

end EquivariantUnits

section FiniteInflation

variable (K : Type u) (L M : Type v) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K M] [Normal K L]

/-- The literal restriction map between the finite Galois groups of a tower. -/
def finiteRelativeRestriction : Gal(M/K) →ₜ* Gal(L/K) where
  toMonoidHom := AlgEquiv.restrictNormalHom L
  continuous_toFun := continuous_of_discreteTopology

/-- The finite-relative inflation uses the original inclusion of units. -/
def relativeInflationCoefficientMap :
    TopRep.res (finiteRelativeRestriction K L M).toMonoidHom (galoisUnitsRep K L) ⟶
      galoisUnitsRep K M :=
  galoisUnitsMap (finiteRelativeRestriction K L M) (algebraMap L M)
    (fun σ x => σ.restrictNormal_commutes L x)

/-- The continuous relative inflation induced by the actual restriction and
unit inclusion of the finite tower. -/
def relativeInflation : continuousCohomology 2 (galoisUnitsRep K L) →+
    continuousCohomology 2 (galoisUnitsRep K M) :=
  transportCohomology 2 (finiteRelativeRestriction K L M) (algebraMap L M)
    (fun σ x => σ.restrictNormal_commutes L x)

variable [FiniteDimensional K L]

/-- The ordinary/continuous comparison intertwines the same inflation on
the two representations. -/
theorem continuousRelativeUnitsH2Equiv_inflation
    (x : continuousCohomology 2 (galoisUnitsRep K L)) :
    continuousRelativeUnitsH2Equiv K M (relativeInflation K L M x) =
      liftedFiniteGaloisTowerUnitsH2Inflation K L M (continuousRelativeUnitsH2Equiv K L x) := by
  exact continuousRelativeUnitsH2Equiv_map (finiteRelativeRestriction K L M) (algebraMap L M)
    (fun σ a => σ.restrictNormal_commutes L a) x

end FiniteInflation

section FiniteRestriction

variable (K : Type u) (E : Type v) (M : Type v) [Field K] [Field E] [Field M]
    [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
    [FiniteDimensional K M] [FiniteDimensional E M]

/-- Restriction between the genuine finite Galois groups over two bases. -/
def relativeBaseRestrictionHom : Gal(M/E) →ₜ* Gal(M/K) where
  toMonoidHom := AlgEquiv.restrictScalarsHom K
  continuous_toFun := continuous_of_discreteTopology

/-- The lower-to-upper restriction on relative continuous cohomology has
the original automorphism map and leaves the actual unit coefficients fixed. -/
def relativeBaseRestriction : continuousCohomology 2 (galoisUnitsRep K M) →+
    continuousCohomology 2 (galoisUnitsRep E M) :=
  transportCohomology 2 (relativeBaseRestrictionHom K E M) (RingHom.id M) (fun _ _ => rfl)

/-- The ordinary/continuous comparison intertwines actual relative base restriction. -/
theorem continuousRelativeUnitsH2Equiv_baseRestriction
    (x : continuousCohomology 2 (galoisUnitsRep K M)) :
    continuousRelativeUnitsH2Equiv E M (relativeBaseRestriction K E M x) =
      liftedFiniteGaloisTowerUnitsH2Restriction K E M (continuousRelativeUnitsH2Equiv K M x) := by
  let r := relativeBaseRestrictionHom K E M
  let i := RingHom.id M
  let hi (σ : Gal(M/E)) (a : M) : i (r σ a) = σ (i a) := rfl
  let q : Gal(M/E) →* Gal(M/K) := AlgEquiv.restrictScalarsHom K
  let p := liftedGaloisUnitsMap (A := K) (B := E) (L := M) (M := M) r i hi
  let p₀ := liftedFiniteGaloisTowerUnitsRestrictionRepHom K E M
  have hc : p.hom.toLinearMap = p₀.hom.toLinearMap := by
    apply LinearMap.ext
    intro a
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  have hm := continuousRelativeUnitsH2Equiv_map (A := K) (B := E) (L := M) (M := M) r i hi x
  have he := groupCohomology.map_congr
    (f := r.toMonoidHom) (g := q) (φ := p) (ψ := p₀) rfl hc 2
  exact hm.trans (ConcreteCategory.congr_hom he (continuousRelativeUnitsH2Equiv K M x))

end FiniteRestriction

end ClassFieldTheory.Brauer
