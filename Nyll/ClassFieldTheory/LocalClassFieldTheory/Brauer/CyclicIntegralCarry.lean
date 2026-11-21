/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicNorm
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteRepresentative
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.IntegralUnitClass
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryRestriction

/-! # Integral representatives of the cyclic carry class -/

@[expose] public section

noncomputable section

open CategoryTheory TopRep ContinuousCohomology ClassFieldTower.Cohomology

namespace ClassFieldTheory.Brauer

universe u

section Finite

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G] [Fintype G] [IsCyclic G]
  (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)

/-- The integral carry cocycle in the inhomogeneous bar resolution. -/
def finiteIntegralCarryCocycle :
    groupCohomology.cocycles₂ (underlyingIntegralRep (trivialIntegralTopRep G)) := by
  let : CommGroup G := IsCyclic.commGroup
  let X := underlyingIntegralRep (trivialIntegralTopRep G)
  let a : LinearMap.ker (Rep.applyAsHom X g - 𝟙 X).hom.toLinearMap :=
    ⟨ULift.up 1, by
      change ULift.up (1 : ℤ) - ULift.up (1 : ℤ) = 0
      exact sub_self _⟩
  exact finiteCyclicCarryTwoCocycle X g hg a

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G] in
private theorem finiteIntegralCarryCocycle_apply (x y : G) :
    finiteIntegralCarryCocycle g hg (x, y) = ULift.up (finiteCyclicCarry g hg x y : ℤ) := by
  let : CommGroup G := IsCyclic.commGroup
  unfold finiteIntegralCarryCocycle
  rw [finiteCyclicCarryTwoCocycle_apply]
  apply ULift.ext
  change finiteCyclicCarry g hg x y • (1 : ℤ) = _
  rw [nsmul_eq_mul, mul_one]

/-- The continuous class of the integral carry for the specified generator. -/
def finiteIntegralCarry : continuousCohomology 2 (trivialIntegralTopRep G) :=
  (discreteIntegralH2Equiv (trivialIntegralTopRep G)).symm
    (groupCohomology.H2π _ (finiteIntegralCarryCocycle g hg))

/-- On the original bar resolution the integer carry is represented by the
same carry on the two consecutive group increments. -/
theorem exists_finiteIntegralCarry_representative :
    ∃ z : cocycles (trivialIntegralTopRep G) 2,
      π (trivialIntegralTopRep G) 2 z = finiteIntegralCarry g hg ∧
        ∀ a b c : G, ((homogeneousCochains (trivialIntegralTopRep G)).iCycles 2 z).val a b c =
          ULift.up (finiteCyclicCarry g hg (a⁻¹ * b) (b⁻¹ * c) : ℤ) := by
  let X := trivialIntegralTopRep G
  obtain ⟨z, hz⟩ := dehomogenizeIntegralTwo_surjective X (finiteIntegralCarryCocycle g hg)
  refine ⟨z, ?_, ?_⟩
  · apply (discreteIntegralH2Equiv X).injective
    change discreteIntegralH2Hom X (π X 2 z) =
      (discreteIntegralH2Equiv X) ((discreteIntegralH2Equiv X).symm (groupCohomology.H2π _
        (finiteIntegralCarryCocycle g hg)))
    rw [discreteIntegralH2Hom_π, hz, AddEquiv.apply_symm_apply]
  · intro a b c
    rw [homogeneousIntegralTwo_apply, hz]
    change (finiteIntegralCarryCocycle g hg) (a⁻¹ * b, b⁻¹ * c) = _
    exact finiteIntegralCarryCocycle_apply g hg (a⁻¹ * b) (b⁻¹ * c)

end Finite

section RestrictionComposition

variable {G H J : Type u}
  [Group G] [Group H] [Group J] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup J]

/-- Successive restrictions of integral cohomology compose as the actual
continuous group homomorphisms. -/
theorem integralRestriction_comp_apply
    (r : H →ₜ* G) (s : J →ₜ* H)
    (x : continuousCohomology 2 (trivialIntegralTopRep G)) :
    integralRestriction s (integralRestriction r x) = integralRestriction (r.comp s) x := by
  let X := trivialIntegralTopRep G
  let Y := trivialIntegralTopRep H
  let Z := trivialIntegralTopRep J
  let f := integralRestrictionCoefficient r
  let g := integralRestrictionCoefficient s
  have hfg : (TopRep.resFunctor s.toMonoidHom).map f ≫ g =
      integralRestrictionCoefficient (r.comp s) := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro a
    rfl
  have h := map_comp (X := X) (Y := Y) (Z := Z) r s f g 2
  have h' := congrArg (fun k : TopRep.res (r.comp s).toMonoidHom X ⟶ Z =>
    map (r.comp s) k 2) hfg
  exact (ConcreteCategory.congr_hom (h.symm.trans h') x)

end RestrictionComposition

section Comparison

variable {G H J : Type u}
  [Group G] [Group H] [Group J] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup J]
  [DiscreteTopology G] [DiscreteTopology H] [Fintype G] [Fintype H] [IsCyclic G] [IsCyclic H]
  (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
  (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)

/-- Pullback through a common action gives the same integral carry when
the chosen generators agree under its finite group equivalence. -/
theorem integralRestriction_finiteIntegralCarry_factors
    (r : J →ₜ* G) (s : J →ₜ* H) (e : H ≃* G)
    (he : e h = g) (hrs : ∀ x : J, r x = e (s x)) :
    integralRestriction r (finiteIntegralCarry g hg) =
      integralRestriction s (finiteIntegralCarry h hh) := by
  obtain ⟨z, hz, hzc⟩ := exists_finiteIntegralCarry_representative g hg
  obtain ⟨w, hw, hwc⟩ := exists_finiteIntegralCarry_representative h hh
  rw [← hz, ← hw, integralRestriction_π, integralRestriction_π]
  let X := trivialIntegralTopRep J
  apply congrArg (π X 2)
  apply cochain_cocycle_injective X 2
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro b
  apply ContinuousMap.ext
  intro c
  have hz' := (mappedRelativeCocycle_apply (Y := X) r
      (integralRestrictionCoefficient r) z a b c).trans
    (congrArg (fun z => integralRestrictionCoefficient r z) (hzc (r a) (r b) (r c)))
  have hw' := (mappedRelativeCocycle_apply (Y := X) s
      (integralRestrictionCoefficient s) w a b c).trans
    (congrArg (fun z => integralRestrictionCoefficient s z) (hwc (s a) (s b) (s c)))
  refine hz'.trans (Eq.trans ?_ hw'.symm)
  change ULift.up (finiteCyclicCarry g hg ((r a)⁻¹ * r b) ((r b)⁻¹ * r c) : ℤ) =
    ULift.up (finiteCyclicCarry h hh ((s a)⁻¹ * s b) ((s b)⁻¹ * s c) : ℤ)
  have h₁ : (r a)⁻¹ * r b = e ((s a)⁻¹ * s b) := by
    rw [hrs a, hrs b, map_mul, map_inv]
  have h₂ : (r b)⁻¹ * r c = e ((s b)⁻¹ * s c) := by
    rw [hrs b, hrs c, map_mul, map_inv]
  rw [h₁, h₂]
  exact congrArg (fun n : ℕ => (ULift.up (n : ℤ) : ULift.{u} ℤ))
    (finiteCyclicCarry_map_of_generator_power g hg h hh e.toMonoidHom 1 (by decide)
      (by rw [one_mul]; exact Nat.card_congr e.symm.toEquiv)
      (by rw [pow_one]; exact he) ((s a)⁻¹ * s b) ((s b)⁻¹ * s c))

end Comparison

section FieldUnits

variable {K : Type u} [Field K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [IsCyclic Gal(E/K)]
  (g : Gal(E/K)) (hg : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers g)

/-- The actual cyclic Brauer class is obtained by multiplying the pulled
back integral carry by the same base unit. -/
theorem cyclicBrauerClass_eq_unitsIntegralClass (a : Kˣ) :
    cyclicBrauerClass E g hg a =
      unitsIntegralClass K a
        (integralRestriction (finiteGaloisRestriction E) (finiteIntegralCarry g hg)) := by
  let : CommGroup Gal(E/K) := IsCyclic.commGroup
  let X := galoisUnitsRep K E
  let B := liftedGaloisUnitsRep K E
  let e := continuousRelativeUnitsH2Equiv K E
  let d := finiteCyclicCarryTwoCocycle (liftedGaloisUnitsRep K E) g hg (liftedBaseUnitCycle K E g a)
  obtain ⟨w, hw⟩ := dehomogenizeIntegralTwo_surjective X d
  have hπ : π X 2 w = cyclicContinuousUnitClass K E g hg (Additive.ofMul a) := by
    apply e.injective
    have hmap := discreteIntegralH2Hom_π X w
    have hcoe := congrArg (fun z : groupCohomology.cocycles₂ B => groupCohomology.H2π B z) hw
    exact hmap.trans (hcoe.trans (e.apply_symm_apply (groupCohomology.H2π B d)).symm)
  let aE : X := Additive.ofMul (α := Eˣ) (Units.map (algebraMap K E).toMonoidHom a)
  have hfix (σ : Gal(E/K)) : X.ρ σ aE = aE := by
    apply Additive.toMul.injective
    apply Units.ext
    exact σ.commutes (a : K)
  have hval (x y z : Gal(E/K)) : ((homogeneousCochains X).iCycles 2 w).val x y z =
      finiteCyclicCarry g hg (x⁻¹ * y) (y⁻¹ * z) • aE := by
    rw [homogeneousIntegralTwo_apply, hw]
    let n := finiteCyclicCarry g hg (x⁻¹ * y) (y⁻¹ * z)
    have hn : (d (x⁻¹ * y, y⁻¹ * z) : X) = n • aE :=
      finiteCyclicCarryTwoCocycle_apply B g hg (liftedBaseUnitCycle K E g a) (x⁻¹ * y) (y⁻¹ * z)
    calc
      X.ρ x (d (x⁻¹ * y, y⁻¹ * z)) = X.ρ x (n • aE) :=
        congrArg (fun b : X => X.ρ x b) hn
      _ = n • X.ρ x aE := map_nsmul (X.ρ x) n aE
      _ = n • aE := congrArg (fun b : X => n • b) (hfix x)
  obtain ⟨z, hz, hzc⟩ := exists_finiteIntegralCarry_representative g hg
  rw [cyclicBrauerClass, ← hπ, ← hz, finiteInflation_π, integralRestriction_π,
    unitsIntegralClass_π]
  let Y := unitsRep K
  apply congrArg (π Y 2)
  apply cochain_cocycle_injective Y 2
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro t
  let r := finiteGaloisRestriction E
  let n := finiteCyclicCarry g hg ((r x)⁻¹ * r y) ((r y)⁻¹ * r t)
  let i := integralRestrictionCoefficient r
  let m := unitScalarCoefficientMap K a
  let e := finiteInflationCoefficientMap E
  let b : Y := Additive.ofMul (α := (SeparableClosure K)ˣ)
    (Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
  let z' := cocyclesMap r i 2 z
  have hleft := (mappedRelativeCocycle_apply (X := X) (Y := Y) r e w x y t).trans
    (congrArg (fun a : X => e a) (hval (r x) (r y) (r t)))
  have hright := (mappedRelativeCocycle_apply (Y := Y) (ContinuousMonoidHom.id _) m z' x y t).trans
    (congrArg (fun a => m a) ((mappedRelativeCocycle_apply r i z x y t).trans
      (congrArg (fun a => i a) (hzc (r x) (r y) (r t)))))
  have hb : e aE = b := by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  have hm : m (ULift.up (n : ℤ)) = n • b :=
    (unitScalarCoefficientMap_apply K a (ULift.up (n : ℤ))).trans (natCast_zsmul b n)
  exact hleft.trans ((map_nsmul e.hom.toContinuousLinearMap n aE).trans
    ((congrArg (fun b : Y => n • b) hb).trans (hm.symm.trans hright.symm)))

end FieldUnits

end ClassFieldTheory.Brauer
