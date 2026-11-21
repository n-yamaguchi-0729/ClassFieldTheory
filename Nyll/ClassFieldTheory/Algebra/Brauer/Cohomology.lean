/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Topology.Instances.Int
public import Nyll.GaloisCohomology.Topology.AlgebraicGaloisOrbits
public import Nyll.GaloisCohomology.Topology.DiscreteCoefficientQuotient

/-!
# Cohomological Brauer groups

The coefficients are the units of the separable closure, with the discrete
topology and their original absolute Galois action.
-/

@[expose] public section

noncomputable section

universe u v

namespace ClassFieldTheory.Brauer

variable (K : Type v) (E : Type u) [Field K] [Field E] [Algebra K E]

/-- The actual action on the units of an extension in their discrete topology. -/
def galoisUnitsRep : TopRep.{u} ℤ Gal(E/K) :=
  TopRep.discreteCoefficientTopRep ℤ Gal(E/K) (Rep.ofAlgebraAutOnUnits K E)

/-- The topology on the coefficients is discrete. -/
instance galoisUnitsRep_discrete : DiscreteTopology (galoisUnitsRep K E) :=
  TopRep.discreteCoefficientTopRep_discrete ℤ Gal(E/K) (Rep.ofAlgebraAutOnUnits K E)

/-- The coefficient action evaluates the given automorphism on the original unit. -/
theorem galoisUnitsRep_ρ_apply (σ : Gal(E/K)) (a : Additive Eˣ) :
    (galoisUnitsRep K E).ρ σ a = Additive.ofMul (σ • a.toMul) :=
  rfl

/-- The joint action is continuous for an algebraic extension and the discrete coefficients. -/
theorem galoisUnitsRep_action_continuous [Algebra.IsIntegral K E] :
    Continuous (fun ga : Gal(E/K) × galoisUnitsRep K E =>
      (galoisUnitsRep K E).ρ ga.1 ga.2) := by
  apply continuous_prod_of_discrete_right.mpr
  intro a
  let a' : Additive Eˣ := a
  exact ((GaloisCohomology.isLocallyConstant_galois_units (K := K) a'.toMul).comp
    (fun z : Eˣ => (Additive.ofMul z : galoisUnitsRep K E))).continuous

variable (K : Type u) [Field K] in
/-- The discrete absolute Galois module of units in the separable closure. -/
abbrev unitsRep : TopRep.{u} ℤ Gal(SeparableClosure K/K) :=
  galoisUnitsRep K (SeparableClosure K)

variable (K : Type u) [Field K] in
/-- Cohomological Brauer classes are the actual continuous degree-two classes. -/
abbrev Br : Type u :=
  continuousCohomology 2 (unitsRep K)

end ClassFieldTheory.Brauer
