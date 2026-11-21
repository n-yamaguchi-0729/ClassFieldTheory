/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.Cohomology
public import Nyll.GaloisCohomology.Topology.DiscreteGroupH2

/-!
# Brauer groups of separably closed fields

An automorphism of the separable closure of a separably closed field fixes the
whole field. Its actual positive degree cohomology therefore vanishes.
-/

@[expose] public section

universe u

namespace ClassFieldTheory.Brauer

variable (K : Type u) [Field K] [IsSepClosed K]

/-- The cohomological Brauer group of a separably closed field is trivial. -/
theorem subsingleton_of_isSepClosed : Subsingleton (Br K) := by
  have hsurj := IsSepClosed.algebraMap_surjective K (SeparableClosure K)
  have : FiniteDimensional K (SeparableClosure K) :=
    Module.Finite.of_surjective (Algebra.linearMap K (SeparableClosure K)) hsurj
  have : Subsingleton Gal(SeparableClosure K/K) := by
    constructor
    intro σ τ
    apply AlgEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := hsurj x
    rw [σ.commutes, τ.commutes]
  let X := unitsRep K
  have : Subsingleton (groupCohomology (ContinuousCohomology.underlyingIntegralRep X) 2) :=
    ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton
        (ContinuousCohomology.underlyingIntegralRep X) 1)
  exact (ContinuousCohomology.discreteIntegralH2Equiv X).injective.subsingleton

end ClassFieldTheory.Brauer
