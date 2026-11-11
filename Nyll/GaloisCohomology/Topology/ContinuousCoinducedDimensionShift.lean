/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.DiscreteCoinducedQuotient
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness

/-!
# Actual continuous dimension shifting by coinduction

For compact groups and discrete coefficients with continuous action, the
actual quotient of coinduction by constants gives connecting isomorphisms
in every positive degree. The middle acyclicity is proved by explicit
continuous primitives, rather than assumed.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits ContRepresentation

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (X : TopRep.{u} ℤ G) [DiscreteTopology X]

/-- The actual coefficient sequence consisting of constants, coinduction,
and its quotient by constants. -/
def coinducedCoefficientShortComplex : ShortComplex (TopRep.{u} ℤ G) := by
  have : DiscreteTopology X.coind₁ := coinduced_discreteTopology G X
  let i : X ⟶ X.coind₁ := (coind₁ι (k := ℤ) (G := G)).app X
  let q := coinducedQuotientProjection ℤ G X
  exact ShortComplex.mk i q (by
    let : Module ℤ X := X.hV2
    let : Module ℤ (coinducedQuotient ℤ G X) :=
      (coinducedQuotient ℤ G X).hV2
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := X.ρ)
      (π₂ := (coinducedQuotient ℤ G X).ρ)
    apply ContinuousLinearMap.ext
    intro x
    exact (coinducedQuotientProjection_eq_zero_iff ℤ G X (i x)).mpr ⟨x, rfl⟩)

/-- The actual coefficient sequence induces a short exact sequence of
continuous module complexes. -/
theorem coinducedContinuousModule_shortExact
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    ((coinducedCoefficientShortComplex G X).map
      (continuousModuleComplexFunctor G)).ShortExact := by
  have : DiscreteTopology X.coind₁ := coinduced_discreteTopology G X
  let S := coinducedCoefficientShortComplex G X
  have : DiscreteTopology S.X₂ := coinduced_discreteTopology G X
  have : DiscreteTopology S.X₃ := coinducedQuotient_discrete ℤ G X
  apply continuousModuleComplex_shortExact G S
  · intro x y h
    exact congrArg (fun f : C(G, X) => f 1) h
  · exact coinducedQuotientProjection_surjective ℤ G X
  · intro f hf
    exact (coinducedQuotientProjection_eq_zero_iff ℤ G X f).mp hf
  · exact hX
  · exact coinduced_action_continuous G X hX

omit [DiscreteTopology X] in
/-- The actual middle coinduced module complex is acyclic in positive degrees. -/
theorem coinducedContinuousModule_isZero (n : ℕ) :
    IsZero (((continuousModuleComplexFunctor G).obj X.coind₁).homology (n + 1)) :=
  continuousModuleComplex_isZero_of_cohomology_eq_zero G X.coind₁ (n + 1)
    (continuousCohomology_coinduced_eq_zero G X n)

/-- The actual connecting map shifts positive continuous cohomology from
the quotient coefficients back to the original coefficients. -/
def coinducedContinuousDimensionShift
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) (n : ℕ) :
    ((continuousModuleComplexFunctor G).obj
      (coinducedQuotient ℤ G X)).homology (n + 1) ≅
      ((continuousModuleComplexFunctor G).obj X).homology (n + 2) :=
  (coinducedContinuousModule_shortExact G X hX).δIso (n + 1) (n + 2) rfl
    (coinducedContinuousModule_isZero G X n)
    (coinducedContinuousModule_isZero G X (n + 1))

/-- A uniform degree-two vanishing theorem for discrete coefficients killed
by an integer implies vanishing in all degrees at least two. The degree-two
hypothesis is explicit; this criterion does not supply geometric vanishing. -/
theorem continuousModule_isZero_of_degreeTwo
    (m : ℤ)
    (h₂ : ∀ (Y : TopRep.{u} ℤ G) [DiscreteTopology Y],
      Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2) →
      (∀ y : Y, m • y = 0) →
      IsZero (((continuousModuleComplexFunctor G).obj Y).homology 2))
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (hm : ∀ x : X, m • x = 0) (n : ℕ) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology (n + 2)) := by
  induction n generalizing X with
  | zero => exact h₂ X hX hm
  | succ n ih =>
    have : DiscreteTopology X.coind₁ := coinduced_discreteTopology G X
    let Q := coinducedQuotient ℤ G X
    have : DiscreteTopology Q := coinducedQuotient_discrete ℤ G X
    have hQ : Continuous (fun gq : G × Q => Q.ρ gq.1 gq.2) :=
      coinducedQuotient_action_continuous ℤ G X hX
    have hmQ : ∀ q : Q, m • q = 0 := by
      intro q
      exact (int_smul_eq_zsmul Q.hV2 m q).symm.trans
        (coinducedQuotient_smul_eq_zero ℤ G X m
          (fun x => (int_smul_eq_zsmul X.hV2 m x).trans (hm x)) q)
    exact IsZero.of_iso (ih Q hQ hmQ)
      (coinducedContinuousDimensionShift G X hX (n + 1)).symm

end TopRep
