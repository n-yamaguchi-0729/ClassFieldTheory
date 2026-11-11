/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.InvariantCoefficientSubrepresentation
public import Nyll.GaloisCohomology.Topology.InvariantCoefficientExactness
public import Nyll.GaloisCohomology.Topology.ContinuousH2FiniteIndexTrace
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Prime-coefficient dévissage for continuous degree-two cohomology

The p-torsion submodule and its actual quotient reduce a finite coefficient
module's annihilator. Thus vanishing for all finite modules killed by a
prime implies vanishing for every finite discrete coefficient module.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits ContRepresentation

namespace TopRep

universe u v

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- Vanishing for every prime-annihilated finite coefficient module implies
vanishing for arbitrary actual finite discrete coefficients. -/
theorem continuousModuleH2_isZero_of_prime_coefficients
    (hprime : ∀ (p : ℕ) [Fact p.Prime] (A : TopRep.{u} ℤ G)
      [Finite A] [DiscreteTopology A],
      Continuous (fun ga : G × A => A.ρ ga.1 ga.2) →
      (∀ a : A, p • a = 0) →
      IsZero (((continuousModuleComplexFunctor G).obj A).homology 2))
    (X : TopRep.{u} ℤ G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology 2) := by
  classical
  suffices step : ∀ n : ℕ, 0 < n →
      ∀ (Y : TopRep.{u} ℤ G) [Finite Y] [DiscreteTopology Y],
      Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2) →
      (∀ y : Y, n • y = 0) →
      IsZero (((continuousModuleComplexFunctor G).obj Y).homology 2) by
    exact step (Nat.card X) Nat.card_pos X hX (fun _ => card_nsmul_eq_zero')
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn Y hfin hdisc hY hnY
    by_cases hn1 : n = 1
    · apply continuousModuleComplex_isZero_of_cohomology_eq_zero G Y 2
      intro v
      have hv := ContinuousCohomology.nsmul_H2_eq_zero_of_coefficients Y n hnY v
      simpa only [hn1, one_nsmul] using hv
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn1
      have : Fact p.Prime := ⟨hp⟩
      let : Module ℤ Y := Y.hV2
      let W : Submodule ℤ Y := LinearMap.ker (p • (LinearMap.id : Y →ₗ[ℤ] Y))
      have hW : ∀ g : G, W ≤ W.comap (Y.ρ g).toLinearMap := by
        intro g y hy
        change p • y = 0 at hy
        change p • Y.ρ g y = 0
        rw [← map_nsmul, hy, map_zero]
      let A := invariantSubmoduleTopRep ℤ G Y W hW
      let : Module ℤ A := A.hV2
      let φ : A ⟶ Y := invariantSubmoduleInclusion ℤ G Y W hW
      have : Finite A := inferInstanceAs (Finite W)
      have : DiscreteTopology A := invariantSubmoduleTopRep_discrete ℤ G Y W hW
      have hAcont : Continuous (fun ga : G × A => A.ρ ga.1 ga.2) :=
        invariantSubmoduleTopRep_action_continuous ℤ G Y W hW hY
      have hpA : ∀ a : A, p • a = 0 := by
        intro a
        apply Subtype.ext
        exact a.property
      have hA := hprime p A hAcont hpA
      let U := LinearMap.range φ.hom.toContinuousLinearMap.toLinearMap
      have hU : ∀ g : G, U ≤ U.comap (Y.ρ g).toLinearMap := by
        rintro g y ⟨a, rfl⟩
        exact ⟨A.ρ g a, φ.hom.isIntertwining g a⟩
      let Q := invariantCoefficientQuotient ℤ G Y U hU
      let q : Y ⟶ Q := invariantCoefficientQuotientProjection ℤ G Y U hU
      have : Finite (Y ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
      have : Finite Q := inferInstanceAs (Finite (Y ⧸ U))
      have : DiscreteTopology Q := invariantCoefficientQuotient_discrete ℤ G Y U hU
      have hQcont : Continuous (fun gq : G × Q => Q.ρ gq.1 gq.2) :=
        invariantCoefficientQuotient_action_continuous ℤ G Y U hU hY
      have hmQ : ∀ z : Q, (n / p) • z = 0 := by
        intro z
        obtain ⟨y, rfl⟩ := invariantCoefficientQuotientProjection_surjective ℤ G Y U hU z
        rw [← map_nsmul]
        apply (invariantCoefficientQuotientProjection_eq_zero_iff ℤ G Y U hU _).mpr
        have hy : (n / p) • y ∈ W := by
          change p • ((n / p) • y) = 0
          rw [← mul_nsmul, Nat.div_mul_cancel hpd]
          exact hnY y
        exact ⟨⟨(n / p) • y, hy⟩, rfl⟩
      have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpd) hp.pos
      have hlt : n / p < n := Nat.div_lt_self hn hp.one_lt
      have hQ := ih (n / p) hlt hm Q hQcont hmQ
      have hS := coefficientRangeContinuousModule_shortExact G A Y φ
        (invariantSubmoduleInclusion_injective ℤ G Y W hW) hAcont hY
      exact (hS.homology_exact₂ 2).isZero_X₂ (hA.eq_of_src _ _) (hQ.eq_of_tgt _ _)

/-- Prime dévissage for an independently sized original coefficient module.
The prime test uses the same working group as its actual lifted homogeneous complex. -/
theorem universeLiftContinuousModuleH2_isZero_of_prime_coefficients
    (hprime : ∀ (p : ℕ) [Fact p.Prime]
      (A : TopRep.{max u v} ℤ (ULift.{v} G)) [Finite A] [DiscreteTopology A],
      Continuous (fun ga : ULift.{v} G × A => A.ρ ga.1 ga.2) →
      (∀ a : A, p • a = 0) →
      IsZero (((continuousModuleComplexFunctor (ULift.{v} G)).obj A).homology 2))
    (X : TopRep.{v} ℤ G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    IsZero (((continuousModuleComplexFunctor (ULift.{v} G)).obj
      (universeLift X)).homology 2) := by
  let : LocallyCompactSpace (ULift.{v} G) :=
    (Homeomorph.ulift : ULift.{v} G ≃ₜ G).isClosedEmbedding.locallyCompactSpace
  have : Finite (universeLift X) := inferInstanceAs (Finite (ULift.{u} X))
  have : DiscreteTopology (universeLift X) :=
    inferInstanceAs (DiscreteTopology (ULift.{u} X))
  exact continuousModuleH2_isZero_of_prime_coefficients (ULift.{v} G) hprime
    (universeLift X) (universeLift_action_continuous X hX)

end TopRep
