/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.AbsoluteFiniteQuotients
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.NormalFieldRange
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Finite restrictions through explicit separable-closure embeddings

These are the original restriction maps and their topological abelianizations.
They depend only on the fields and the supplied embedding.
-/

@[expose] public section

noncomputable section

universe v w

namespace FunctionField

open LocalClassFieldTheory ProCGroups.Abelian
open scoped IsMulCommutative

section FiniteAbelianization

variable (K : Type v) [Field K]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E]

/-- Finite Galois restriction followed by abelianization has an open and closed kernel. -/
theorem restrictionAbelianization_ker_closed_open :
    let q : Gal(SeparableClosure K/K) →* Group.Abelianization Gal(E/K) :=
      Group.Abelianization.of.comp (AlgEquiv.restrictNormalHom E)
    IsClosed (q.ker : Set Gal(SeparableClosure K/K)) ∧
      IsOpen (q.ker : Set Gal(SeparableClosure K/K)) := by
  intro q
  let r : Gal(SeparableClosure K/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hker : (q.ker : Set Gal(SeparableClosure K/K)) =
      r ⁻¹' (commutator Gal(E/K) : Set Gal(E/K)) := by
    ext σ
    change Group.Abelianization.of (r σ) = 1 ↔ r σ ∈ commutator Gal(E/K)
    exact QuotientGroup.eq_one_iff (N := commutator Gal(E/K)) (r σ)
  rw [hker]
  exact ⟨(isClosed_discrete _).preimage (InfiniteGalois.restrictNormalHom_continuous E),
    (isOpen_discrete _).preimage (InfiniteGalois.restrictNormalHom_continuous E)⟩

/-- Actual finite Galois restriction, descended after abelianization. -/
def absoluteAbelianizedRestriction :
    localAbsoluteAbelianProfinite K →* Group.Abelianization Gal(E/K) := by
  let q : Gal(SeparableClosure K/K) →* Group.Abelianization Gal(E/K) :=
    Group.Abelianization.of.comp (AlgEquiv.restrictNormalHom E)
  have hcomm : commutator Gal(SeparableClosure K/K) ≤ q.ker :=
    Group.Abelianization.commutator_le_ker q
  have hclosed : IsClosed (q.ker : Set Gal(SeparableClosure K/K)) :=
    (restrictionAbelianization_ker_closed_open K E).1
  have hclosure : (commutator Gal(SeparableClosure K/K)).topologicalClosure ≤ q.ker :=
    (commutator Gal(SeparableClosure K/K)).topologicalClosure_minimal hcomm hclosed
  exact QuotientGroup.lift (commutator Gal(SeparableClosure K/K)).topologicalClosure q
    (fun σ hσ => MonoidHom.mem_ker.mp (hclosure hσ))

/-- On an absolute automorphism, the map is literal finite restriction
followed by the ordinary abelianization quotient. -/
theorem absoluteAbelianizedRestriction_mk (σ : Gal(SeparableClosure K/K)) :
    absoluteAbelianizedRestriction K E
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) =
      Group.Abelianization.of (AlgEquiv.restrictNormalHom E σ) := rfl

end FiniteAbelianization

section Restriction

variable (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Actual finite restriction through the given separable-closure embedding. -/
def embeddedFiniteRestriction (i : L →ₐ[K] SeparableClosure K) :
    Gal(SeparableClosure K/K) →* Gal(L/K) :=
  (AlgEquiv.autCongr (finiteGaloisFieldRangeEquivOfEmbedding K L i)).symm.toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (finiteGaloisFieldRangeOfEmbedding K L i))

omit [FiniteDimensional K L] in
/-- The restricted automorphism has exactly the original action on the
embedded elements of the finite field. -/
theorem embeddedFiniteRestriction_commutes
    (i : L →ₐ[K] SeparableClosure K) (σ : Gal(SeparableClosure K/K)) (x : L) :
    i (embeddedFiniteRestriction K L i σ x) = σ (i x) := by
  let e := finiteGaloisFieldRangeEquivOfEmbedding K L i
  change ((e (e.symm ((AlgEquiv.restrictNormalHom
      (finiteGaloisFieldRangeOfEmbedding K L i) σ) (e x)))) : SeparableClosure K) = _
  rw [e.apply_symm_apply]
  exact AlgEquiv.restrictNormal_commutes σ
    (finiteGaloisFieldRangeOfEmbedding K L i) (e x)

/-- Embedded finite restriction is continuous for the original Krull topologies. -/
theorem continuous_embeddedFiniteRestriction
    (i : L →ₐ[K] SeparableClosure K) : Continuous (embeddedFiniteRestriction K L i) :=
  (continuous_of_discreteTopology : Continuous
    (AlgEquiv.autCongr (finiteGaloisFieldRangeEquivOfEmbedding K L i)).symm).comp
      (InfiniteGalois.restrictNormalHom_continuous
        (finiteGaloisFieldRangeOfEmbedding K L i))

omit [FiniteDimensional K L] in
/-- The actual finite restriction is onto for any of the supplied embeddings. -/
theorem embeddedFiniteRestriction_surjective
    (i : L →ₐ[K] SeparableClosure K) : Function.Surjective (embeddedFiniteRestriction K L i) :=
  (AlgEquiv.autCongr (finiteGaloisFieldRangeEquivOfEmbedding K L i)).symm.surjective.comp
    (AlgEquiv.restrictNormalHom_surjective (F := K)
      (K₁ := finiteGaloisFieldRangeOfEmbedding K L i) (E := SeparableClosure K))

/-- The continuous form of the same embedded finite restriction. -/
def embeddedFiniteRestrictionContinuous (i : L →ₐ[K] SeparableClosure K) :
    Gal(SeparableClosure K/K) →ₜ* Gal(L/K) :=
  ⟨embeddedFiniteRestriction K L i, continuous_embeddedFiniteRestriction K L i⟩

/-- Actual embedded restriction descended to the absolute topological
abelianization, with the original finite Galois abelianization as target. -/
def absoluteAbelianizedRestrictionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    localAbsoluteAbelianProfinite K →* Group.Abelianization Gal(L/K) :=
  ((AlgEquiv.autCongr
    (finiteGaloisFieldRangeEquivOfEmbedding K L i)).abelianizationCongr.symm.toMonoidHom).comp
      (absoluteAbelianizedRestriction K (finiteGaloisFieldRangeOfEmbedding K L i))

/-- The descended map is ordinary embedded restriction on representatives. -/
theorem absoluteAbelianizedRestrictionOfEmbedding_mk
    (i : L →ₐ[K] SeparableClosure K) (σ : Gal(SeparableClosure K/K)) :
    absoluteAbelianizedRestrictionOfEmbedding K L i
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) =
      Group.Abelianization.of (embeddedFiniteRestriction K L i σ) := rfl

end Restriction

section Abelian

variable (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- For an abelian finite extension, actual embedded restriction descends
continuously with values in the original automorphism group. -/
def absoluteRestrictionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    localAbsoluteAbelianProfinite K →ₜ* Gal(L/K) :=
  TopologicalAbelianization.lift
    (embeddedFiniteRestrictionContinuous K L i)

/-- The continuous abelian map retains the literal embedded action. -/
theorem absoluteRestrictionOfEmbedding_mk
    (i : L →ₐ[K] SeparableClosure K) (σ : Gal(SeparableClosure K/K)) :
    absoluteRestrictionOfEmbedding K L i
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) =
      embeddedFiniteRestriction K L i σ := rfl

/-- Abelianizing the finite automorphism agrees with the general finite
Galois abelianization coordinate. -/
theorem absoluteRestrictionOfEmbedding_of
    (i : L →ₐ[K] SeparableClosure K) (x : localAbsoluteAbelianProfinite K) :
    Group.Abelianization.of (absoluteRestrictionOfEmbedding K L i x) =
      absoluteAbelianizedRestrictionOfEmbedding K L i x := by
  refine QuotientGroup.induction_on x ?_
  intro σ
  rfl

end Abelian

end FunctionField
