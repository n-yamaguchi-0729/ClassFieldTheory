/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteNonabelianRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteIsomorphism
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization

/-!
# Native absolute Artin coordinates through an explicit embedding

Finite Galois extensions need not be presented as subtypes of the chosen
separable closure. Their actual embedded field ranges give the restriction
map, and conjugation by the original field-range equivalence returns to the
original Galois group. Finite Artin isomorphism naturality proves the native
absolute evaluation formula for this map.
-/

@[expose] public section

universe u v w

noncomputable section

namespace FunctionField

open LocalClassFieldTheory ProCGroups.Abelian
open scoped IsMulCommutative

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

/-- Actual embedded restriction descended to the absolute topological
abelianization, with the original finite Galois abelianization as target. -/
def absoluteAbelianizedRestrictionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    localAbsoluteAbelianProfinite K →* Abelianization Gal(L/K) :=
  ((AlgEquiv.autCongr
    (finiteGaloisFieldRangeEquivOfEmbedding K L i)).abelianizationCongr.symm.toMonoidHom).comp
      (absoluteAbelianizedRestriction K (finiteGaloisFieldRangeOfEmbedding K L i))

/-- The descended map is ordinary embedded restriction on representatives. -/
theorem absoluteAbelianizedRestrictionOfEmbedding_mk
    (i : L →ₐ[K] SeparableClosure K) (σ : Gal(SeparableClosure K/K)) :
    absoluteAbelianizedRestrictionOfEmbedding K L i
        (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K) =
      Abelianization.of (embeddedFiniteRestriction K L i σ) := rfl

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
    { toMonoidHom := embeddedFiniteRestriction K L i
      continuous_toFun := continuous_embeddedFiniteRestriction K L i }

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
    Abelianization.of (absoluteRestrictionOfEmbedding K L i x) =
      absoluteAbelianizedRestrictionOfEmbedding K L i x := by
  refine QuotientGroup.induction_on x ?_
  intro σ
  rfl

end Abelian

section Artin

variable (k : Type u) (K : Type v) (L : Type w)
    [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsGalois K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

/-- Every explicit finite Galois realization gives the original native
Artin symbol as its absolute reciprocity coordinate. -/
theorem absoluteArtin_abelianizedRestrictionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) (c : IdeleClassGroup k K) :
    absoluteAbelianizedRestrictionOfEmbedding K L i (absoluteArtin k K c) =
      finiteArtin k K L c := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let E := finiteGaloisFieldRangeOfEmbedding K L i
  let e := finiteGaloisFieldRangeEquivOfEmbedding K L i
  let eab := (AlgEquiv.autCongr e).abelianizationCongr
  change eab.symm (absoluteAbelianizedRestriction K E (absoluteArtin k K c)) = _
  rw [absoluteArtin_abelianizedRestriction k K E c]
  apply eab.injective
  rw [eab.apply_symm_apply]
  exact (finiteArtin_autCongr k K L E e c).symm

variable [IsAbelianGalois K L]

omit [IsGalois K L] in
/-- In the abelian case the coordinate is the native actual Artin
automorphism, before applying any abelianization equivalence. -/
theorem absoluteArtin_restrictionOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) (c : IdeleClassGroup k K) :
    absoluteRestrictionOfEmbedding K L i (absoluteArtin k K c) =
      abelianFiniteArtin k K L c := by
  apply (Abelianization.equivOfComm (H := Gal(L/K))).injective
  change Abelianization.of (absoluteRestrictionOfEmbedding K L i (absoluteArtin k K c)) =
    Abelianization.of (abelianFiniteArtin k K L c)
  rw [absoluteRestrictionOfEmbedding_of, abelianFiniteArtin_of]
  exact absoluteArtin_abelianizedRestrictionOfEmbedding k K L i c

end Artin

end FunctionField
