/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteNonabelianRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteIsomorphism
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.EmbeddedAbsoluteRestriction
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
  apply (Group.Abelianization.equivOfComm (H := Gal(L/K))).injective
  change Group.Abelianization.of (absoluteRestrictionOfEmbedding K L i (absoluteArtin k K c)) =
    Group.Abelianization.of (abelianFiniteArtin k K L c)
  rw [absoluteRestrictionOfEmbedding_of, abelianFiniteArtin_of]
  exact absoluteArtin_abelianizedRestrictionOfEmbedding k K L i c

end Artin

end FunctionField
