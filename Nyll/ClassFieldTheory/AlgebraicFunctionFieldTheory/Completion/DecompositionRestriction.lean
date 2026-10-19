/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.Places.Restriction.AlgEquivSmulEqRestrictEq
import Nyll.AlgebraicCurves.Places.Restriction.RestrictionComposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition

/-!
# Lifting decomposition automorphisms in finite Galois towers

A decomposition automorphism lifts through every finite Galois tower at
any specified place above the original place. A global automorphism lift
is corrected by an automorphism over the intermediate field, using actual
transitivity on the fiber of places. Thus restriction onto the lower
decomposition group is surjective.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L M : Type*} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower k K L] [IsScalarTower k K M]
    [IsScalarTower k L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]

omit [FiniteDimensional K L] [IsGalois K M] in
/-- Restricting the upper place commutes with the induced lower automorphism. -/
theorem restrict_place_algAut_smul (ρ : Gal(M/K)) (W : Place k M) :
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    (SemilinearAut.ofAlgAut (ρ.restrictScalars k) • W).restrict L =
      SemilinearAut.ofAlgAut ((AlgEquiv.restrictNormalHom L ρ).restrictScalars k) •
        W.restrict L := by
  intro hLMfinite
  let i : L →ₐ[k] M := IsScalarTower.toAlgHom k L M
  have hi : i.toRingHom.IsIntegral := Algebra.IsIntegral.isIntegral
  exact Place.smul_restrictAlong i i hi hi (ρ.restrictScalars k)
    ((AlgEquiv.restrictNormalHom L ρ).restrictScalars k)
    (fun x => AlgEquiv.restrictNormal_commutes ρ L x) W

omit [FiniteDimensional K L] in
/-- Every decomposition automorphism lifts while fixing any chosen upper place
in a finite Galois tower. -/
theorem exists_decompositionGroup_lift (W : Place k M) :
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    ∀ σ : decompositionGroup (K := K) (W.restrict L),
      ∃ τ : decompositionGroup (K := K) W,
        AlgEquiv.restrictNormalHom L τ.1 = σ.1 := by
  intro hLMfinite σ
  have : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  obtain ⟨ρ, hρ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := M) σ.1
  let g : SemilinearAut k M := SemilinearAut.ofAlgAut (ρ.restrictScalars k)
  have hplace : (g • W).restrict L = W.restrict L := by
    rw [restrict_place_algAut_smul (K := K) ρ W, hρ]
    exact decompositionGroup_smul_eq (W.restrict L) σ
  obtain ⟨η, hη⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq
    (F' := L) (g • W) W hplace.symm
  let τ : Gal(M/K) := η.restrictScalars K * ρ
  have hτ : τ ∈ decompositionGroup (K := K) W := by
    change (SemilinearAut.ofAlgAut (η.restrictScalars k) * g) • W = W
    rw [mul_smul]
    exact hη
  refine ⟨⟨τ, hτ⟩, ?_⟩
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L M).injective
  calc
    algebraMap L M ((AlgEquiv.restrictNormalHom L τ) x) =
        τ (algebraMap L M x) := AlgEquiv.restrictNormal_commutes τ L x
    _ = ρ (algebraMap L M x) := by
      change η (ρ (algebraMap L M x)) = ρ (algebraMap L M x)
      rw [← AlgEquiv.restrictNormal_commutes ρ L x, η.commutes]
    _ = algebraMap L M ((AlgEquiv.restrictNormalHom L ρ) x) :=
      (AlgEquiv.restrictNormal_commutes ρ L x).symm
    _ = algebraMap L M (σ.1 x) :=
      congrArg (fun σ' : Gal(L/K) => algebraMap L M (σ' x)) hρ

end FunctionField.IdeleGroup
