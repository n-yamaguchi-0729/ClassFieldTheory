/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Normal.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantFieldExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantGaloisTower

/-!
# Restrictions of automorphisms in a constant compositum tower

For a finite Galois intermediate field `L/K` and finite constants `C`, an
automorphism of `L(C)` over `K` restricts to the actual embedded constants.
Together with restriction to `L`, this determines the automorphism. On
automorphisms fixing `L`, the construction agrees with the existing constant
extension restriction.
-/

noncomputable section

namespace FunctionField

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Finite k] (L : FiniteGaloisIntermediateField K Ω)
    (C : IntermediateField k Ω) [FiniteDimensional k C]

/-- Restriction to the actual constants for automorphisms fixing the lower
field of a finite Galois tower. -/
def constantGaloisTowerRestriction :
    Gal((IntermediateField.adjoin L (C : Set Ω))/K) →* Gal(C/k) :=
  have : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
  have : IsScalarTower k K (IntermediateField.adjoin L (C : Set Ω)) :=
    IsScalarTower.to₁₂₄ k K L (IntermediateField.adjoin L (C : Set Ω))
  let _aC : Algebra C (IntermediateField.adjoin L (C : Set Ω)) :=
    constantAlgebra (K := L) C
  have : IsScalarTower k C (IntermediateField.adjoin L (C : Set Ω)) :=
    constantScalarTower (K := L) C
  have : Finite C := Module.finite_of_finite k
  (AlgEquiv.restrictNormalHom C).comp (AlgEquiv.restrictScalarsHom k)

/-- Restriction acts through the actual inclusion of the constants. -/
theorem constantGaloisTowerRestriction_commutes
    (σ : Gal((IntermediateField.adjoin L (C : Set Ω))/K)) (c : C) :
    let _ : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
    constantEmbedding (K := L) C (constantGaloisTowerRestriction L C σ c) =
      σ (constantEmbedding (K := L) C c) := by
  intro hkLΩ
  have : IsScalarTower k K (IntermediateField.adjoin L (C : Set Ω)) :=
    IsScalarTower.to₁₂₄ k K L (IntermediateField.adjoin L (C : Set Ω))
  let _aC : Algebra C (IntermediateField.adjoin L (C : Set Ω)) :=
    constantAlgebra (K := L) C
  have : IsScalarTower k C (IntermediateField.adjoin L (C : Set Ω)) :=
    constantScalarTower (K := L) C
  have : Finite C := Module.finite_of_finite k
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) C c

/-- Restricting the base field of an automorphism does not change its action
on the constants. -/
theorem constantGaloisTowerRestriction_restrictScalars
    (σ : Gal((IntermediateField.adjoin L (C : Set Ω))/L)) :
    let _ : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
    constantGaloisTowerRestriction L C (σ.restrictScalars K) =
      constantExtensionRestriction (K := L) C σ := by
  intro hkLΩ
  apply AlgEquiv.ext
  intro c
  apply (constantEmbedding (K := L) C).injective
  exact (constantGaloisTowerRestriction_commutes L C (σ.restrictScalars K) c).trans
    (constantExtensionRestriction_commutes (K := L) C σ c).symm

/-- An automorphism of the actual constant compositum is determined by its
restrictions to the upper original field and the constants. -/
theorem constantGaloisTower_restrictions_injective :
    Function.Injective
      ((AlgEquiv.restrictNormalHom L :
        Gal((IntermediateField.adjoin L (C : Set Ω))/K) →* Gal(L/K)).prod
          (constantGaloisTowerRestriction L C)) := by
  have : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro σ hσ
  have hL : AlgEquiv.restrictNormalHom L σ = 1 := congrArg Prod.fst hσ
  have hC : constantGaloisTowerRestriction L C σ = 1 := congrArg Prod.snd hσ
  let η : Gal((IntermediateField.adjoin L (C : Set Ω))/L) :=
    { σ.toRingEquiv with
      commutes' := fun x =>
        (AlgEquiv.restrictNormal_commutes σ L x).symm.trans
          (congrArg (algebraMap L (IntermediateField.adjoin L (C : Set Ω)))
            (congrArg (fun ρ : Gal(L/K) => ρ x) hL)) }
  have hηC : constantExtensionRestriction (K := L) C η = 1 := by
    apply AlgEquiv.ext
    intro c
    apply (constantEmbedding (K := L) C).injective
    calc
      constantEmbedding (K := L) C (constantExtensionRestriction (K := L) C η c) =
          σ (constantEmbedding (K := L) C c) :=
        constantExtensionRestriction_commutes (K := L) C η c
      _ = constantEmbedding (K := L) C (constantGaloisTowerRestriction L C σ c) :=
        (constantGaloisTowerRestriction_commutes L C σ c).symm
      _ = constantEmbedding (K := L) C c :=
        congrArg (constantEmbedding (K := L) C)
          (congrArg (fun ρ : Gal(C/k) => ρ c) hC)
  have hη : η = 1 := constantExtensionRestriction_injective (K := L) C
    (hηC.trans (map_one (constantExtensionRestriction (K := L) C)).symm)
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun ρ : Gal((IntermediateField.adjoin L (C : Set Ω))/L) => ρ x) hη


/-- Adjoining finite constants to an abelian intermediate field preserves
abelianity over the original base field. -/
theorem isAbelianGalois_constantExtension_over_base [IsAbelianGalois K L] :
    IsAbelianGalois K (IntermediateField.adjoin L (C : Set Ω)) := by
  have hC : Finite C := Module.finite_of_finite k
  have hGalois : IsGalois K (IntermediateField.adjoin L (C : Set Ω)) :=
    isGalois_constantExtension_over_base L C
  have hcomm : IsMulCommutative Gal((IntermediateField.adjoin L (C : Set Ω))/K) :=
    .of_comm fun σ τ => (constantGaloisTower_restrictions_injective L C) (by
      rw [map_mul, map_mul, mul_comm'])
  exact { }

end FunctionField
