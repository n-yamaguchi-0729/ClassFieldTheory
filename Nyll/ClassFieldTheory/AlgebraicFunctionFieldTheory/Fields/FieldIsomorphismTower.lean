/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.FieldIsomorphismRayNaturality
public import Nyll.GaloisCohomology.Topology.FieldIsomorphismClosure

/-!
# Native Galois conjugation through one specified ambient field map

Native coordinates of an upper field are transported through the given
ambient closures. Conjugating there and then restricting to the original
base field is the same literal ambient conjugation as first restricting.
No compatibility of independently chosen native extensions is assumed.
-/

@[expose] public section

noncomputable section

namespace FunctionField

open GaloisCohomology

universe u₁ u₂ v₁ v₂

variable {K₁ : Type u₁} {K₂ : Type u₂} {L₁ : Type v₁} {L₂ : Type v₂}
  [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra K₁ L₁] [Algebra K₂ L₂]
  [Algebra L₁ (SeparableClosure K₁)] [Algebra L₂ (SeparableClosure K₂)]
  [IsScalarTower K₁ L₁ (SeparableClosure K₁)]
  [IsScalarTower K₂ L₂ (SeparableClosure K₂)]
  (Φ : K₁ ≃+* K₂)
  (a : SeparableClosure K₁ ≃+* SeparableClosure K₂)
  (ha : ∀ x, a (algebraMap K₁ (SeparableClosure K₁) x) =
    algebraMap K₂ (SeparableClosure K₂) (Φ x))
  (ΦL : L₁ ≃+* L₂)
  (e₁ : SeparableClosure L₁ ≃ₐ[L₁] SeparableClosure K₁)
  (e₂ : SeparableClosure L₂ ≃ₐ[L₂] SeparableClosure K₂)
  (hL : ∀ x, a (algebraMap L₁ (SeparableClosure K₁) x) =
    algebraMap L₂ (SeparableClosure K₂) (ΦL x))

local notation "aL" => nativeClosureEquivOfSupplied a e₁ e₂
local notation "haL" => nativeClosureEquivOfSupplied_algebraMap ΦL a e₁ e₂ hL

/-- The actual native conjugation at the upper field commutes with
restriction to the original field, because both use the single given
ambient closure map. -/
theorem nativeFieldIsoGaloisEquiv_restrict_via_supplied
    (σ : Gal(SeparableClosure L₁/L₁)) :
    (AlgEquiv.autCongr e₂ (nativeFieldIsoGaloisEquiv ΦL aL haL σ)).restrictScalars K₂ =
      nativeFieldIsoGaloisEquiv Φ a ha ((AlgEquiv.autCongr e₁ σ).restrictScalars K₁) := by
  apply AlgEquiv.ext
  intro x
  change e₂ (nativeFieldIsoGaloisEquiv ΦL aL haL σ (e₂.symm x)) =
    nativeFieldIsoGaloisEquiv Φ a ha ((AlgEquiv.autCongr e₁ σ).restrictScalars K₁) x
  rw [nativeFieldIsoGaloisEquiv_apply, nativeFieldIsoGaloisEquiv_apply]
  change e₂ (e₂.symm (a (e₁ (σ (e₁.symm (a.symm (e₂ (e₂.symm x)))))))) =
    a (e₁ (σ (e₁.symm (a.symm x))))
  rw [e₂.apply_symm_apply, e₂.apply_symm_apply]

end FunctionField
