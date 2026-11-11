/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalNormNaturality
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Abelian
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.UnitsH2Over
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue

/-!
# Restricting local Artin automorphisms in a function-field tower

The existing restriction law for local reciprocity is applied to the actual
tower of completed fields. Evaluation on the embedded original field then
identifies the restrictions of the actual decomposition automorphisms.
-/

@[expose] public section

universe u v w s

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

section CompletionTransport

variable {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

private theorem completionIsAbelianGalois_over
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
    let _ : Algebra v.adicCompletion w.adicCompletion :=
      (IdeleGroup.completionMapOver v w hw).toAlgebra
    IsAbelianGalois v.adicCompletion w.adicCompletion := by
  have h : IsAbelianGalois (w.restrict K).adicCompletion w.adicCompletion :=
    inferInstance
  subst v
  exact h

variable [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

private theorem localArtin_completion_apply_over
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v)
    (x : v.adicCompletionˣ) (y : L) :
    let _ : Algebra v.adicCompletion w.adicCompletion :=
      (IdeleGroup.completionMapOver v w hw).toAlgebra
    let _ : FiniteDimensional v.adicCompletion w.adicCompletion :=
      (IdeleGroup.completionFiniteGaloisOver v w hw).1
    let _ : IsAbelianGalois v.adicCompletion w.adicCompletion :=
      completionIsAbelianGalois_over v w hw
    let _ : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
    let _ : IsNonarchimedeanLocalField v.adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField v
    LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom
        v.adicCompletion w.adicCompletion x⁻¹
        (algebraMap L w.adicCompletion y) =
      algebraMap L w.adicCompletion (localArtin (K := K) w (hw.symm ▸ x) y) := by
  subst v
  exact localArtin_completion_apply_universe w x y

end CompletionTransport

/-- Comparing the actions through compatible embeddings identifies the
restriction of the original automorphism with the lower automorphism. -/
theorem restrictNormalHom_eq_of_pointwise_actions
    {K L M E T : Type*} [Field K] [Field L] [Field M] [Field E] [Field T]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Normal K L]
    [Algebra E T]
    (σ : Gal(M/K)) (τ : Gal(L/K)) (ρ : T → T) (θ : E → E)
    (iL : L →+* E) (iM : M →+* T)
    (hmap : ∀ y : L, algebraMap E T (iL y) = iM (algebraMap L M y))
    (hres : ∀ y : E, ρ (algebraMap E T y) = algebraMap E T (θ y))
    (hupper : ∀ y : L, ρ (iM (algebraMap L M y)) = iM (σ (algebraMap L M y)))
    (hlower : ∀ y : L, θ (iL y) = iL (τ y)) :
    AlgEquiv.restrictNormalHom L σ = τ := by
  apply AlgEquiv.ext
  intro y
  apply iL.injective
  apply (algebraMap E T).injective
  calc
    _ = iM (algebraMap L M (σ.restrictNormal L y)) := hmap _
    _ = iM (σ (algebraMap L M y)) := congrArg iM (σ.restrictNormal_commutes L y)
    _ = ρ (iM (algebraMap L M y)) := (hupper y).symm
    _ = ρ (algebraMap E T (iL y)) := congrArg ρ (hmap y).symm
    _ = algebraMap E T (θ (iL y)) := hres (iL y)
    _ = _ := congrArg (algebraMap E T) (hlower y)

/-- Restriction of the completed automorphism gives the pointwise action
comparison along the completed field embedding. -/
theorem restrictNormalHom_eq_of_embedded_actions
    {K L M F E T : Type*} [Field K] [Field L] [Field M] [Field F] [Field E] [Field T]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Normal K L]
    [Algebra F E] [Algebra F T] [Algebra E T] [IsScalarTower F E T] [Normal F E]
    (σ : Gal(M/K)) (τ : Gal(L/K)) (ρ : Gal(T/F)) (θ : Gal(E/F))
    (iL : L →+* E) (iM : M →+* T)
    (hmap : ∀ y : L, algebraMap E T (iL y) = iM (algebraMap L M y))
    (hres : ρ.restrictNormal E = θ)
    (hupper : ∀ y : L, ρ (iM (algebraMap L M y)) = iM (σ (algebraMap L M y)))
    (hlower : ∀ y : L, θ (iL y) = iL (τ y)) :
    AlgEquiv.restrictNormalHom L σ = τ :=
  restrictNormalHom_eq_of_pointwise_actions σ τ ρ θ iL iM hmap
    (fun y => (ρ.restrictNormal_commutes E y).symm.trans
      (congrArg (fun χ : Gal(E/F) => algebraMap E T (χ y)) hres)) hupper hlower

private theorem completionArtin_restrict_tower_at
    (F E T : Type*) [Field F] [Field E] [Field T]
    [Algebra F E] [Algebra F T] [Algebra E T] [IsScalarTower F E T]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [FiniteDimensional F E] [FiniteDimensional F T]
    [IsAbelianGalois F E] [IsAbelianGalois F T] (x : Fˣ) :
    (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom F T x).restrictNormal E =
      LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom F E x :=
  DFunLike.congr_fun
    (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_restrict_tower F E T) x

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

variable {k : Type u} {K : Type v} {L : Type w} {M : Type s}
    [Field k] [Finite k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower k L M]
    [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- Restriction of the local Artin automorphism to a finite abelian
subextension is its own local Artin automorphism at the restricted place. -/
theorem localArtin_restrictNormal (u : Place k M)
    (x : (u.restrict K).adicCompletionˣ) :
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    AlgEquiv.restrictNormalHom L (localArtin (K := K) u x) =
      localArtin (K := K) (u.restrict L)
        ((restrict_restrict (F := K) (E := L) u).symm ▸ x) := by
  intro hLMfinite
  let v : Place k K := u.restrict K
  let w : Place k L := u.restrict L
  have hw : w.restrict K = v := restrict_restrict (F := K) (E := L) u
  have hLMgalois : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let avw : Algebra v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionMapOver v w hw).toAlgebra
  have hvwfinite : FiniteDimensional v.adicCompletion w.adicCompletion :=
    (IdeleGroup.completionFiniteGaloisOver v w hw).1
  have hvwabelian : IsAbelianGalois v.adicCompletion w.adicCompletion :=
    completionIsAbelianGalois_over v w hw
  let rv : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have hvlocal : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  have hvwu : IsScalarTower v.adicCompletion w.adicCompletion u.adicCompletion :=
    IsScalarTower.of_algebraMap_eq (fun y =>
      (congrArg (fun f : v.adicCompletion →+* u.adicCompletion => f y)
        (IdeleGroup.completionMapOver_trans v w u hw rfl rfl)).symm)
  let ρ : Gal(u.adicCompletion/v.adicCompletion) :=
    LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom v.adicCompletion u.adicCompletion x⁻¹
  let θ : Gal(w.adicCompletion/v.adicCompletion) :=
    LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom v.adicCompletion w.adicCompletion x⁻¹
  let σ : Gal(M/K) := localArtin (K := K) u x
  let τ : Gal(L/K) := localArtin (K := K) w (hw.symm ▸ x)
  let iL : L →+* w.adicCompletion := algebraMap L w.adicCompletion
  let iM : M →+* u.adicCompletion := algebraMap M u.adicCompletion
  have hres : ρ.restrictNormal w.adicCompletion = θ := completionArtin_restrict_tower_at
    v.adicCompletion w.adicCompletion u.adicCompletion x⁻¹
  have hmap (y : L) :
      algebraMap w.adicCompletion u.adicCompletion (iL y) = iM (algebraMap L M y) :=
    IdeleGroup.completionMapOver_algebraMap w u rfl y
  have hupper (y : L) :
      ρ (iM (algebraMap L M y)) = iM (σ (algebraMap L M y)) :=
    localArtin_completion_apply_universe (K := K) u x (algebraMap L M y)
  have hlower (y : L) : θ (iL y) = iL (τ y) :=
    localArtin_completion_apply_over v w hw x y
  have hrestrict := restrictNormalHom_eq_of_embedded_actions
    (K := K) (L := L) (M := M)
    (F := v.adicCompletion) (E := w.adicCompletion) (T := u.adicCompletion)
    σ τ ρ θ iL iM hmap hres hupper hlower
  exact hrestrict

end FunctionField
