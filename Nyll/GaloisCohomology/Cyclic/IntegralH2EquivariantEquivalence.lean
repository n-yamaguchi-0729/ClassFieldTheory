/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology
public import Nyll.GaloisCohomology.GroupTheory.H2EquivariantEquivalence

/-! # Equivariant transport of integral degree-two cohomology -/

@[expose] public section

noncomputable section

namespace IntegralGroupCohomology.Universe

universe u v w z

variable {G : Type u} {H : Type v} [Group G] [Group H]
    {A : Rep.{w} ℤ G} {B : Rep.{z} ℤ H}
    (e : G ≃* H) (f : A ≃+ B) (hf : ∀ g a, f (A.ρ g a) = B.ρ (e g) (f a))

/-- Reindex the native cochains by the given equivalence of the original groups. -/
def liftedH2GroupEquiv : ULift.{w} G ≃* ULift.{z} H :=
  MulEquiv.ulift.trans (e.trans MulEquiv.ulift.symm)

/-- Map the original coefficient through the native lifts on the two representations. -/
def liftedH2CoefficientEquiv : (nativeFunctor G).obj A ≃+ (nativeFunctor H).obj B where
  toFun a := ULift.up (f a.down)
  invFun b := ULift.up (f.symm b.down)
  left_inv a := by cases a; exact congrArg ULift.up (f.symm_apply_apply _)
  right_inv b := by cases b; exact congrArg ULift.up (f.apply_symm_apply _)
  map_add' a b := congrArg ULift.up (map_add f a.down b.down)

include hf in
theorem liftedH2CoefficientEquiv_ρ (g : ULift.{w} G) (a : (nativeFunctor G).obj A) :
    liftedH2CoefficientEquiv f (((nativeFunctor G).obj A).ρ g a) =
      ((nativeFunctor H).obj B).ρ (liftedH2GroupEquiv e g) (liftedH2CoefficientEquiv f a) := by
  exact congrArg ULift.up (hf g.down a.down)

/-- Compatible field or group transports identify the original integral H²,
with independent universes for both groups and both coefficient carriers. -/
def equivariantH2AddEquiv : cohomology A 2 ≃+ cohomology B 2 :=
  groupCohomology.equivariantH2AddEquiv (liftedH2GroupEquiv e) (liftedH2CoefficientEquiv f)
    (liftedH2CoefficientEquiv_ρ e f hf)

/-- On a cocycle the integral equivalence applies the original group and coefficient maps. -/
theorem equivariantH2AddEquiv_H2π (c : groupCohomology.cocycles₂ ((nativeFunctor G).obj A)) :
    equivariantH2AddEquiv e f hf (groupCohomology.H2π ((nativeFunctor G).obj A) c) =
      groupCohomology.H2π ((nativeFunctor H).obj B)
        (groupCohomology.reindexTwoCocycle (liftedH2GroupEquiv e) (liftedH2CoefficientEquiv f)
          (liftedH2CoefficientEquiv_ρ e f hf) c) :=
  groupCohomology.equivariantH2AddEquiv_H2π _ _ _ c

end IntegralGroupCohomology.Universe
