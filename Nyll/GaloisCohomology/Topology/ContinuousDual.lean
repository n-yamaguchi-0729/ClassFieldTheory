/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.DiscreteCoefficientQuotient
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The discrete contragredient and its evaluation

These are the original linear maps with the conjugation action.
Finiteness of the source makes the action jointly continuous.
-/

@[expose] public section

open CategoryTheory ContRepresentation
open scoped Topology

noncomputable section

namespace TopRep

universe u r

variable {R : Type r} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {G : Type u} [Group G] (A M : TopRep.{u} R G)

/-- Discrete linear maps with the conjugation action from the original
source and target. -/
def discreteLinearDual : TopRep.{u} R G :=
  discreteCoefficientTopRep R G
    (Rep.of (Representation.linHom A.ρ.toRepresentation M.ρ.toRepresentation))

instance discreteLinearDual_discrete : DiscreteTopology (discreteLinearDual A M) :=
  discreteCoefficientTopRep_discrete _ _ _

/-- The dual coefficient group is literally the original linear-map group. -/
def discreteLinearDualMap (f : discreteLinearDual A M) : A →ₗ[R] M := f

theorem discreteLinearDual_finite [Finite A] [Finite M] : Finite (discreteLinearDual A M) :=
  Finite.of_injective (fun f : discreteLinearDual A M => (discreteLinearDualMap A M f : A → M))
    (fun _ _ h => LinearMap.ext fun a => congrFun h a)

theorem discreteLinearDual_action (g : G) (f : discreteLinearDual A M) (a : A) :
    discreteLinearDualMap A M ((discreteLinearDual A M).ρ g f) a =
      M.ρ g (discreteLinearDualMap A M f (A.ρ g⁻¹ a)) := rfl

/-- The contragredient pullback is precomposition on the original maps. -/
def discreteLinearDualPullback {A B : TopRep.{u} R G} (f : A ⟶ B) :
    discreteLinearDual B M ⟶ discreteLinearDual A M := by
  let f₀ := f.hom.toContinuousLinearMap.toLinearMap
  let pullback : (B →ₗ[R] M) →ₗ[R] (A →ₗ[R] M) :=
    { toFun := fun l => l.comp f₀
      map_add' := fun _ _ => LinearMap.ext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => rfl }
  let φ : (discreteLinearDual B M).ρ →ⁱL (discreteLinearDual A M).ρ :=
    { toContinuousLinearMap := ⟨pullback, continuous_of_discreteTopology⟩
      isIntertwining' := fun g => by
        apply ContinuousLinearMap.ext
        intro l
        apply LinearMap.ext
        intro a
        let l₀ : B →ₗ[R] M := discreteLinearDualMap B M l
        change M.ρ g (l₀ (B.ρ g⁻¹ (f a))) = M.ρ g (l₀ (f (A.ρ g⁻¹ a)))
        exact congrArg (fun b : B => M.ρ g (l₀ b))
          (f.hom.isIntertwining g⁻¹ a).symm }
  exact ConcreteCategory.ofHom (C := TopRep R G) φ

/-- Precomposition agrees pointwise with evaluation. -/
@[simp]
theorem discreteLinearDualPullback_apply {A B : TopRep.{u} R G} (f : A ⟶ B)
    (l : discreteLinearDual B M) (a : A) :
    discreteLinearDualMap A M (discreteLinearDualPullback M f l) a =
      discreteLinearDualMap B M l (f a) := rfl

/-- The actual evaluation, with the argument order used by cup products. -/
def discreteLinearDualEvaluation : A →ₗ[R] discreteLinearDual A M →ₗ[R] M :=
  (LinearMap.id : (A →ₗ[R] M) →ₗ[R] (A →ₗ[R] M)).flip

theorem discreteLinearDualEvaluation_apply (a : A) (f : discreteLinearDual A M) :
    discreteLinearDualEvaluation A M a f = discreteLinearDualMap A M f a := rfl

theorem discreteLinearDualEvaluation_equivariant (g : G) (a : A) (f : discreteLinearDual A M) :
    discreteLinearDualEvaluation A M (A.ρ g a) ((discreteLinearDual A M).ρ g f) =
      M.ρ g (discreteLinearDualEvaluation A M a f) := by
  change discreteLinearDualMap A M ((discreteLinearDual A M).ρ g f) (A.ρ g a) =
    M.ρ g (discreteLinearDualMap A M f a)
  have h : A.ρ g⁻¹ (A.ρ g a) = a := by
    have hg := congrArg (fun p : A →L[R] A => p a) (map_mul A.ρ g⁻¹ g).symm
    rw [inv_mul_cancel, map_one] at hg
    exact hg
  rw [discreteLinearDual_action, h]

theorem discreteLinearDualEvaluation_continuous [DiscreteTopology A] :
    Continuous (fun x : A × discreteLinearDual A M => discreteLinearDualEvaluation A M x.1 x.2) :=
  continuous_of_discreteTopology

/-- The natural map to the double contragredient is evaluation on the
original coefficient and intertwines the Galois actions. -/
def discreteLinearDualBidualMap [DiscreteTopology A] :
    A ⟶ discreteLinearDual (discreteLinearDual A M) M := by
  let D := discreteLinearDual A M
  exact ConcreteCategory.ofHom (C := TopRep R G)
    { toContinuousLinearMap := ⟨discreteLinearDualEvaluation A M, continuous_of_discreteTopology⟩
      isIntertwining' := fun g => by
        apply ContinuousLinearMap.ext
        intro a
        apply LinearMap.ext
        intro l
        change discreteLinearDualEvaluation A M (A.ρ g a) l =
          M.ρ g (discreteLinearDualEvaluation A M a (D.ρ g⁻¹ l))
        have hl : D.ρ g (D.ρ g⁻¹ l) = l := by
          have h := congrArg (fun p : D →L[R] D => p l) (map_mul D.ρ g g⁻¹).symm
          rw [mul_inv_cancel, map_one] at h
          exact h
        have he := discreteLinearDualEvaluation_equivariant A M g a (D.ρ g⁻¹ l)
        change discreteLinearDualEvaluation A M (A.ρ g a) (D.ρ g (D.ρ g⁻¹ l)) =
          M.ρ g (discreteLinearDualEvaluation A M a (D.ρ g⁻¹ l)) at he
        exact (congrArg (fun t : D => discreteLinearDualEvaluation A M (A.ρ g a) t)
          hl).symm.trans he }

@[simp]
theorem discreteLinearDualBidualMap_apply [DiscreteTopology A]
    (a : A) (l : discreteLinearDual A M) :
    discreteLinearDualMap (discreteLinearDual A M) M (discreteLinearDualBidualMap A M a) l =
      discreteLinearDualMap A M l a := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The simultaneous action on the discrete dual is jointly continuous
whenever the original finite source and discrete target actions are. -/
theorem discreteLinearDual_action_continuous [Finite A] [DiscreteTopology A] [DiscreteTopology M]
    (hA : Continuous (fun x : G × A => A.ρ x.1 x.2))
    (hM : Continuous (fun x : G × M => M.ρ x.1 x.2)) :
    Continuous (fun x : G × discreteLinearDual A M => (discreteLinearDual A M).ρ x.1 x.2) := by
  apply continuous_prod_of_discrete_right.mpr
  intro f
  let f₀ := discreteLinearDualMap A M f
  have hpoint (a : A) : Continuous (fun g : G =>
      discreteLinearDualMap A M ((discreteLinearDual A M).ρ g f) a) := by
    change Continuous (fun g : G => M.ρ g (f₀ (A.ρ g⁻¹ a)))
    have hs : Continuous (fun g : G => A.ρ g⁻¹ a) :=
      hA.comp (continuous_inv.prodMk continuous_const)
    exact hM.comp (continuous_id.prodMk
      ((continuous_of_discreteTopology : Continuous (fun x : A => f₀ x)).comp hs))
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  let V (a : A) := {h : G |
    discreteLinearDualMap A M ((discreteLinearDual A M).ρ h f) a =
      discreteLinearDualMap A M ((discreteLinearDual A M).ρ g f) a}
  refine ⟨⋂ a : A, V a, isOpen_iInter_of_finite (fun a => ?_),
    Set.mem_iInter.mpr (fun _ => rfl), ?_⟩
  · let y := discreteLinearDualMap A M ((discreteLinearDual A M).ρ g f) a
    let s : Set M := {y}
    change IsOpen ((fun h : G =>
      discreteLinearDualMap A M ((discreteLinearDual A M).ρ h f) a) ⁻¹' s)
    exact (hpoint a).isOpen_preimage s (isOpen_discrete s)
  · intro h hh
    apply LinearMap.ext
    intro a
    exact Set.mem_iInter.mp hh a

end TopRep
