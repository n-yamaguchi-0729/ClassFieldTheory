/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Discrete quotients by invariant coefficient submodules

These constructions use the ordinary representation quotient and its
discrete topology. Continuity of the action descends along the actual
surjective coefficient projection.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory ContRepresentation

namespace TopRep

variable (R : Type v) [Ring R] [TopologicalSpace R] [DiscreteTopology R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Equip an ordinary representation over a discrete ring with its discrete topology. -/
def discreteCoefficientTopRep (A : Rep.{u} R G) : TopRep.{u} R G := by
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  let ρ : ContRepresentation R G A :=
    { toMonoidHom :=
      { toFun := fun g =>
          { toLinearMap := A.ρ g
            cont := continuous_of_discreteTopology }
        map_one' := by
          apply ContinuousLinearMap.ext
          intro x
          exact congrArg (fun f : Module.End R A => f x) (map_one A.ρ)
        map_mul' := by
          intro g h
          apply ContinuousLinearMap.ext
          intro x
          exact congrArg (fun f : Module.End R A => f x) (map_mul A.ρ g h) } }
  have : ContinuousSMul R A := ⟨continuous_of_discreteTopology⟩
  exact TopRep.of ρ

/-- The discrete topology in the coefficient construction is actual, not assumed. -/
instance discreteCoefficientTopRep_discrete (A : Rep.{u} R G) :
    DiscreteTopology (discreteCoefficientTopRep R G A) := ⟨rfl⟩

variable (X : TopRep.{u} R G) (W : Submodule R X)
  (hW : ∀ g : G, W ≤ W.comap (X.ρ g).toLinearMap)

/-- The ordinary representation on the actual invariant-submodule quotient. -/
def invariantCoefficientQuotientRep : Rep.{u} R G :=
  (Rep.of X.ρ.toRepresentation).quotient W hW

/-- The actual invariant-submodule quotient with discrete topology. -/
def invariantCoefficientQuotient : TopRep.{u} R G :=
  discreteCoefficientTopRep R G (invariantCoefficientQuotientRep R G X W hW)

/-- The actual coefficient quotient has discrete topology. -/
instance invariantCoefficientQuotient_discrete :
    DiscreteTopology (invariantCoefficientQuotient R G X W hW) :=
  discreteCoefficientTopRep_discrete R G _

/-- The actual quotient projection of discrete coefficients is continuous and equivariant. -/
def invariantCoefficientQuotientProjection [DiscreteTopology X] :
    X ⟶ invariantCoefficientQuotient R G X W hW := by
  let Q := invariantCoefficientQuotient R G X W hW
  let : TopologicalSpace (invariantCoefficientQuotientRep R G X W hW) := Q.hV3
  have : DiscreteTopology (invariantCoefficientQuotientRep R G X W hW) := ⟨rfl⟩
  have : ContinuousSMul R (invariantCoefficientQuotientRep R G X W hW) := Q.hV5
  have : IsTopologicalAddGroup (invariantCoefficientQuotientRep R G X W hW) := Q.hV4
  let q : X.ρ →ⁱL Q.ρ :=
    { toLinearMap := W.mkQ
      cont := continuous_of_discreteTopology
      isIntertwining' := fun g => by
        apply ContinuousLinearMap.ext
        intro x
        rfl }
  exact ConcreteCategory.ofHom (C := TopRep R G) q

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Every actual coefficient quotient class has a representative. -/
theorem invariantCoefficientQuotientProjection_surjective [DiscreteTopology X] :
    Function.Surjective (invariantCoefficientQuotientProjection R G X W hW) :=
  W.mkQ_surjective

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The kernel of the actual coefficient quotient is the given submodule. -/
theorem invariantCoefficientQuotientProjection_eq_zero_iff
    [DiscreteTopology X] (x : X) :
    invariantCoefficientQuotientProjection R G X W hW x = 0 ↔ x ∈ W :=
  Submodule.Quotient.mk_eq_zero W

omit [IsTopologicalGroup G] in
/-- Joint continuity descends to the actual discrete coefficient quotient. -/
theorem invariantCoefficientQuotient_action_continuous
    [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    Continuous (fun gq : G × invariantCoefficientQuotient R G X W hW =>
      (invariantCoefficientQuotient R G X W hW).ρ gq.1 gq.2) := by
  apply continuous_prod_of_discrete_right.mpr
  intro q
  obtain ⟨x, rfl⟩ := invariantCoefficientQuotientProjection_surjective R G X W hW q
  have hx : Continuous (fun g : G => X.ρ g x) :=
    hX.comp (continuous_id.prodMk continuous_const)
  exact ((invariantCoefficientQuotientProjection R G X W hW).hom.cont.comp hx).congr
    (fun g => (invariantCoefficientQuotientProjection R G X W hW).hom.isIntertwining g x)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A scalar annihilator is inherited by the actual coefficient quotient. -/
theorem invariantCoefficientQuotient_smul_eq_zero
    [DiscreteTopology X] (m : R) (hm : ∀ x : X, m • x = 0)
    (q : invariantCoefficientQuotient R G X W hW) : m • q = 0 := by
  obtain ⟨x, rfl⟩ := invariantCoefficientQuotientProjection_surjective R G X W hW q
  exact ((invariantCoefficientQuotientProjection R G X W hW).hom.map_smul m x).symm.trans
    ((congrArg (invariantCoefficientQuotientProjection R G X W hW) (hm x)).trans
      (map_zero (invariantCoefficientQuotientProjection R G X W hW).hom))

end TopRep
