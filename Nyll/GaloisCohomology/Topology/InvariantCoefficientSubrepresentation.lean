/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Invariant coefficient subrepresentations with inherited topology

The algebraic action is Mathlib's existing subrepresentation. Continuous
linear restriction gives its inherited topology and the actual inclusion
into the original topological representation.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory ContRepresentation

namespace TopRep

variable (R : Type v) [Ring R] [TopologicalSpace R]
  (G : Type u) [Monoid G] (X : TopRep.{u} R G)
  (W : Submodule R X) (hW : ∀ g : G, W ≤ W.comap (X.ρ g).toLinearMap)

/-- The actual coefficient subrepresentation with the inherited topology. -/
def invariantSubmoduleTopRep : TopRep.{u} R G := by
  let A := X.ρ.toRepresentation.subrepresentation W hW
  let π : ContRepresentation R G W :=
    { toMonoidHom :=
      { toFun := fun g => (X.ρ g).restrict (hW g)
        map_one' := by
          apply ContinuousLinearMap.ext
          intro w
          exact congrArg (fun f : Module.End R W => f w) (map_one A)
        map_mul' := by
          intro g h
          apply ContinuousLinearMap.ext
          intro w
          exact congrArg (fun f : Module.End R W => f w) (map_mul A g h) } }
  exact TopRep.of π

/-- The actual inclusion of an invariant coefficient subrepresentation. -/
def invariantSubmoduleInclusion :
    invariantSubmoduleTopRep R G X W hW ⟶ X := by
  let f : (invariantSubmoduleTopRep R G X W hW).ρ →ⁱL X.ρ :=
    { toContinuousLinearMap := W.subtypeL
      isIntertwining' := fun g => by
        apply ContinuousLinearMap.ext
        intro w
        rfl }
  exact ConcreteCategory.ofHom (C := TopRep R G) f

/-- Restricting discrete coefficients preserves their discrete topology. -/
instance invariantSubmoduleTopRep_discrete [DiscreteTopology X] :
    DiscreteTopology (invariantSubmoduleTopRep R G X W hW) :=
  inferInstanceAs (DiscreteTopology W)

/-- The actual coefficient inclusion is injective. -/
theorem invariantSubmoduleInclusion_injective :
    Function.Injective (invariantSubmoduleInclusion R G X W hW) :=
  Subtype.val_injective

/-- A jointly continuous action restricts to a jointly continuous action
on the actual invariant coefficient subrepresentation. -/
theorem invariantSubmoduleTopRep_action_continuous [TopologicalSpace G]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    Continuous (fun gw : G × invariantSubmoduleTopRep R G X W hW =>
      (invariantSubmoduleTopRep R G X W hW).ρ gw.1 gw.2) :=
  Continuous.subtype_mk
    (hX.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _

end TopRep
