/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousCoinducedPrimitives
public import Nyll.GaloisCohomology.Topology.DiscreteCoefficientQuotient

/-!
# The actual discrete quotient of coinduction by constants

The quotient is the ordinary module quotient of continuous functions by
constant functions, with its induced group action and discrete topology.
For compact groups it is the cokernel used in continuous dimension shifting.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory ContRepresentation

namespace TopRep

variable (R : Type v) [Ring R] [TopologicalSpace R] [DiscreteTopology R]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{u} R G)

/-- Constant continuous functions form the image of the actual coinduction unit. -/
def coinducedConstantSubmodule : Submodule R X.coind₁ :=
  LinearMap.range X.ρ.coind₁ι.toContinuousLinearMap.toLinearMap

omit [DiscreteTopology R] in
/-- The constant-function submodule is preserved by the actual coinduced action. -/
theorem coinducedConstantSubmodule_invariant (g : G) :
    coinducedConstantSubmodule R G X ≤
      (coinducedConstantSubmodule R G X).comap (X.coind₁.ρ g).toLinearMap := by
  rintro f ⟨x, rfl⟩
  exact ⟨X.ρ g x, X.ρ.coind₁ι.isIntertwining g x⟩

/-- The ordinary representation on the actual quotient by constants. -/
def coinducedQuotientRep : Rep.{u} R G :=
  invariantCoefficientQuotientRep R G X.coind₁
    (coinducedConstantSubmodule R G X) (coinducedConstantSubmodule_invariant R G X)

/-- The actual quotient by constants as a discrete topological representation. -/
def coinducedQuotient : TopRep.{u} R G :=
  invariantCoefficientQuotient R G X.coind₁
    (coinducedConstantSubmodule R G X) (coinducedConstantSubmodule_invariant R G X)

/-- The quotient by constants is discrete. -/
instance coinducedQuotient_discrete : DiscreteTopology (coinducedQuotient R G X) :=
  invariantCoefficientQuotient_discrete R G X.coind₁ _ _

/-- The actual quotient projection is continuous and equivariant when the actual
coinduced coefficient space is discrete. -/
def coinducedQuotientProjection [DiscreteTopology X.coind₁] :
    X.coind₁ ⟶ coinducedQuotient R G X :=
  invariantCoefficientQuotientProjection R G X.coind₁ _ _

/-- Every quotient class has an actual continuous-function representative. -/
theorem coinducedQuotientProjection_surjective [DiscreteTopology X.coind₁] :
    Function.Surjective (coinducedQuotientProjection R G X) :=
  invariantCoefficientQuotientProjection_surjective R G X.coind₁ _ _

/-- The kernel of the actual quotient projection consists exactly of constants. -/
theorem coinducedQuotientProjection_eq_zero_iff
    [DiscreteTopology X.coind₁] (f : X.coind₁) :
    coinducedQuotientProjection R G X f = 0 ↔
      ∃ x : X, X.ρ.coind₁ι x = f :=
  invariantCoefficientQuotientProjection_eq_zero_iff R G X.coind₁ _ _ f

/-- The quotient action is jointly continuous, as follows by lifting each
orbit to the actual continuous coinduced action. -/
theorem coinducedQuotient_action_continuous
    [DiscreteTopology X.coind₁]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    Continuous (fun gq : G × coinducedQuotient R G X =>
      (coinducedQuotient R G X).ρ gq.1 gq.2) := by
  apply invariantCoefficientQuotient_action_continuous R G X.coind₁ _ _
  apply continuous_prod_of_discrete_right.mpr
  intro f
  exact ContinuousMap.continuous_of_continuous_uncurry _ (by
    have hv : Continuous (fun gx : G × G => f (gx.1⁻¹ * gx.2)) :=
      f.continuous.comp (continuous_fst.inv.mul continuous_snd)
    exact hX.comp (continuous_fst.prodMk hv))

/-- A scalar annihilating the original coefficients also annihilates
the actual quotient of coinduced coefficients by constants. -/
theorem coinducedQuotient_smul_eq_zero
    [DiscreteTopology X.coind₁] (m : R)
    (hm : ∀ x : X, m • x = 0) (q : coinducedQuotient R G X) :
    m • q = 0 :=
  invariantCoefficientQuotient_smul_eq_zero R G X.coind₁ _ _ m
    (fun f => ContinuousMap.ext (fun x => hm (f x))) q

end TopRep
