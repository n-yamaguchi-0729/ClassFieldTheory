/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.AbsoluteMuNTopRep
public import Nyll.GaloisCohomology.Topology.ContinuousDual
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The natural twisted dual of finite Galois coefficients

The coefficients of exponent `n` are dualized into the actual roots of unity
with their natural action. The construction supplies the jointly continuous
action and its equivariant evaluation without choosing a primitive root.
-/

@[expose] public section

open CategoryTheory ClassFieldTower.Martinet.Shafarevich
open scoped Topology

noncomputable section

universe u

namespace LocalClassFieldTheory

variable (K : Type u) [Field K] (n : ℕ+)
variable (A : TopRep.{u} (ZMod (n : ℕ)) (Field.absoluteGaloisGroup K))

/-- The natural roots-of-unity dual, with the contragredient action on the
same linear maps and the discrete topology. -/
def localTateDual : TopRep.{u} (ZMod (n : ℕ)) (Field.absoluteGaloisGroup K) :=
  TopRep.discreteLinearDual A (absoluteMuNTopRep K (n : ℕ))

instance localTateDual_discrete : DiscreteTopology (localTateDual K n A) :=
  TopRep.discreteLinearDual_discrete _ _

/-- A twisted dual coefficient has the underlying original linear map. -/
def localTateDualLinearMap (f : localTateDual K n A) :
    A →ₗ[ZMod (n : ℕ)] AbsoluteMuN K (n : ℕ) :=
  f

/-- The linear-map carrier has the same additive homomorphisms as
`Hom_ℤ(A, μₙ)`. -/
def localTateDualAddHomEquiv : localTateDual K n A ≃+ (A →+ AbsoluteMuN K (n : ℕ)) where
  toFun f := (localTateDualLinearMap K n A f).toAddMonoidHom
  invFun f := f.toZModLinearMap (n : ℕ)
  left_inv f := LinearMap.ext fun a => show
    localTateDualLinearMap K n A f a = localTateDualLinearMap K n A f a from rfl
  right_inv f := AddMonoidHom.ext fun a => show f.toZModLinearMap (n : ℕ) a = f a from rfl
  map_add' f g := AddMonoidHom.ext fun a => show
    localTateDualLinearMap K n A (f + g) a =
      localTateDualLinearMap K n A f a + localTateDualLinearMap K n A g a from rfl

/-- A finite coefficient module has finite twisted dual. -/
theorem localTateDual_finite [Finite A] : Finite (localTateDual K n A) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact Finite.of_injective
    (fun f : localTateDual K n A =>
      (localTateDualLinearMap K n A f : A → AbsoluteMuN K (n : ℕ)))
    (fun _ _ h => LinearMap.ext fun x => congrFun h x)

/-- The action conjugates a coefficient homomorphism by the original
Galois actions on its source and target. -/
theorem localTateDual_action_apply (σ : Field.absoluteGaloisGroup K)
    (f : localTateDual K n A) (a : A) :
    localTateDualLinearMap K n A ((localTateDual K n A).ρ σ f) a =
      (absoluteMuNTopRep K (n : ℕ)).ρ σ (localTateDualLinearMap K n A f (A.ρ σ⁻¹ a)) :=
  rfl

/-- Evaluation is equivariant for the simultaneous Galois action. -/
theorem localTateDual_evaluation_equivariant (σ : Field.absoluteGaloisGroup K)
    (f : localTateDual K n A) (a : A) :
    localTateDualLinearMap K n A ((localTateDual K n A).ρ σ f) (A.ρ σ a) =
      (absoluteMuNTopRep K (n : ℕ)).ρ σ (localTateDualLinearMap K n A f a) :=
  TopRep.discreteLinearDualEvaluation_equivariant A (absoluteMuNTopRep K (n : ℕ)) σ a f

/-- The full twisted dual action is jointly continuous when the original
finite discrete coefficient action is jointly continuous. -/
theorem localTateDual_action_continuous [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun p : Field.absoluteGaloisGroup K × A => A.ρ p.1 p.2)) :
    Continuous (fun p : Field.absoluteGaloisGroup K × localTateDual K n A =>
      (localTateDual K n A).ρ p.1 p.2) := by
  let : DiscreteTopology (absoluteMuNTopRep K (n : ℕ)) :=
    inferInstanceAs (DiscreteTopology (AbsoluteMuN K (n : ℕ)))
  exact TopRep.discreteLinearDual_action_continuous A (absoluteMuNTopRep K (n : ℕ)) hA
    (absoluteMuNTopRep_action_continuous K (n : ℕ))

end LocalClassFieldTheory
