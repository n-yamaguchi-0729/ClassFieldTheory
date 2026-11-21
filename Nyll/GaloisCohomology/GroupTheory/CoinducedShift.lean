/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.RepresentationTheory.Coinduced

/-!
# The actual coinduced dimension-shifting sequence

The canonical map sends a coefficient `a` to the function `g ↦ ρ(g)a`.
Evaluation at the identity is a linear retraction, so the map is injective.
Its actual cokernel supplies a short exact sequence of representations.
-/

@[expose] public section

noncomputable section

universe u uR

open CategoryTheory CategoryTheory.Limits

namespace Rep

variable {R : Type uR} {G : Type u} [CommRing R] [Group G]

/-- Embed the original representation into actual coinduction of its
restriction to the trivial subgroup. -/
def coindShiftUnit (A : Rep.{u} R G) :
    A ⟶ coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) :=
  resCoindToHom (⊥ : Subgroup G).subtype A
    (res (⊥ : Subgroup G).subtype A) (𝟙 _)

/-- The embedding uses the original action on each coefficient. -/
theorem coindShiftUnit_apply (A : Rep.{u} R G) (a : A) (g : G) :
    ((coindShiftUnit A).hom a).1 g = A.ρ g a := rfl

/-- Evaluation at the identity is a linear retraction on the underlying modules. -/
def coindShiftRetraction (A : Rep.{u} R G) :
    coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) →ₗ[R] A where
  toFun f := f.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The retraction recovers the original coefficient, without equivariance
being asserted for evaluation itself. -/
theorem coindShiftRetraction_unit (A : Rep.{u} R G) (a : A) :
    coindShiftRetraction A ((coindShiftUnit A).hom a) = a := by
  change A.ρ 1 a = a
  rw [map_one, one_apply_eq_self]

instance coindShiftUnit_mono (A : Rep.{u} R G) : Mono (coindShiftUnit A) :=
  (mono_iff_injective _).mpr
    (show Function.LeftInverse (coindShiftRetraction A) (coindShiftUnit A).hom from
      coindShiftRetraction_unit A).injective

/-- The upward shift is the actual cokernel of the coinduction embedding. -/
def coindShiftUp (A : Rep.{u} R G) : Rep.{u} R G := cokernel (coindShiftUnit A)

/-- The original embedding and its cokernel projection form the shifting sequence. -/
def coindShiftSequence (A : Rep.{u} R G) : ShortComplex (Rep.{u} R G) :=
  ShortComplex.cokernelSequence (coindShiftUnit A)

/-- The coinduced shifting sequence is short exact, supplied by its explicit
linear retraction and the universal cokernel. -/
theorem coindShiftSequence_shortExact (A : Rep.{u} R G) :
    (coindShiftSequence A).ShortExact where
  exact := ShortComplex.cokernelSequence_exact (coindShiftUnit A)
  mono_f := by change Mono (coindShiftUnit A); infer_instance
  epi_g := by change Epi (cokernel.π (coindShiftUnit A)); infer_instance

end Rep
