/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.RepresentationTheory.Induced

/-!
# The actual induced dimension-shifting sequence

The induction-restriction counit is surjective: the class of `1 ⊗ a`
maps to `a`. Its actual kernel supplies the downward shifting sequence.
The scalar ring and acting group have independent universes; the coefficients
live in the common universe needed by induction.
-/

@[expose] public section

noncomputable section

universe u uR

open CategoryTheory CategoryTheory.Limits

namespace Rep

variable {R : Type uR} {G : Type u} [CommRing R] [Group G]

/-- The actual counit of induction from the trivial subgroup. -/
def indShiftCounit (A : Rep.{max u uR} R G) :
    ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) ⟶ A :=
  (indResHomEquiv.{max u uR} (⊥ : Subgroup G).subtype
    (res (⊥ : Subgroup G).subtype A) A).symm (𝟙 _)

/-- The underlying linear section is the class of `1 ⊗ a`. -/
def indShiftSection (A : Rep.{max u uR} R G) :
    A →ₗ[R] ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) :=
  Representation.IndV.mk (⊥ : Subgroup G).subtype
    (res (⊥ : Subgroup G).subtype A).ρ 1

/-- The specified section recovers every original coefficient under the counit. -/
theorem indShiftCounit_section (A : Rep.{max u uR} R G) (a : A) :
    (indShiftCounit A).hom (indShiftSection A a) = a :=
  congrArg (fun f : res (⊥ : Subgroup G).subtype A ⟶
    res (⊥ : Subgroup G).subtype A => f.hom a)
    ((indResHomEquiv.{max u uR} (⊥ : Subgroup G).subtype
      (res (⊥ : Subgroup G).subtype A) A).apply_symm_apply (𝟙 _))

/-- The counit is an epimorphism because its underlying linear map has a section. -/
instance indShiftCounit_epi (A : Rep.{max u uR} R G) : Epi (indShiftCounit A) :=
  (epi_iff_surjective _).mpr fun a => ⟨indShiftSection A a, indShiftCounit_section A a⟩

/-- The downward shift is the actual kernel of the induction counit. -/
def indShiftDown (A : Rep.{max u uR} R G) : Rep.{max u uR} R G :=
  kernel (indShiftCounit A)

/-- The original kernel inclusion and counit form the downward shifting sequence. -/
def indShiftSequence (A : Rep.{max u uR} R G) : ShortComplex (Rep.{max u uR} R G) :=
  ShortComplex.kernelSequence (indShiftCounit A)

/-- The induced shifting sequence is short exact, with no acyclicity input. -/
theorem indShiftSequence_shortExact (A : Rep.{max u uR} R G) :
    (indShiftSequence A).ShortExact where
  exact := ShortComplex.kernelSequence_exact (indShiftCounit A)
  mono_f := by change Mono (kernel.ι (indShiftCounit A)); infer_instance
  epi_g := by change Epi (indShiftCounit A); infer_instance

end Rep
