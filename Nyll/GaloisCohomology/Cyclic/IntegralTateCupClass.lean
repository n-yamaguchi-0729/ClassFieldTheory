/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupUnit

/-!
# Degree-two classes and the twice shifted coefficient map

Two original coinduced connecting maps lift every degree-two class from
a fixed vector of the twice shifted coefficient. Cup with that class is
the map of the vector's equivariant tensor inclusion followed by the two
corresponding tensor connecting maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped RepTensor

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- The actual degree-two class obtained by the two successive upward
connecting maps from an original fixed vector. -/
def tateClassOfDoubleShift (B : Rep.{u} ℤ G)
    (b : (Rep.coindShiftUp (Rep.coindShiftUp B)).ρ.invariants) :
    tate B 2 :=
  coindShiftUpEquiv B 1 (coindShiftUpEquiv (Rep.coindShiftUp B) 0
    (fixedClass (Rep.coindShiftUp (Rep.coindShiftUp B)) b))

/-- Every original degree-two Tate class has a fixed representative in
the twice shifted coefficients. -/
theorem tateClassOfDoubleShift_surjective (B : Rep.{u} ℤ G) :
    Function.Surjective (tateClassOfDoubleShift B) :=
  (coindShiftUpEquiv B 1).surjective.comp
    ((coindShiftUpEquiv (Rep.coindShiftUp B) 0).surjective.comp
      (fixedClass_surjective (Rep.coindShiftUp (Rep.coindShiftUp B))))

/-- Cup with a twice shifted class is the actual equivariant coefficient map
followed by the two tensor shifts. Both signs are `(-1)^p` and cancel. -/
theorem tateCup_classOfDoubleShift (A B : Rep.{u} ℤ G) (p : ℤ) (x : tate A p)
    (b : (Rep.coindShiftUp (Rep.coindShiftUp B)).ρ.invariants) :
    tateCup A B p 2 (p + 1 + 1) (by omega) x (tateClassOfDoubleShift B b) =
      tensorCoindShiftEquiv A B (p + 1) (tensorCoindShiftEquiv A (Rep.coindShiftUp B) p
        ((tateFunctor G p).map
          (Rep.tensorInvariant A (Rep.coindShiftUp (Rep.coindShiftUp B)) b) x)) := by
  let C := Rep.coindShiftUp (Rep.coindShiftUp B)
  let c := fixedClass C b
  have e₂ := tateCup_coindShift_connecting A B (by decide : 0 ≤ (1 : ℤ))
    (rfl : p + 1 = p + 1) x (coindShiftUpEquiv (Rep.coindShiftUp B) 0 c)
  have e₁ := tateCup_coindShift_connecting A (Rep.coindShiftUp B) (by decide : 0 ≤ (0 : ℤ))
    (add_zero p) x c
  change tateCup A (Rep.coindShiftUp B) p 1 (p + 1) (by omega) x
    (coindShiftUpEquiv (Rep.coindShiftUp B) 0 c) = _ at e₁
  rw [tateCup_zero_right, tensorCupZeroRight_fixedClass] at e₁
  change tateCup A B p 2 (p + 1 + 1) (by omega) x (tateClassOfDoubleShift B b) = _ at e₂
  rw [e₂, e₁]
  have hS (z : tate (A ⊗ᵣ Rep.coindShiftUp B) (p + 1)) :
      tensorCoindShiftEquiv A B (p + 1) (p.negOnePow • z) =
        p.negOnePow • tensorCoindShiftEquiv A B (p + 1) z := by
    simp only [Units.smul_def]
    exact (tensorCoindShiftEquiv A B (p + 1)).toAddEquiv.toAddMonoidHom.map_zsmul
      (p.negOnePow : ℤ) z
  rw [hS, smul_smul, Int.units_mul_self, one_smul]

end IntegralGroupCohomology.Universe
