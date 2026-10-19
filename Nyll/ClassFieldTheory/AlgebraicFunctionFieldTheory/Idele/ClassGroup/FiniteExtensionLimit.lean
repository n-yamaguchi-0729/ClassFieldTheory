/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionSystem
import Mathlib.Algebra.Colimit.DirectLimit

/-!
# The finite-extension idele-class direct limit

The stages are the actual all-place idele class groups of the finite Galois
intermediate extensions of a function field. Their transition maps are the
proved inclusions on idele classes. Mathlib's directed quotient supplies the
commutative group structure, and injectivity of these concrete transition maps
ensures that every finite stage embeds in the limit.

The representative and equality lemmas reduce questions in the limit to finite
extensions. The universal lift applies to compatible maps out of these actual
stages; no reciprocity or class-formation hypothesis enters the construction.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionLimit

open FiniteExtensionSystem

variable {k K Ω : Type*} [Field k] [PerfectField k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω]
    [IsScalarTower (RatFunc k) K Ω] [IsScalarTower k (RatFunc k) Ω]
    [FunctionField k K]

/-- The direct limit of the actual finite Galois idele class groups in `Ω / K`. -/
abbrev Limit (k K Ω : Type*) [Field k] [PerfectField k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω]
    [IsScalarTower (RatFunc k) K Ω] [IsScalarTower k (RatFunc k) Ω]
    [FunctionField k K] :=
  _root_.DirectLimit (stage (k := k) (K := K) (Ω := Ω))
    (fun E F h => transition (k := k) E F h)

/-- The canonical homomorphism from a finite Galois idele class group to the limit. -/
def of (E : FiniteGaloisIntermediateField K Ω) : stage (k := k) E →* Limit k K Ω where
  toFun c := ⟦⟨E, c⟩⟧
  map_one' := (DirectLimit.one_def
    (G := stage (k := k) (K := K) (Ω := Ω))
    (f := fun E F h => transition (k := k) E F h) E).symm
  map_mul' c d := (DirectLimit.mul_def
    (G := stage (k := k) (K := K) (Ω := Ω))
    (f := fun E F h => transition (k := k) E F h) E c d).symm

/-- Moving a representative along an actual field inclusion does not change its limit class. -/
@[simp]
theorem of_transition (E F : FiniteGaloisIntermediateField K Ω) (h : E ≤ F)
    (c : stage (k := k) E) :
    of (k := k) (K := K) (Ω := Ω) F (transition (k := k) E F h c) =
      of (k := k) (K := K) (Ω := Ω) E c :=
  DirectLimit.mk_apply
    (F := stage (k := k) (K := K) (Ω := Ω))
    (f := fun E F h => transition (k := k) E F h) E F c h

/-- Each actual finite-stage idele class group embeds in the direct limit. -/
theorem of_injective (E : FiniteGaloisIntermediateField K Ω) :
    Function.Injective (of (k := k) (K := K) (Ω := Ω) E) :=
  DirectLimit.mk_injective
    (F := stage (k := k) (K := K) (Ω := Ω))
    (fun E F h => transition (k := k) E F h)
    (fun E F h => transition_injective (k := k) E F h) E

@[simp]
theorem of_eq_one_iff (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E) : of (k := k) (K := K) (Ω := Ω) E c = 1 ↔ c = 1 := by
  rw [← map_one (of (k := k) (K := K) (Ω := Ω) E),
    (of_injective (k := k) (K := K) (Ω := Ω) E).eq_iff]

/-- Every limit class has a representative in one actual finite extension. -/
theorem exists_of (c : Limit k K Ω) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (a : stage (k := k) E),
      of (k := k) (K := K) (Ω := Ω) E a = c := by
  obtain ⟨E, a, ha⟩ := DirectLimit.exists_eq_mk
    (F := stage (k := k) (K := K) (Ω := Ω))
    (fun E F h => transition (k := k) E F h) c
  exact ⟨E, a, ha.symm⟩

/-- Two limit classes can be represented in the same finite Galois extension. -/
theorem exists_of₂ (c d : Limit k K Ω) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (a b : stage (k := k) E),
      of (k := k) (K := K) (Ω := Ω) E a = c ∧ of (k := k) (K := K) (Ω := Ω) E b = d := by
  obtain ⟨E, a, b, ha, hb⟩ := DirectLimit.exists_eq_mk₂
    (F := stage (k := k) (K := K) (Ω := Ω))
    (fun E F h => transition (k := k) E F h) c d
  exact ⟨E, a, b, ha.symm, hb.symm⟩

/-- A representative may be chosen above any prescribed finite Galois stage. -/
theorem exists_of_above (E : FiniteGaloisIntermediateField K Ω) (c : Limit k K Ω) :
    ∃ (F : FiniteGaloisIntermediateField K Ω), E ≤ F ∧
      ∃ a : stage (k := k) F, of (k := k) (K := K) (Ω := Ω) F a = c := by
  obtain ⟨F, a, rfl⟩ := exists_of (k := k) (K := K) (Ω := Ω) c
  exact ⟨E ⊔ F, le_sup_left, transition (k := k) F (E ⊔ F) le_sup_right a,
    of_transition (k := k) (K := K) (Ω := Ω) F (E ⊔ F) le_sup_right a⟩

/-- Equality in the limit is witnessed by equality after actual finite base changes. -/
theorem of_eq_of_iff (E F : FiniteGaloisIntermediateField K Ω)
    (a : stage (k := k) E) (b : stage (k := k) F) :
    of (k := k) (K := K) (Ω := Ω) E a = of (k := k) (K := K) (Ω := Ω) F b ↔
      ∃ (H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hFH : F ≤ H),
        transition (k := k) E H hEH a = transition (k := k) F H hFH b :=
  Quotient.eq

/-- For nested fields, equality in the limit is already detected in the larger stage. -/
theorem of_eq_of_iff_of_le (E F : FiniteGaloisIntermediateField K Ω) (h : E ≤ F)
    (a : stage (k := k) E) (b : stage (k := k) F) :
    of (k := k) (K := K) (Ω := Ω) E a = of (k := k) (K := K) (Ω := Ω) F b ↔
      transition (k := k) E F h a = b := by
  rw [← of_transition (k := k) (K := K) (Ω := Ω) E F h a,
    (of_injective (k := k) (K := K) (Ω := Ω) F).eq_iff]

/-- Propositions about the actual limit can be proved on finite-stage representatives. -/
@[elab_as_elim]
theorem induction_on {P : Limit k K Ω → Prop} (c : Limit k K Ω)
    (h : ∀ (E : FiniteGaloisIntermediateField K Ω) (a : stage (k := k) E),
      P (of (k := k) (K := K) (Ω := Ω) E a)) :
    P c := by
  obtain ⟨E, a, rfl⟩ := exists_of (k := k) (K := K) (Ω := Ω) c
  exact h E a

section UniversalProperty

variable {A : Type*} [CommGroup A]

/-- Bundle the existing direct-limit lift before substituting the concrete field stages. -/
private def liftMonoidHom {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type*) [∀ i, CommGroup (G i)]
    (t : ∀ i j, i ≤ j → G i →* G j) [DirectedSystem G (t · · ·)]
    (f : ∀ i, G i →* A) (hf : ∀ i j h x, f j (t i j h x) = f i x) :
    DirectLimit G t →* A where
  toFun := DirectLimit.lift t (fun i => f i) (fun i j h x => (hf i j h x).symm)
  map_one' := DirectLimit.lift_one
    (G := G) (H := fun i => G i →* A) (f := t)
    f (fun i j h x => (hf i j h x).symm)
  map_mul' x y := DirectLimit.lift_mul
    (G := G) (H := fun i => G i →* A) (f := t)
    f (fun i j h x => (hf i j h x).symm) x y

/-- Compatible homomorphisms from the concrete finite stages induce a homomorphism
from their idele-class direct limit. -/
def lift (f : ∀ E : FiniteGaloisIntermediateField K Ω, stage (k := k) E →* A)
    (hf : ∀ E F h c, f F (transition (k := k) E F h c) = f E c) :
    Limit k K Ω →* A :=
  liftMonoidHom (stage (k := k) (K := K) (Ω := Ω))
    (fun E F h => transition (k := k) E F h) f hf

@[simp]
theorem lift_of (f : ∀ E : FiniteGaloisIntermediateField K Ω, stage (k := k) E →* A)
    (hf : ∀ E F h c, f F (transition (k := k) E F h c) = f E c)
    (E : FiniteGaloisIntermediateField K Ω) (c : stage (k := k) E) :
    lift (k := k) (K := K) (Ω := Ω) f hf (of (k := k) (K := K) (Ω := Ω) E c) = f E c :=
  rfl

/-- Homomorphisms out of the limit are determined by their restrictions to actual finite stages. -/
@[ext]
theorem hom_ext {f g : Limit k K Ω →* A}
    (h : ∀ E : FiniteGaloisIntermediateField K Ω,
      f.comp (of (k := k) (K := K) (Ω := Ω) E) =
        g.comp (of (k := k) (K := K) (Ω := Ω) E)) :
    f = g := by
  apply MonoidHom.ext
  intro c
  obtain ⟨E, a, rfl⟩ := exists_of (k := k) (K := K) (Ω := Ω) c
  exact DFunLike.congr_fun (h E) a

/-- The induced homomorphism is the unique extension of its finite-stage maps. -/
theorem lift_unique (f : ∀ E : FiniteGaloisIntermediateField K Ω, stage (k := k) E →* A)
    (hf : ∀ E F h c, f F (transition (k := k) E F h c) = f E c)
    (g : Limit k K Ω →* A) (hg : ∀ E, g.comp (of (k := k) (K := K) (Ω := Ω) E) = f E) :
    g = lift (k := k) (K := K) (Ω := Ω) f hf := by
  apply hom_ext (k := k) (K := K) (Ω := Ω)
  intro E
  rw [hg E]
  exact MonoidHom.ext (fun _ => rfl)

end UniversalProperty

end FunctionField.IdeleClassGroup.FiniteExtensionLimit
