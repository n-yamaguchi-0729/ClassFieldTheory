/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite-tuple coordinates for actual continuous cochains

For a locally compact group, iterated continuous function spaces are
continuously and linearly equivalent to continuous functions on finite
powers. The actual action becomes the diagonal homogeneous action.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory ContRepresentation

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Splitting off the first coordinate of a finite tuple is a homeomorphism. -/
def finiteTupleConsHomeomorph (n : ℕ) : G × (Fin n → G) ≃ₜ (Fin (n + 1) → G) where
  toEquiv := Fin.consEquiv (fun _ => G)
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)

variable [LocallyCompactSpace G] (X : TopRep.{u} ℤ G)

/-- Tuple coordinates on the actual iterated continuous-coinduction term. -/
def resolutionTupleHomeomorph : (n : ℕ) →
    resolutionX X n ≃ₜ C(Fin n → G, X)
  | 0 => Homeomorph.continuousMapOfUnique
  | n + 1 =>
    ((Homeomorph.arrowCongr (Homeomorph.refl G) (resolutionTupleHomeomorph n)).trans
      Homeomorph.curry.symm).trans
        (Homeomorph.arrowCongr (finiteTupleConsHomeomorph G n) (Homeomorph.refl X))

/-- The zero-coordinate evaluation is the original coefficient. -/
theorem resolutionTupleHomeomorph_zero_apply (x : X) (a : Fin 0 → G) :
    resolutionTupleHomeomorph G X 0 x a = x := rfl

/-- Tuple evaluation agrees with successive actual function evaluation. -/
theorem resolutionTupleHomeomorph_succ_apply (n : ℕ)
    (f : resolutionX X (n + 1)) (a : Fin (n + 1) → G) :
    resolutionTupleHomeomorph G X (n + 1) f a =
      resolutionTupleHomeomorph G X n (f (a 0)) (fun i => a i.succ) := rfl

/-- Tuple evaluation preserves addition in every degree. -/
theorem resolutionTupleHomeomorph_add (n : ℕ) (f g : resolutionX X n) :
    resolutionTupleHomeomorph G X n (f + g) =
      resolutionTupleHomeomorph G X n f + resolutionTupleHomeomorph G X n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply ContinuousMap.ext
    intro a
    change resolutionTupleHomeomorph G X n (f (a 0) + g (a 0)) (fun i => a i.succ) = _
    exact congrArg (fun h : C(Fin n → G, X) => h (fun i => a i.succ))
      (ih (f (a 0)) (g (a 0)))

/-- Tuple evaluation preserves the integral coefficient-module structure. -/
theorem resolutionTupleHomeomorph_smul (n : ℕ) (r : ℤ) (f : resolutionX X n) :
    resolutionTupleHomeomorph G X n (r • f) = r • resolutionTupleHomeomorph G X n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply ContinuousMap.ext
    intro a
    change resolutionTupleHomeomorph G X n (r • f (a 0)) (fun i => a i.succ) = _
    exact congrArg (fun h : C(Fin n → G, X) => h (fun i => a i.succ)) (ih (f (a 0)))

/-- The tuple comparison is a continuous linear equivalence, not just a bijection. -/
def resolutionTupleContinuousLinearEquiv (n : ℕ) :
    resolutionX X n ≃L[ℤ] C(Fin n → G, X) where
  toLinearEquiv :=
    { toEquiv := (resolutionTupleHomeomorph G X n).toEquiv
      map_add' := resolutionTupleHomeomorph_add G X n
      map_smul' := resolutionTupleHomeomorph_smul G X n }
  continuous_toFun := (resolutionTupleHomeomorph G X n).continuous_toFun
  continuous_invFun := (resolutionTupleHomeomorph G X n).continuous_invFun

/-- The actual coinduced action becomes the diagonal action on tuple coordinates. -/
theorem resolutionTupleHomeomorph_action (n : ℕ) (σ : G)
    (f : resolutionX X n) (a : Fin n → G) :
    resolutionTupleHomeomorph G X n ((resolutionX X n).ρ σ f) a =
      X.ρ σ (resolutionTupleHomeomorph G X n f (fun i => σ⁻¹ * a i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change resolutionTupleHomeomorph G X n
      ((resolutionX X n).ρ σ (f (σ⁻¹ * a 0))) (fun i => a i.succ) =
      X.ρ σ (resolutionTupleHomeomorph G X n (f (σ⁻¹ * a 0))
        (fun i => σ⁻¹ * a i.succ))
    exact ih _ _

/-- Actual homogeneous cochains give equivariant continuous tuple functions. -/
theorem homogeneousCochain_tuple_equivariant (n : ℕ)
    (z : (homogeneousCochains X).X n) (σ : G) (a : Fin (n + 1) → G) :
    resolutionTupleHomeomorph G X (n + 1) z.val (fun i => σ * a i) =
      X.ρ σ (resolutionTupleHomeomorph G X (n + 1) z.val a) := by
  have h := congrArg (fun f => resolutionTupleHomeomorph G X (n + 1) f
    (fun i => σ * a i)) (z.property σ)
  rw [resolutionTupleHomeomorph_action] at h
  have ha : (fun i => σ⁻¹ * (σ * a i)) = a :=
    funext (fun i => inv_mul_cancel_left σ (a i))
  rw [ha] at h
  exact h.symm

/-- In tuple coordinates the actual continuous-cochain differential is the
usual alternating sum of coordinate omissions. -/
theorem resolutionTupleHomeomorph_d (n : ℕ) (f : resolutionX X n)
    (a : Fin (n + 1) → G) :
    resolutionTupleHomeomorph G X (n + 1) ((d X n).hom f) a =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) •
        resolutionTupleHomeomorph G X n f (fun j => a (i.succAbove j)) := by
  induction n with
  | zero =>
    change f = ∑ i : Fin 1, (-1 : ℤ) ^ (i : ℕ) • f
    simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul]
  | succ n ih =>
    change resolutionTupleHomeomorph G X (n + 1)
      (f - (d X n).hom (f (a 0))) (fun j => a j.succ) = _
    have hsub : resolutionTupleHomeomorph G X (n + 1)
        (f - (d X n).hom (f (a 0))) =
        resolutionTupleHomeomorph G X (n + 1) f -
          resolutionTupleHomeomorph G X (n + 1) ((d X n).hom (f (a 0))) :=
      (resolutionTupleContinuousLinearEquiv G X (n + 1)).map_sub _ _
    rw [hsub]
    change resolutionTupleHomeomorph G X (n + 1) f (fun j => a j.succ) -
      resolutionTupleHomeomorph G X (n + 1) ((d X n).hom (f (a 0)))
        (fun j => a j.succ) = _
    rw [ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.zero_succAbove,
      Fin.val_succ]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ, mul_neg_one, neg_smul]
    have hface :
        resolutionTupleHomeomorph G X (n + 1) f (fun j => a (i.succ.succAbove j)) =
        resolutionTupleHomeomorph G X n (f (a 0))
          (fun j => a (i.succAbove j).succ) :=
      (resolutionTupleHomeomorph_succ_apply G X n f
        (fun j => a (i.succ.succAbove j))).trans
        (congrArg₂ (fun x t => resolutionTupleHomeomorph G X n x t)
          (congrArg f (congrArg a (Fin.succ_succAbove_zero i)))
          (funext (fun j => congrArg a (Fin.succ_succAbove_succ i j))))
    exact congrArg (fun x => -(((-1 : ℤ) ^ (i : ℕ)) • x)) hface.symm

/-- Every continuous equivariant tuple function is an actual homogeneous cochain. -/
def homogeneousCochainOfTuple (n : ℕ) (f : C(Fin (n + 1) → G, X))
    (hf : ∀ (σ : G) (a : Fin (n + 1) → G),
      f (fun i => σ * a i) = X.ρ σ (f a)) :
    (homogeneousCochains X).X n := by
  let H := resolutionTupleHomeomorph G X (n + 1)
  refine ⟨H.symm f, ?_⟩
  intro σ
  apply H.injective
  apply ContinuousMap.ext
  intro a
  have hh := congrArg (fun h : C(Fin (n + 1) → G, X) => h a) (H.apply_symm_apply f)
  have hh' := congrArg (fun h : C(Fin (n + 1) → G, X) =>
    h (fun i => σ⁻¹ * a i)) (H.apply_symm_apply f)
  have ha : (fun i => σ * (σ⁻¹ * a i)) = a :=
    funext (fun i => mul_inv_cancel_left σ (a i))
  have he := hf σ (fun i => σ⁻¹ * a i)
  rw [ha] at he
  exact (resolutionTupleHomeomorph_action G X (n + 1) σ (H.symm f) a).trans
    ((congrArg (fun x => X.ρ σ x) hh').trans (he.symm.trans hh.symm))

/-- The tuple-to-cochain construction returns precisely the supplied tuple function. -/
theorem homogeneousCochainOfTuple_apply (n : ℕ) (f : C(Fin (n + 1) → G, X))
    (hf : ∀ (σ : G) (a : Fin (n + 1) → G),
      f (fun i => σ * a i) = X.ρ σ (f a)) :
    resolutionTupleHomeomorph G X (n + 1) (homogeneousCochainOfTuple G X n f hf).val = f :=
  (resolutionTupleHomeomorph G X (n + 1)).apply_symm_apply f

end TopRep
