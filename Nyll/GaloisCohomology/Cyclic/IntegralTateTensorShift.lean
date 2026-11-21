/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex), Claude

The tensor trace argument follows Tau Ceti's
`RepresentationTheory/Homological/TateCohomology/Coinduced.lean`.
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.FiniteIndex
public import Nyll.GaloisCohomology.Cyclic.IntegralTateExactness
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTraceVanishing
public import Nyll.GaloisCohomology.Cyclic.TateCoinducedVanishing
public import Nyll.GaloisCohomology.GroupTheory.CoinducedShiftNaturality
public import Nyll.GaloisCohomology.GroupTheory.InducedShiftNaturality
public import Nyll.GaloisCohomology.GroupTheory.TensorShiftExactness

/-!
# Integral Tate cohomology of the tensor dimension shifts

The projection onto the identity coordinate of coinduction has trace equal
to the identity. This remains true after tensoring with any representation.
The tensor dimension shifts use the connecting maps in the resulting exact
sequences and the vanishing of their induced or coinduced middle terms.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped RepTensor BigOperators TensorProduct

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- A trace identity also gives Tate acyclicity after diagonal tensoring. -/
theorem tate_tensor_isZero_of_trace_identity (A C : Rep.{u} ℤ G) (p : C →ₗ[ℤ] C)
    (hp : ∀ a : C, a = ∑ g : G, C.ρ g⁻¹ (p (C.ρ g a))) (n : ℤ) :
    IsZero (tate (A ⊗ᵣ C) n) := by
  apply tate_isZero_of_trace_identity (A ⊗ᵣ C) (p.lTensor A) _ n
  let X := A ⊗ᵣ C
  let pX : X →ₗ[ℤ] X := p.lTensor A
  let traceTerm (g : G) : X →ₗ[ℤ] X := (X.ρ g⁻¹).comp (pX.comp (X.ρ g))
  let t : X →ₗ[ℤ] X := ∑ g : G, traceTerm g
  have ht_apply (x : X) : t x = ∑ g : G, traceTerm g x := LinearMap.sum_apply _ _ _
  have ht : (LinearMap.id : X →ₗ[ℤ] X) = t := by
    apply TensorProduct.ext'
    intro a c
    let x : X := a ⊗ₜ[ℤ] c
    change x = t x
    rw [ht_apply]
    calc
      a ⊗ₜ[ℤ] c = a ⊗ₜ[ℤ] (∑ g : G, C.ρ g⁻¹ (p (C.ρ g c))) :=
        congrArg (fun z : C => a ⊗ₜ[ℤ] z) (hp c)
      _ = _ := by
        rw [TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro g _
        change a ⊗ₜ[ℤ] C.ρ g⁻¹ (p (C.ρ g c)) =
          TensorProduct.map (A.ρ g⁻¹) (C.ρ g⁻¹)
            ((p.lTensor A) (TensorProduct.map (A.ρ g) (C.ρ g) (a ⊗ₜ[ℤ] c)))
        rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, TensorProduct.map_tmul]
        have hAg : A.ρ g⁻¹ (A.ρ g a) = a := by
          rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
          rfl
        rw [hAg]
  intro x
  calc
    x = t x := DFunLike.congr_fun ht x
    _ = ∑ g : G, X.ρ g⁻¹ ((p.lTensor A) (X.ρ g x)) := ht_apply x

/-- The diagonal tensor with a representation coinduced from the trivial
subgroup is Tate acyclic in every degree. -/
theorem tate_tensorCoindBot_isZero (A : Rep.{u} ℤ G) (B : Rep.{u} ℤ (⊥ : Subgroup G))
    (n : ℤ) : IsZero (tate (A ⊗ᵣ Rep.coind (⊥ : Subgroup G).subtype B) n) := by
  classical
  let C := Rep.coind (⊥ : Subgroup G).subtype B
  let point := Rep.coindPoint B
  let ev : C →+ C :=
    { toFun := fun f => point (f.val 1)
      map_zero' := map_zero point
      map_add' := fun f g => map_add point (f.val 1) (g.val 1) }
  let linear (D : Rep.{u} ℤ G) (f : D →+ D) : D →ₗ[ℤ] D := {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun z x => (congrArg f (int_smul_eq_zsmul D.hV2 z x)).trans
      ((map_zsmul f z x).trans (int_smul_eq_zsmul D.hV2 z (f x)).symm) }
  let p := linear C ev
  apply tate_tensor_isZero_of_trace_identity A C p _ n
  intro f
  apply Subtype.ext
  funext h
  let eval : C →+ B :=
    { toFun := fun v => v.val h
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change f.val h = eval (∑ g : G, C.ρ g⁻¹ (p (C.ρ g f)))
  rw [map_sum]
  have hterm (g : G) : eval (C.ρ g⁻¹ (p (C.ρ g f))) =
      if h * g⁻¹ = 1 then f.val g else 0 := by
    change (Rep.coindPoint B (f.val (1 * g))).val (h * g⁻¹) = _
    rw [Rep.coindPoint_apply]
    simp only [one_mul]
  have hsum : (∑ g : G, eval (C.ρ g⁻¹ (p (C.ρ g f)))) =
      ∑ g : G, if h * g⁻¹ = 1 then f.val g else 0 :=
    Finset.sum_congr rfl fun g _ => hterm g
  rw [hsum, Finset.sum_eq_single h
    (fun g _ hg => ite_eq_right (fun he => hg (mul_inv_eq_one.mp he).symm))
    (fun hn => (hn (Finset.mem_univ h)).elim), ite_eq_left (mul_inv_cancel h)]

/-- The same vanishing holds for induction via the finite-index comparison. -/
theorem tate_tensorIndBot_isZero (A : Rep.{u} ℤ G) (B : Rep.{u} ℤ (⊥ : Subgroup G))
    (n : ℤ) : IsZero (tate (A ⊗ᵣ Rep.ind (⊥ : Subgroup G).subtype B) n) := by
  classical
  exact (tate_tensorCoindBot_isZero A B n).of_iso
    ((tateFunctor G n).mapIso ((Rep.diagonalTensorLeft A).mapIso (Rep.indCoindIso.{u} B)))

/-- The connecting map of the original tensored coinduction sequence. -/
def tensorCoindShiftEquiv (A B : Rep.{u} ℤ G) (n : ℤ) :
    tate (A ⊗ᵣ Rep.coindShiftUp B) n ≃ₗ[ℤ] tate (A ⊗ᵣ B) (n + 1) :=
  tateδEquiv (Rep.tensorLeft_coindShiftSequence_shortExact A B) n
    (tate_tensorCoindBot_isZero A (Rep.res (⊥ : Subgroup G).subtype B) n)
    (tate_tensorCoindBot_isZero A (Rep.res (⊥ : Subgroup G).subtype B) (n + 1))

/-- The connecting map of the original tensored induction sequence. -/
def tensorIndShiftEquiv (A B : Rep.{u} ℤ G) (n : ℤ) :
    tate (A ⊗ᵣ B) n ≃ₗ[ℤ] tate (A ⊗ᵣ Rep.indShiftDown B) (n + 1) :=
  tateδEquiv (Rep.tensorLeft_indShiftSequence_shortExact A B) n
    (tate_tensorIndBot_isZero A (Rep.res (⊥ : Subgroup G).subtype B) n)
    (tate_tensorIndBot_isZero A (Rep.res (⊥ : Subgroup G).subtype B) (n + 1))

/-- The connecting map of a tensor sequence commutes with a change of the
tensor factor and a map of the original short complexes. -/
theorem tateδ_tensor_naturality {A C : Rep.{u} ℤ G}
    {S T : ShortComplex (Rep.{u} ℤ G)} (f : A ⟶ C) (g : S ⟶ T)
    (hS : (S.map (Rep.diagonalTensorLeft A)).ShortExact)
    (hT : (T.map (Rep.diagonalTensorLeft C)).ShortExact)
    (n : ℤ) (x : tate (A ⊗ᵣ S.X₃) n) :
    (tateFunctor G (n + 1)).map (f ⊗ᵣₘ g.τ₁) (tateδ hS n x) =
      tateδ hT n ((tateFunctor G n).map (f ⊗ᵣₘ g.τ₃) x) := by
  let h : S.map (Rep.diagonalTensorLeft A) ⟶ T.map (Rep.diagonalTensorLeft C) :=
    S.mapNatTrans (Rep.diagonalTensorLeftNatTrans f) ≫
      (Rep.diagonalTensorLeft C).mapShortComplex.map g
  have h₁ : h.τ₁ = f ⊗ᵣₘ g.τ₁ := by
    change (f ⊗ᵣₘ 𝟙 _) ≫ (𝟙 _ ⊗ᵣₘ g.τ₁) = _
    rw [Rep.diagonalTensorMap_comp, Category.comp_id, Category.id_comp]
  have h₃ : h.τ₃ = f ⊗ᵣₘ g.τ₃ := by
    change (f ⊗ᵣₘ 𝟙 _) ≫ (𝟙 _ ⊗ᵣₘ g.τ₃) = _
    rw [Rep.diagonalTensorMap_comp, Category.comp_id, Category.id_comp]
  have hn := tateδ_naturality hS hT h n
  rw [h₁, h₃] at hn
  exact congrArg (fun v : tate (A ⊗ᵣ S.X₃) n ⟶ tate (C ⊗ᵣ T.X₁) (n + 1) => v x) hn

/-- Naturality of the actual coinduced tensor connecting map in both factors. -/
theorem tensorCoindShiftEquiv_naturality {A B C D : Rep.{u} ℤ G}
    (f : A ⟶ C) (g : B ⟶ D) (n : ℤ) (x : tate (A ⊗ᵣ Rep.coindShiftUp B) n) :
    (tateFunctor G (n + 1)).map (f ⊗ᵣₘ g) (tensorCoindShiftEquiv A B n x) =
      tensorCoindShiftEquiv C D n
        ((tateFunctor G n).map (f ⊗ᵣₘ Rep.coindShiftUpMap g) x) :=
  tateδ_tensor_naturality f (Rep.coindShiftSequenceMap g)
    (Rep.tensorLeft_coindShiftSequence_shortExact A B)
    (Rep.tensorLeft_coindShiftSequence_shortExact C D) n x

/-- Naturality of the actual induced tensor connecting map in both factors. -/
theorem tensorIndShiftEquiv_naturality {A B C D : Rep.{u} ℤ G}
    (f : A ⟶ C) (g : B ⟶ D) (n : ℤ) (x : tate (A ⊗ᵣ B) n) :
    (tateFunctor G (n + 1)).map (f ⊗ᵣₘ Rep.indShiftDownMap g) (tensorIndShiftEquiv A B n x) =
      tensorIndShiftEquiv C D n ((tateFunctor G n).map (f ⊗ᵣₘ g) x) :=
  tateδ_tensor_naturality f (Rep.indShiftSequenceMap g)
    (Rep.tensorLeft_indShiftSequence_shortExact A B)
    (Rep.tensorLeft_indShiftSequence_shortExact C D) n x

/-- The inverse connecting map has the same naturality square. -/
theorem tensorIndShiftEquiv_symm_naturality {A B C D : Rep.{u} ℤ G}
    (f : A ⟶ C) (g : B ⟶ D) (n : ℤ) (x : tate (A ⊗ᵣ Rep.indShiftDown B) (n + 1)) :
    (tateFunctor G n).map (f ⊗ᵣₘ g) ((tensorIndShiftEquiv A B n).symm x) =
      (tensorIndShiftEquiv C D n).symm
        ((tateFunctor G (n + 1)).map (f ⊗ᵣₘ Rep.indShiftDownMap g) x) := by
  apply (tensorIndShiftEquiv C D n).injective
  rw [LinearEquiv.apply_symm_apply, ← tensorIndShiftEquiv_naturality,
    LinearEquiv.apply_symm_apply]

end IntegralGroupCohomology.Universe
