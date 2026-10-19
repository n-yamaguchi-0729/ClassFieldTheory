/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.GaloisAction
import Nyll.AlgebraicCurves.Places.Restriction.AlgEquivSmulEqRestrictEq
import Nyll.ProCGroups.InducedFunctions

/-!
# Actual local orbit blocks of function-field ideles

Regrouping all places by their restriction gives a restricted product of the
actual finite products of completion units. The integral subgroups are the
products of the actual local integral-unit subgroups. Finite fibers make both
directions of regrouping preserve the restricted-product condition.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place RestrictedProduct

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- The product of the actual completion unit groups in a finite fiber. -/
abbrev FiberUnits (v : Place k K) := (u : v.fiberOver L) → u.1.adicCompletionˣ

/-- A fiber block is integral exactly when each of its completed components is integral. -/
def fiberIntegralUnits (v : Place k K) : Subgroup (FiberUnits (L := L) v) where
  carrier := {a | ∀ u, a u ∈ u.1.adicCompletionIntegers.units}
  one_mem' u := (u.1.adicCompletionIntegers.units).one_mem
  mul_mem' ha hb u := (u.1.adicCompletionIntegers.units).mul_mem (ha u) (hb u)
  inv_mem' ha u := (u.1.adicCompletionIntegers.units).inv_mem (ha u)

/-- Restrict an actual all-place idele to one finite fiber. -/
def fiberProjection (v : Place k K) : IdeleGroup k L →* FiberUnits (L := L) v where
  toFun a u := a u.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Extend a finite fiber block by one at every other place. -/
def fiberInclusion (v : Place k K) : FiberUnits (L := L) v →* IdeleGroup k L where
  toFun a := ∏ u : v.fiberOver L, placeIdele u.1 (a u)
  map_one' := by simp only [Pi.one_apply, map_one, Finset.prod_const_one]
  map_mul' a b := by
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

/-- Inclusion of a finite block recovers each of its actual local components. -/
theorem component_fiberInclusion (v : Place k K) (a : FiberUnits (L := L) v)
    (u : v.fiberOver L) : component u.1 (fiberInclusion (L := L) v a) = a u := by
  classical
  change component u.1 (∏ z : v.fiberOver L, placeIdele z.1 (a z)) = a u
  rw [map_prod, Finset.prod_eq_single u]
  · exact component_placeIdele_same u.1 (a u)
  · intro z _ hzu
    apply component_placeIdele_of_ne z.1 u.1 (a z)
    exact fun h => hzu (Subtype.ext h.symm)
  · exact fun h => (h (Finset.mem_univ u)).elim

/-- A finite block contributes the identity outside its own actual fiber. -/
theorem component_fiberInclusion_of_not_mem (v : Place k K)
    (a : FiberUnits (L := L) v) (u : Place k L) (hu : u ∉ v.fiberOver L) :
    component u (fiberInclusion (L := L) v a) = 1 := by
  classical
  change component u (∏ z : v.fiberOver L, placeIdele z.1 (a z)) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro z _
  apply component_placeIdele_of_ne z.1 u (a z)
  exact fun h => hu (h.symm ▸ z.2)

@[simp]
theorem fiberProjection_fiberInclusion (v : Place k K) (a : FiberUnits (L := L) v) :
    fiberProjection (L := L) v (fiberInclusion (L := L) v a) = a := by
  funext u
  exact component_fiberInclusion (L := L) v a u

/-- The restricted product of actual completed fiber blocks over all base places. -/
abbrev FiberRestrictedProduct :=
  Πʳ v : Place k K, [FiberUnits (L := L) v, fiberIntegralUnits (L := L) v]

private theorem fiberProjection_eventually_integral (a : IdeleGroup k L) :
    ∀ᶠ v : Place k K in Filter.cofinite,
      fiberProjection (L := L) v a ∈ fiberIntegralUnits (L := L) v := by
  have hbad : {u : Place k L | a u ∉ u.adicCompletionIntegers.units}.Finite :=
    Filter.eventually_cofinite.mp a.2
  have haway : ∀ᶠ v : Place k K in Filter.cofinite,
      v ∉ (fun u : Place k L => u.restrict K) ''
        {u : Place k L | a u ∉ u.adicCompletionIntegers.units} :=
    (hbad.image (fun u : Place k L => u.restrict K)).compl_mem_cofinite
  apply haway.mono
  intro v hv u
  by_contra hu
  exact hv ⟨u.1, hu, (Place.mem_fiberOver v).mp u.2⟩

section SeparableGrouping

variable [Algebra.IsSeparable K L]

private theorem ungroup_eventually_integral
    (a : FiberRestrictedProduct (k := k) (K := K) (L := L)) :
    ∀ᶠ u : Place k L in Filter.cofinite,
      a (u.restrict K) ⟨u, Place.restrict_mem_fiberOver u⟩ ∈
        u.adicCompletionIntegers.units := by
  have h := (tendsto_restrict_cofinite (k := k) (K := K) (L := L)).eventually a.2
  exact h.mono fun u hu => hu ⟨u, Place.restrict_mem_fiberOver u⟩

/-- All-place ideles are exactly the restricted product of their actual finite fiber blocks. -/
def groupByPlace : IdeleGroup k L ≃*
    FiberRestrictedProduct (k := k) (K := K) (L := L) where
  toFun a := ⟨fun v => fiberProjection (L := L) v a, fiberProjection_eventually_integral a⟩
  invFun a := ⟨fun u => a (u.restrict K) ⟨u, Place.restrict_mem_fiberOver u⟩,
    ungroup_eventually_integral a⟩
  left_inv a := by
    apply IdeleGroup.ext
    intro u
    rfl
  right_inv a := by
    apply RestrictedProduct.ext
    intro v
    funext ⟨u, hu⟩
    have h : u.restrict K = v := (Place.mem_fiberOver v).mp hu
    subst v
    rfl
  map_mul' _ _ := rfl

@[simp]
theorem groupByPlace_apply (a : IdeleGroup k L) (v : Place k K) (u : v.fiberOver L) :
    groupByPlace (k := k) (K := K) (L := L) a v u = a u.1 :=
  rfl

end SeparableGrouping

open ProCGroups.InducedFunctions

/-- An idele supplies an equivariant function on the Galois group by evaluating
all its actual conjugates at the chosen place. -/
def ideleToInduced (w : Place k L) :
    IdeleGroup k L →*
      InducedModule (B := w.adicCompletionˣ) (decompositionGroup (K := K) w) where
  toFun a := ⟨fun σ => component w (SemilinearAut.ofAlgAut (σ.restrictScalars k) • a), by
    intro h σ
    change component w ((SemilinearAut.ofAlgAut (h.1.restrictScalars k) *
      SemilinearAut.ofAlgAut (σ.restrictScalars k)) • a) = _
    rw [mul_smul, decomposition_smul_component]⟩
  map_one' := by
    apply Subtype.ext
    funext σ
    change component w (SemilinearAut.ofAlgAut (σ.restrictScalars k) •
      (1 : IdeleGroup k L)) = 1
    simp only [smul_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    funext σ
    change component w (SemilinearAut.ofAlgAut (σ.restrictScalars k) • (a * b)) =
      component w (SemilinearAut.ofAlgAut (σ.restrictScalars k) • a) *
        component w (SemilinearAut.ofAlgAut (σ.restrictScalars k) • b)
    simp only [smul_mul', map_mul]

/-- Right translation of the induced function is the actual global conjugation action. -/
theorem ideleToInduced_smul (w : Place k L) (σ : L ≃ₐ[K] L) (a : IdeleGroup k L) :
    ideleToInduced (K := K) w (SemilinearAut.ofAlgAut (σ.restrictScalars k) • a) =
      σ • ideleToInduced (K := K) w a := by
  apply Subtype.ext
  funext τ
  change component w (SemilinearAut.ofAlgAut (τ.restrictScalars k) •
      (SemilinearAut.ofAlgAut (σ.restrictScalars k) • a)) =
    component w ((SemilinearAut.ofAlgAut (τ.restrictScalars k) *
      SemilinearAut.ofAlgAut (σ.restrictScalars k)) • a)
  rw [mul_smul]

/-- The induced function depends only on the completed components in the actual fiber. -/
theorem ideleToInduced_fiberInclusion_projection (w : Place k L) (a : IdeleGroup k L) :
    ideleToInduced (K := K) w
        (fiberInclusion (L := L) (w.restrict K) (fiberProjection (L := L) (w.restrict K) a)) =
      ideleToInduced (K := K) w a := by
  apply Subtype.ext
  funext σ
  change (placeCompletionUnitsEquiv
      (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
        ((fiberInclusion (L := L) (w.restrict K) (fiberProjection (L := L) (w.restrict K) a))
          ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w)) =
    (placeCompletionUnitsEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ w).symm
      (a ((SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w))
  congr 1
  exact component_fiberInclusion (L := L) (w.restrict K) (fiberProjection (L := L) (w.restrict K) a)
    ⟨(SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w,
      (Place.mem_fiberOver (w.restrict K)).mpr (Place.restrict_ofAlgAut_smul σ.symm w)⟩

/-- The concrete comparison from a completed fiber to equivariant functions on the Galois group. -/
def fiberToInduced (w : Place k L) :
    FiberUnits (L := L) (w.restrict K) →*
      InducedModule (B := w.adicCompletionˣ) (decompositionGroup (K := K) w) :=
  (ideleToInduced (K := K) w).comp (fiberInclusion (L := L) (w.restrict K))

variable [IsGalois K L]

/-- A conjugate component at the chosen place detects every component in its actual fiber. -/
theorem fiberToInduced_injective (w : Place k L) :
    Function.Injective (fiberToInduced (K := K) w) := by
  intro a b hab
  funext u
  obtain ⟨τ, hτ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq w u.1
    ((Place.mem_fiberOver (w.restrict K)).mp u.2)
  have h := congrArg
    (fun f : InducedModule (B := w.adicCompletionˣ) (decompositionGroup (K := K) w) =>
      f.1 τ⁻¹) hab
  change (placeCompletionUnitsEquiv (SemilinearAut.ofAlgAut (τ.restrictScalars k)) w).symm
      (fiberInclusion (L := L) (w.restrict K) a
        (SemilinearAut.ofAlgAut (τ.restrictScalars k) • w)) =
    (placeCompletionUnitsEquiv (SemilinearAut.ofAlgAut (τ.restrictScalars k)) w).symm
      (fiberInclusion (L := L) (w.restrict K) b
        (SemilinearAut.ofAlgAut (τ.restrictScalars k) • w)) at h
  have h' := (placeCompletionUnitsEquiv
    (SemilinearAut.ofAlgAut (τ.restrictScalars k)) w).symm.injective h
  rw [hτ] at h'
  change component u.1 (fiberInclusion (L := L) (w.restrict K) a) =
    component u.1 (fiberInclusion (L := L) (w.restrict K) b) at h'
  rwa [component_fiberInclusion, component_fiberInclusion] at h'

/-- An equivariant function is realized by an actual idele supported on the finite place fiber. -/
theorem ideleToInduced_surjective (w : Place k L) :
    Function.Surjective (ideleToInduced (K := K) w) := by
  classical
  let S : (L ≃ₐ[K] L) →* SemilinearAut k L :=
    SemilinearAut.ofAlgAut.comp (AlgEquiv.restrictScalarsHom k)
  have hex (u : (w.restrict K).fiberOver L) :
      ∃ σ : L ≃ₐ[K] L, (S σ)⁻¹ • w = u.1 := by
    obtain ⟨τ, hτ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq w u.1
      ((Place.mem_fiberOver (w.restrict K)).mp u.2)
    exact ⟨τ⁻¹, by simpa only [map_inv, inv_inv] using (show S τ • w = u.1 from hτ)⟩
  choose r hr using hex
  intro f
  let a : IdeleGroup k L :=
    ∏ u : (w.restrict K).fiberOver L, (S (r u))⁻¹ • placeIdele w (f.1 (r u))
  refine ⟨a, ?_⟩
  apply Subtype.ext
  funext σ
  let q : (w.restrict K).fiberOver L :=
    ⟨(S σ)⁻¹ • w, (Place.mem_fiberOver (w.restrict K)).mpr
      (Place.restrict_ofAlgAut_smul σ.symm w)⟩
  change component w (semilinearHom (S σ)
    (∏ u : (w.restrict K).fiberOver L, (S (r u))⁻¹ • placeIdele w (f.1 (r u)))) = f.1 σ
  rw [map_prod, map_prod, Finset.prod_eq_single q]
  · let δ : decompositionGroup (K := K) w := ⟨σ * (r q)⁻¹, by
      change (S σ * (S (r q))⁻¹) • w = w
      rw [mul_smul, hr q]
      exact smul_inv_smul (S σ) w⟩
    change component w (S σ • ((S (r q))⁻¹ • placeIdele w (f.1 (r q)))) = f.1 σ
    rw [← mul_smul]
    change component w (SemilinearAut.ofAlgAut (δ.1.restrictScalars k) •
      placeIdele w (f.1 (r q))) = f.1 σ
    rw [decomposition_smul_component, component_placeIdele_same]
    have hf := f.2 δ (r q)
    change f.1 ((σ * (r q)⁻¹) * r q) = δ • f.1 (r q) at hf
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hf.symm
  · intro u _ huq
    have hne : (S σ * (S (r u))⁻¹)⁻¹ • w ≠ w := by
      intro hh
      have hh' : S σ • ((S (r u))⁻¹ • w) = w :=
        by simpa only [mul_smul] using ((inv_smul_eq_iff).mp hh).symm
      have heq : u.1 = q.1 := (hr u).symm.trans
        ((smul_eq_iff_eq_inv_smul (S σ)).mp hh')
      exact huq (Subtype.ext heq)
    change component w (S σ • ((S (r u))⁻¹ • placeIdele w (f.1 (r u)))) = 1
    rw [← mul_smul]
    change (placeCompletionUnitsEquiv (S σ * (S (r u))⁻¹)⁻¹ w).symm
      (component ((S σ * (S (r u))⁻¹)⁻¹ • w) (placeIdele w (f.1 (r u)))) = 1
    rw [component_placeIdele_of_ne w _ _ hne, map_one]
  · exact fun h => (h (Finset.mem_univ q)).elim

/-- The comparison is surjective already on the actual completed fiber. -/
theorem fiberToInduced_surjective (w : Place k L) :
    Function.Surjective (fiberToInduced (K := K) w) := by
  intro f
  obtain ⟨a, ha⟩ := ideleToInduced_surjective (K := K) w f
  refine ⟨fiberProjection (L := L) (w.restrict K) a, ?_⟩
  exact (ideleToInduced_fiberInclusion_projection (K := K) w a).trans ha

/-- The actual product of completion unit groups over a place is its induced local module. -/
def fiberInducedEquiv (w : Place k L) :
    FiberUnits (L := L) (w.restrict K) ≃*
      InducedModule (B := w.adicCompletionˣ) (decompositionGroup (K := K) w) :=
  MulEquiv.ofBijective (fiberToInduced (K := K) w)
    ⟨fiberToInduced_injective w, fiberToInduced_surjective w⟩

end FunctionField.IdeleGroup
