/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousCrossedHom
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Maps of actual continuous degree-two cohomology in independent universes -/

public section

noncomputable section

open CategoryTheory TopRep
open scoped BigOperators

namespace ContinuousCohomology

universe u v w

variable {G : Type u} {H : Type v} {J : Type w}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J] [LocallyCompactSpace J]
    {X : TopRep.{u} ℤ G} {Y : TopRep.{v} ℤ H} {Z : TopRep.{w} ℤ J}

section Map

variable (r : H →ₜ* G) (f : X →+ Y) (hf : Continuous f)
    (h : ∀ (σ : H) (x : X), f (X.ρ (r σ) x) = Y.ρ σ (f x))

private theorem tuple_cochain_ext (n : ℕ) {a b : (homogeneousCochains Y).X n}
    (hab : ∀ p : Fin (n + 1) → H,
      resolutionTupleHomeomorph H Y (n + 1) a.val p =
        resolutionTupleHomeomorph H Y (n + 1) b.val p) :
    a = b :=
  Subtype.ext ((resolutionTupleHomeomorph H Y (n + 1)).injective (ContinuousMap.ext hab))

private def cochainTupleMap (n : ℕ) (a : (homogeneousCochains X).X n) : C(Fin (n + 1) → H, Y) :=
  ⟨fun p => f (resolutionTupleHomeomorph G X (n + 1) a.val (fun i => r (p i))),
    hf.comp ((resolutionTupleHomeomorph G X (n + 1) a.val).continuous.comp
      (continuous_pi fun i => r.continuous.comp (continuous_apply i)))⟩

omit [IsTopologicalGroup H] [LocallyCompactSpace H] in
include h in
private theorem cochainTupleMap_equivariant (n : ℕ) (a : (homogeneousCochains X).X n)
    (σ : H) (p : Fin (n + 1) → H) : cochainTupleMap r f hf n a (fun i => σ * p i) =
      Y.ρ σ (cochainTupleMap r f hf n a p) := by
  change f (resolutionTupleHomeomorph G X (n + 1) a.val (fun i => r (σ * p i))) = _
  simp only [map_mul, homogeneousCochain_tuple_equivariant G X n a, h, cochainTupleMap]
  rfl

private def universeCochainMap (n : ℕ) :
    (homogeneousCochains X).X n →+ (homogeneousCochains Y).X n where
  toFun a := homogeneousCochainOfTuple H Y n (cochainTupleMap r f hf n a)
    (cochainTupleMap_equivariant r f hf h n a)
  map_zero' := by
    apply tuple_cochain_ext n
    intro p
    rw [homogeneousCochainOfTuple_apply]
    rw [show resolutionTupleHomeomorph H Y (n + 1) (0 : (homogeneousCochains Y).X n).val = 0 from
      map_zero (resolutionTupleContinuousLinearEquiv H Y (n + 1))]
    change f (resolutionTupleHomeomorph G X (n + 1) (0 : (homogeneousCochains X).X n).val
      (fun i => r (p i))) = 0
    rw [show resolutionTupleHomeomorph G X (n + 1) (0 : (homogeneousCochains X).X n).val = 0
      from map_zero (resolutionTupleContinuousLinearEquiv G X (n + 1)),
      ContinuousMap.zero_apply, map_zero]
  map_add' a b := by
    apply tuple_cochain_ext n
    intro p
    rw [homogeneousCochainOfTuple_apply]
    change cochainTupleMap r f hf n (a + b) p =
      resolutionTupleHomeomorph H Y (n + 1)
        ((homogeneousCochainOfTuple H Y n (cochainTupleMap r f hf n a)
        (cochainTupleMap_equivariant r f hf h n a)).val +
        (homogeneousCochainOfTuple H Y n (cochainTupleMap r f hf n b)
          (cochainTupleMap_equivariant r f hf h n b)).val) p
    rw [resolutionTupleHomeomorph_add, ContinuousMap.add_apply,
      homogeneousCochainOfTuple_apply, homogeneousCochainOfTuple_apply]
    change f (resolutionTupleHomeomorph G X (n + 1) (a.val + b.val) (fun i => r (p i))) = _
    rw [resolutionTupleHomeomorph_add, ContinuousMap.add_apply, map_add]
    rfl

private theorem universeCochainMap_apply (n : ℕ) (a : (homogeneousCochains X).X n)
    (p : Fin (n + 1) → H) :
    resolutionTupleHomeomorph H Y (n + 1) (universeCochainMap r f hf h n a).val p =
      f (resolutionTupleHomeomorph G X (n + 1) a.val (fun i => r (p i))) :=
  congrArg (fun q : C(Fin (n + 1) → H, Y) => q p)
    (homogeneousCochainOfTuple_apply H Y n (cochainTupleMap r f hf n a)
      (cochainTupleMap_equivariant r f hf h n a))

private theorem universeCochainMap_d (n : ℕ) (a : (homogeneousCochains X).X n) :
    universeCochainMap r f hf h (n + 1) (((homogeneousCochains X).d n (n + 1)).hom a) =
      ((homogeneousCochains Y).d n (n + 1)).hom (universeCochainMap r f hf h n a) := by
  apply tuple_cochain_ext (n + 1)
  intro p
  rw [universeCochainMap_apply]
  rw [show (((homogeneousCochains X).d n (n + 1)).hom a).val = (d X (n + 1)).hom a.val from
      homogeneousCochains.d_apply X n a,
    show (((homogeneousCochains Y).d n (n + 1)).hom (universeCochainMap r f hf h n a)).val =
      (d Y (n + 1)).hom (universeCochainMap r f hf h n a).val
        from homogeneousCochains.d_apply Y n _,
    resolutionTupleHomeomorph_d, resolutionTupleHomeomorph_d, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, universeCochainMap_apply]

omit [LocallyCompactSpace H] in
private theorem cycleInclusion_injective (n : ℕ) :
    Function.Injective ((homogeneousCochains Y).iCycles n) := by
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  exact (ModuleCat.mono_iff_injective (F.map ((homogeneousCochains Y).iCycles n))).mp inferInstance

omit [LocallyCompactSpace G] in
private theorem cycle_d_eq_zero (n : ℕ) (z : cocycles X n) :
    ((homogeneousCochains X).d n (n + 1)).hom ((homogeneousCochains X).iCycles n z) = 0 := by
  let C := homogeneousCochains X
  have h := ConcreteCategory.congr_hom (C.iCycles_d n (n + 1)) z
  change ((C.d n (n + 1)).hom (C.iCycles n z)) = 0 at h
  exact h

private theorem universeCocycle_closed (z : cocycles X 2) :
    ((homogeneousCochains Y).d 2 3).hom
      (universeCochainMap r f hf h 2 ((homogeneousCochains X).iCycles 2 z)) = 0 := by
  rw [← universeCochainMap_d r f hf h 2, cycle_d_eq_zero 2 z, map_zero]

private def universeCocycle (z : cocycles X 2) : cocycles Y 2 := by
  let a := universeCochainMap r f hf h 2 ((homogeneousCochains X).iCycles 2 z)
  let C := homogeneousCochains Y
  let hl := CrossedHom.scalarLine_comp_eq_zero a (C.d 2 3) (universeCocycle_closed r f hf h z)
  exact C.liftCycles (CrossedHom.scalarLine a) 3 (CochainComplex.next ℕ 2) hl (ULift.up (1 : ℤ))

private theorem universeCocycle_iCycles (z : cocycles X 2) :
    (homogeneousCochains Y).iCycles 2 (universeCocycle r f hf h z) =
      universeCochainMap r f hf h 2 ((homogeneousCochains X).iCycles 2 z) := by
  unfold universeCocycle
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  exact CrossedHom.scalarLine_one
    (universeCochainMap r f hf h 2 ((homogeneousCochains X).iCycles 2 z))

private def universeCocycleMap : cocycles X 2 →+ cocycles Y 2 where
  toFun := universeCocycle r f hf h
  map_zero' := by
    apply cycleInclusion_injective 2
    rw [universeCocycle_iCycles, map_zero, map_zero, map_zero]
  map_add' x y := by
    apply cycleInclusion_injective 2
    rw [universeCocycle_iCycles, map_add, map_add, map_add,
      universeCocycle_iCycles, universeCocycle_iCycles]

private theorem universeCocycle_boundary (z : cocycles X 2) (hz : π X 2 z = 0) :
    π Y 2 (universeCocycleMap r f hf h z) = 0 := by
  obtain ⟨a, ha⟩ := exists_boundary_of_π_eq_zero X 1 z hz
  let C := homogeneousCochains Y
  have he : C.toCycles 1 2 (universeCochainMap r f hf h 1 a) = universeCocycleMap r f hf h z := by
    apply cycleInclusion_injective 2
    rw [← ConcreteCategory.comp_apply, C.toCycles_i]
    change (C.d 1 2).hom (universeCochainMap r f hf h 1 a) =
      C.iCycles 2 (universeCocycle r f hf h z)
    rw [universeCocycle_iCycles, ← universeCochainMap_d, ha]
  rw [← he]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) _

/-- Actual degree-two cohomology pulls back the group arguments and applies
the given equivariant continuous map to the coefficients across universes. -/
def universeMapH2 : continuousCohomology 2 X →+ continuousCohomology 2 Y := by
  let p := (π X 2).hom.toLinearMap.toAddMonoidHom
  let q := (π Y 2).hom.toLinearMap.toAddMonoidHom
  let e := QuotientAddGroup.quotientKerEquivOfSurjective p (π_surjective X 2)
  exact (QuotientAddGroup.lift p.ker (q.comp (universeCocycleMap r f hf h))
    (fun z hz => universeCocycle_boundary r f hf h z hz)).comp e.symm.toAddMonoidHom

private theorem universeMapH2_π (z : cocycles X 2) :
    universeMapH2 r f hf h (π X 2 z) = π Y 2 (universeCocycle r f hf h z) := by
  let p := (π X 2).hom.toLinearMap.toAddMonoidHom
  let q := (π Y 2).hom.toLinearMap.toAddMonoidHom.comp (universeCocycleMap r f hf h)
  let e := QuotientAddGroup.quotientKerEquivOfSurjective p (π_surjective X 2)
  let hq (a : cocycles X 2) (ha : a ∈ p.ker) : q a = 0 := universeCocycle_boundary r f hf h a ha
  have he : e.symm (π X 2 z) = QuotientAddGroup.mk z := by
    apply e.injective
    exact e.apply_symm_apply _
  change QuotientAddGroup.lift p.ker q hq (e.symm (π X 2 z)) = _
  exact (congrArg (QuotientAddGroup.lift p.ker q hq) he).trans rfl

end Map

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [TopologicalSpace J] [IsTopologicalGroup J] [LocallyCompactSpace J] in
/-- Continuity of the composed coefficient map with its bundled additive type. -/
theorem universeMapH2_comp_continuous (f : X →+ Y) (g : Y →+ Z)
    (hf : Continuous f) (hg : Continuous g) : Continuous (g.comp f) := by
  change Continuous (g ∘ f)
  exact hg.comp hf

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [IsTopologicalGroup J] [LocallyCompactSpace J] in
/-- Equivariance of the composed group and coefficient maps in their bundled types. -/
theorem universeMapH2_comp_equivariant (r : H →ₜ* G) (f : X →+ Y)
    (h : ∀ σ x, f (X.ρ (r σ) x) = Y.ρ σ (f x)) (s : J →ₜ* H) (g : Y →+ Z)
    (k : ∀ σ y, g (Y.ρ (s σ) y) = Z.ρ σ (g y)) (σ : J) (x : X) :
    (g.comp f) (X.ρ ((r.comp s) σ) x) = Z.ρ σ ((g.comp f) x) := by
  change g (f (X.ρ (r (s σ)) x)) = Z.ρ σ (g (f x))
  exact (congrArg g (h (s σ) x)).trans (k σ (f x))

/-- The original representatives verify compatibility with composition across universes. -/
theorem universeMapH2_comp
    (r : H →ₜ* G) (f : X →+ Y) (hf : Continuous f)
    (h : ∀ σ x, f (X.ρ (r σ) x) = Y.ρ σ (f x))
    (s : J →ₜ* H) (g : Y →+ Z) (hg : Continuous g)
    (k : ∀ σ y, g (Y.ρ (s σ) y) = Z.ρ σ (g y)) :
    (universeMapH2 s g hg k).comp (universeMapH2 r f hf h) =
      universeMapH2 (r.comp s) (g.comp f) (universeMapH2_comp_continuous f g hf hg)
        (universeMapH2_comp_equivariant r f h s g k) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := π_surjective X 2 x
  rw [AddMonoidHom.comp_apply, universeMapH2_π, universeMapH2_π, universeMapH2_π]
  apply congrArg (π Z 2)
  apply cycleInclusion_injective 2
  rw [universeCocycle_iCycles, universeCocycle_iCycles, universeCocycle_iCycles]
  apply tuple_cochain_ext 2
  intro p
  let a := (homogeneousCochains X).iCycles 2 z
  let t (i : Fin 3) : H := s (p i)
  let t' (i : Fin 3) : G := r (t i)
  have hOuter := universeCochainMap_apply s g hg k 2 (universeCochainMap r f hf h 2 a) p
  have hInner := universeCochainMap_apply r f hf h 2 a t
  have hComposite := universeCochainMap_apply (r.comp s) (g.comp f)
    (universeMapH2_comp_continuous f g hf hg) (universeMapH2_comp_equivariant r f h s g k) 2 a p
  change _ = g (f (resolutionTupleHomeomorph G X 3 a.val t')) at hComposite
  exact hOuter.trans ((congrArg g hInner).trans hComposite.symm)

/-- In a common universe this comparison is Mathlib's original continuous cohomology map. -/
theorem universeMapH2_eq_map {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] {Y : TopRep.{u} ℤ H}
    (r : H →ₜ* G) (φ : TopRep.res r.toMonoidHom X ⟶ Y) (f : X →+ Y) (hf : Continuous f)
    (h : ∀ σ x, f (X.ρ (r σ) x) = Y.ρ σ (f x)) (hφ : ∀ x : X, f x = φ x)
    (x : continuousCohomology 2 X) : universeMapH2 r f hf h x =
      ContinuousCohomology.map r φ 2 x := by
  obtain ⟨z, rfl⟩ := π_surjective X 2 x
  have hclass : (ContinuousCohomology.map r φ 2) (π X 2 z) = π Y 2 (cocyclesMap r φ 2 z) :=
    ConcreteCategory.congr_hom (π_map r φ 2) z
  rw [universeMapH2_π, hclass]
  apply congrArg (π Y 2)
  apply cycleInclusion_injective 2
  rw [universeCocycle_iCycles, cochainOfMappedCocycle]
  apply tuple_cochain_ext 2
  intro p
  rw [universeCochainMap_apply, resolutionTupleHomeomorph_cochainsMap, hφ]

end ContinuousCohomology
