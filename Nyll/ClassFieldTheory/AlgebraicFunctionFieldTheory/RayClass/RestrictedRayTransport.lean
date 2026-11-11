/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayEmbedding
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Finite support and transport of the actual restricted ray product

The restricting subgroups of the local ray product are the identity groups.
Consequently every family is a finite product of its original one-place
inclusions. This proves that compatibility with every original local Artin
map determines compatibility with the entire global Artin map.

Transport of the actual local factors is defined coordinatewise, along the
given place equivalence. Its inverse and finite-support condition are proved
using the same coordinate equivalences. No global reciprocity square or
principal-kernel correspondence is assumed in this construction.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve Filter
open scoped BigOperators

namespace FunctionField.RayClass

section FiniteSupport

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- An actual restricted ray family has only finitely many nonidentity coordinates. -/
theorem restrictedRay_finite_support (m : Modulus k K) (a : RayRestrictedProduct m) :
    Set.Finite {v : Place k K | a v ≠ 1} := by
  have h := Filter.eventually_cofinite.mp a.2
  apply h.subset
  intro v hv
  change a v ∉ (⊥ : Subgroup (RayLocalFactor m v))
  exact fun hmem => hv (Subgroup.mem_bot.mp hmem)

/-- The original local inclusions reconstruct a restricted family from any
finite set containing its nonidentity coordinates. -/
theorem restrictedRay_eq_prod_local (m : Modulus k K) (a : RayRestrictedProduct m)
    (s : Finset (Place k K)) (hs : ∀ v, v ∉ s → a v = 1) :
    (∏ v ∈ s, localRayToRestrictedProduct m v (a v)) = a := by
  classical
  apply RestrictedProduct.ext
  intro w
  let ev : RayRestrictedProduct m →* RayLocalFactor m w :=
    RestrictedProduct.evalMonoidHom (fun v : Place k K => RayLocalFactor m v) w
  calc
    (∏ v ∈ s, localRayToRestrictedProduct m v (a v)) w =
        ∏ v ∈ s, localRayToRestrictedProduct m v (a v) w :=
      map_prod ev (fun v => localRayToRestrictedProduct m v (a v)) s
    _ = localRayToRestrictedProduct m w (a w) w :=
      Finset.prod_eq_single w
        (fun v _ hv => localRayToRestrictedProduct_of_ne m v w (a v) hv.symm)
        (fun hw => by
          rw [hs w hw, localRayToRestrictedProduct_same])
    _ = a w := localRayToRestrictedProduct_same m w (a w)

/-- Multiplicative induction on original one-place ray factors. -/
theorem restrictedRay_induction (m : Modulus k K)
    {P : RayRestrictedProduct m → Prop}
    (hone : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hlocal : ∀ v x, P (localRayToRestrictedProduct m v x))
    (a : RayRestrictedProduct m) : P a := by
  classical
  let s := (restrictedRay_finite_support m a).toFinset
  have hs : ∀ v, v ∉ s → a v = 1 := by
    intro v hv
    by_contra hne
    exact hv ((restrictedRay_finite_support m a).mem_toFinset.mpr hne)
  have hp : ∀ t : Finset (Place k K),
      P (∏ v ∈ t, localRayToRestrictedProduct m v (a v)) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      simpa only [Finset.prod_empty] using hone
    | @insert v t hv ih =>
      rw [Finset.prod_insert hv]
      exact hmul _ _ (hlocal v (a v)) ih
  rw [← restrictedRay_eq_prod_local m a s hs]
  exact hp s

/-- Homomorphisms out of the actual ray product are determined by their
values on the original one-place inclusions. -/
theorem restrictedRay_hom_ext (m : Modulus k K)
    {G : Type*} [Monoid G] (f g : RayRestrictedProduct m →* G)
    (hlocal : ∀ v x,
      f (localRayToRestrictedProduct m v x) = g (localRayToRestrictedProduct m v x)) :
    f = g := by
  apply MonoidHom.ext
  intro a
  apply restrictedRay_induction m
    (P := fun q => f q = g q) _ _ hlocal a
  · rw [map_one, map_one]
  · intro x y hx hy
    rw [map_mul, map_mul, hx, hy]

end FiniteSupport

section Transport

variable {k₁ K₁ k₂ K₂ : Type*}
    [Field k₁] [Field K₁] [Algebra k₁ K₁]
    [Field k₂] [Field K₂] [Algebra k₂ K₂]
    {m₁ : Modulus k₁ K₁} {m₂ : Modulus k₂ K₂}

/-- Coordinatewise transport of the original restricted product of local
ray factors, including its actual finite-support condition. -/
def restrictedRayEquiv (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (φ : ∀ v, RayLocalFactor m₁ v ≃* RayLocalFactor m₂ (e v)) :
    RayRestrictedProduct m₁ ≃* RayRestrictedProduct m₂ where
  toFun a := ⟨e.piCongr (fun v => (φ v).toEquiv) a.1, by
    filter_upwards [e.symm.injective.tendsto_cofinite.eventually a.2] with w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    have hv : a v = 1 := by
      have hv' : a (e.symm (e v)) = 1 := Subgroup.mem_bot.mp hw
      exact Eq.mp (congrArg (fun w : Place k₁ K₁ => a.1 w = 1)
        (e.symm_apply_apply v)) hv'
    change (e.piCongr (fun v => (φ v).toEquiv) a.1) (e v) = 1
    exact (Equiv.piCongr_apply_apply e (fun v => (φ v).toEquiv) a.1 v).trans
      ((congrArg (φ v) hv).trans (map_one (φ v)))⟩
  invFun b := ⟨fun v => (φ v).symm (b (e v)), by
    filter_upwards [e.injective.tendsto_cofinite.eventually b.2] with v hv
    change (φ v).symm (b (e v)) = 1
    have hv' : b (e v) = 1 := Subgroup.mem_bot.mp hv
    rw [hv', map_one]⟩
  left_inv a := by
    apply RestrictedProduct.ext
    intro v
    change (φ v).symm ((e.piCongr (fun v => (φ v).toEquiv) a.1) (e v)) = a v
    exact (congrArg (φ v).symm
      (Equiv.piCongr_apply_apply e (fun v => (φ v).toEquiv) a.1 v)).trans
        ((φ v).symm_apply_apply (a v))
  right_inv b := by
    apply RestrictedProduct.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    change (e.piCongr (fun v => (φ v).toEquiv)
      (fun v => (φ v).symm (b (e v)))) (e v) = b (e v)
    exact (Equiv.piCongr_apply_apply e (fun v => (φ v).toEquiv)
      (fun v => (φ v).symm (b (e v))) v).trans
        ((φ v).apply_symm_apply (b (e v)))
  map_mul' a b := by
    apply RestrictedProduct.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    change (e.piCongr (fun v => (φ v).toEquiv) (a * b).1) (e v) =
      (e.piCongr (fun v => (φ v).toEquiv) a.1) (e v) *
        (e.piCongr (fun v => (φ v).toEquiv) b.1) (e v)
    rw [Equiv.piCongr_apply_apply, Equiv.piCongr_apply_apply,
      Equiv.piCongr_apply_apply]
    exact map_mul (φ v) (a v) (b v)

/-- Transport at a matched place is the specified original local map. -/
theorem restrictedRayEquiv_apply (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (φ : ∀ v, RayLocalFactor m₁ v ≃* RayLocalFactor m₂ (e v))
    (a : RayRestrictedProduct m₁) (v : Place k₁ K₁) :
    restrictedRayEquiv e φ a (e v) = φ v (a v) :=
  Equiv.piCongr_apply_apply e (fun v => (φ v).toEquiv) a.1 v

/-- The inverse reads the same matched coordinate, with the inverse local map. -/
theorem restrictedRayEquiv_symm_apply (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (φ : ∀ v, RayLocalFactor m₁ v ≃* RayLocalFactor m₂ (e v))
    (b : RayRestrictedProduct m₂) (v : Place k₁ K₁) :
    (restrictedRayEquiv e φ).symm b v = (φ v).symm (b (e v)) := rfl

/-- Coordinate transport preserves the original one-place inclusions. -/
theorem restrictedRayEquiv_local (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (φ : ∀ v, RayLocalFactor m₁ v ≃* RayLocalFactor m₂ (e v))
    (v : Place k₁ K₁) (x : RayLocalFactor m₁ v) :
    restrictedRayEquiv e φ (localRayToRestrictedProduct m₁ v x) =
      localRayToRestrictedProduct m₂ (e v) (φ v x) := by
  apply RestrictedProduct.ext
  intro w
  obtain ⟨u, rfl⟩ := e.surjective w
  refine (restrictedRayEquiv_apply e φ (localRayToRestrictedProduct m₁ v x) u).trans ?_
  by_cases hu : u = v
  · subst u
    exact (congrArg (φ v) (localRayToRestrictedProduct_same m₁ v x)).trans
      (localRayToRestrictedProduct_same m₂ (e v) (φ v x)).symm
  · have heu : e u ≠ e v := fun h => hu (e.injective h)
    exact (congrArg (φ u) (localRayToRestrictedProduct_of_ne m₁ v u x hu)).trans
      ((map_one (φ u)).trans
        (localRayToRestrictedProduct_of_ne m₂ (e v) (e u) (φ v x) heu).symm)

/-- The matched local coordinate is trivial before transport exactly when
it is trivial afterwards. In particular, no principal-unit condition is lost. -/
theorem restrictedRayEquiv_apply_eq_one_iff (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (φ : ∀ v, RayLocalFactor m₁ v ≃* RayLocalFactor m₂ (e v))
    (a : RayRestrictedProduct m₁) (v : Place k₁ K₁) :
    restrictedRayEquiv e φ a (e v) = 1 ↔ a v = 1 := by
  constructor
  · intro h
    exact (φ v).injective
      ((restrictedRayEquiv_apply e φ a v).symm.trans (h.trans (map_one (φ v)).symm))
  · intro h
    exact (restrictedRayEquiv_apply e φ a v).trans
      ((congrArg (φ v) h).trans (map_one (φ v)))

end Transport

end FunctionField.RayClass
