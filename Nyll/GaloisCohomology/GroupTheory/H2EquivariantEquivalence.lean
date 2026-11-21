/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Transport of actual degree-two classes in independent universes -/

@[expose] public section

open CategoryTheory

noncomputable section

namespace groupCohomology

universe u v

variable {R G : Type u} {S H : Type v} [CommRing R] [CommRing S] [Group G] [Group H]
  {A : Rep R G} {B : Rep S H} (e : G ≃* H) (f : A ≃+ B)
  (he : ∀ g a, f (A.ρ g a) = B.ρ (e g) (f a))

include he in
/-- The inverse of an equivariant additive equivalence is equivariant for
the inverse equivalence of acting groups. -/
theorem equivariantAddEquiv_symm (h : H) (b : B) :
    f.symm (B.ρ h b) = A.ρ (e.symm h) (f.symm b) := by
  apply f.injective
  rw [f.apply_symm_apply, he, e.apply_symm_apply, f.apply_symm_apply]

/-- Reindex a degree-two cocycle and transport its coefficient equivariantly. -/
def reindexTwoCocycle (z : cocycles₂ A) : cocycles₂ B := by
  refine ⟨fun xy => f (z (e.symm xy.1, e.symm xy.2)), ?_⟩
  rw [mem_cocycles₂_iff]
  intro g h j
  have hρ := he (e.symm g) (z (e.symm h, e.symm j))
  rw [e.apply_symm_apply] at hρ
  change f (z (e.symm (g * h), e.symm j)) + f (z (e.symm g, e.symm h)) =
    B.ρ g (f (z (e.symm h, e.symm j))) + f (z (e.symm g, e.symm (h * j)))
  simp only [map_mul, ← hρ, ← map_add]
  exact congrArg f ((mem_cocycles₂_iff (z : G × G → A)).1 z.property
    (e.symm g) (e.symm h) (e.symm j))

/-- The equivariant reindexing of two-cocycles is an additive equivalence. -/
def reindexTwoCocycleEquiv : cocycles₂ A ≃+ cocycles₂ B where
  toFun := reindexTwoCocycle e f he
  invFun := reindexTwoCocycle e.symm f.symm (equivariantAddEquiv_symm e f he)
  left_inv z := by
    apply cocycles₂_ext
    intro g h
    change f.symm (f (z (e.symm (e g), e.symm (e h)))) = z (g, h)
    rw [e.symm_apply_apply, e.symm_apply_apply, f.symm_apply_apply]
  right_inv z := by
    apply cocycles₂_ext
    intro g h
    change f (f.symm (z (e (e.symm g), e (e.symm h)))) = z (g, h)
    rw [e.apply_symm_apply, e.apply_symm_apply, f.apply_symm_apply]
  map_add' x y := by
    apply cocycles₂_ext
    intro g h
    exact map_add f _ _

/-- Equivariant reindexing sends an actual two-coboundary to a two-coboundary. -/
theorem H2π_reindexTwoCocycle_eq_zero (z : cocycles₂ A) (hz : H2π A z = 0) :
    H2π B (reindexTwoCocycle e f he z) = 0 := by
  obtain ⟨b, hb⟩ := (H2π_eq_zero_iff z).1 hz
  apply (H2π_eq_zero_iff _).2
  refine ⟨fun h => f (b (e.symm h)), ?_⟩
  funext xy
  obtain ⟨g, h⟩ := xy
  have hh := congrArg f (congrFun hb (e.symm g, e.symm h))
  change f (A.ρ (e.symm g) (b (e.symm h)) - b (e.symm g * e.symm h) + b (e.symm g)) =
    f (z (e.symm g, e.symm h)) at hh
  rw [map_add, map_sub, he, e.apply_symm_apply] at hh
  change B.ρ g (f (b (e.symm h))) - f (b (e.symm (g * h))) + f (b (e.symm g)) =
    f (z (e.symm g, e.symm h))
  rw [map_mul]
  exact hh

include e f he in
/-- An equivariant equivalence of the coefficients and an equivalence of
the acting groups identify ordinary H² across universe levels. -/
def equivariantH2AddEquiv : H2 A ≃+ H2 B := by
  let p := (H2π A).hom.toAddMonoidHom
  let q := (H2π B).hom.toAddMonoidHom
  let c := reindexTwoCocycleEquiv e f he
  have hk : p.ker.map c.toAddMonoidHom = q.ker := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact H2π_reindexTwoCocycle_eq_zero e f he y hy
    · intro hz
      exact ⟨c.symm z, H2π_reindexTwoCocycle_eq_zero e.symm f.symm
        (equivariantAddEquiv_symm e f he) z hz, c.apply_symm_apply z⟩
  let p' := QuotientAddGroup.quotientKerEquivOfSurjective p
    ((ModuleCat.epi_iff_surjective (H2π A)).1 inferInstance)
  let q' := QuotientAddGroup.quotientKerEquivOfSurjective q
    ((ModuleCat.epi_iff_surjective (H2π B)).1 inferInstance)
  exact p'.symm.trans ((QuotientAddGroup.congr p.ker q.ker c hk).trans q')

/-- On the original representative, the comparison transports its two
arguments and its coefficient. -/
theorem equivariantH2AddEquiv_H2π (z : cocycles₂ A) :
    equivariantH2AddEquiv e f he (H2π A z) = H2π B (reindexTwoCocycle e f he z) := by
  unfold equivariantH2AddEquiv
  dsimp only [AddEquiv.trans_apply]
  have hp : (QuotientAddGroup.quotientKerEquivOfSurjective
      (H2π A).hom.toAddMonoidHom ((ModuleCat.epi_iff_surjective (H2π A)).1 inferInstance)).symm
      (H2π A z) = QuotientAddGroup.mk z := by
    apply (QuotientAddGroup.quotientKerEquivOfSurjective
      (H2π A).hom.toAddMonoidHom ((ModuleCat.epi_iff_surjective (H2π A)).1 inferInstance)).injective
    rw [AddEquiv.apply_symm_apply]
    rfl
  rw [hp]
  rfl

/-- The actual degree-two equivalence commutes with pullback along a commuting
square of group homomorphisms and coefficient maps, even across universes. -/
theorem equivariantH2AddEquiv_map {G' : Type u} {H' : Type v} [Group G'] [Group H']
    {A' : Rep R G'} {B' : Rep S H'} (e' : G' ≃* H') (f' : A' ≃+ B')
    (he' : ∀ g a, f' (A'.ρ g a) = B'.ρ (e' g) (f' a))
    (a : G' →* G) (b : H' →* H) (φ : Rep.res a A ⟶ A') (ψ : Rep.res b B ⟶ B')
    (ha : ∀ g, e (a g) = b (e' g)) (hφ : ∀ x : A, f' (φ x) = ψ (f x)) (z : H2 A) :
    equivariantH2AddEquiv e' f' he' (groupCohomology.map a φ 2 z) =
      groupCohomology.map b ψ 2 (equivariantH2AddEquiv e f he z) := by
  induction z using H2_induction_on with
  | h z =>
    rw [H2π_comp_map_apply, equivariantH2AddEquiv_H2π, equivariantH2AddEquiv_H2π,
      H2π_comp_map_apply]
    apply congrArg (H2π B')
    apply cocycles₂_ext
    intro g h
    have hE (q : H') : a (e'.symm q) = e.symm (b q) := by
      apply e.injective
      rw [ha, e'.apply_symm_apply, e.apply_symm_apply]
    change f' (φ (z (a (e'.symm g), a (e'.symm h)))) = ψ (f (z (e.symm (b g), e.symm (b h))))
    rw [hE g, hE h, hφ]

end groupCohomology
