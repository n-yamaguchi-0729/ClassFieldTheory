/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.H2EquivariantEquivalence

/-! # Degree-two cohomology pullback across independent universes -/

@[expose] public section

noncomputable section

open CategoryTheory

namespace groupCohomology

universe u v w

variable {R G : Type u} {S H : Type v} [CommRing R] [CommRing S] [Group G] [Group H]
  {A : Rep R G} {B : Rep S H}
  (r : H →* G) (p : A →+ B) (hp : ∀ g a, p (A.ρ (r g) a) = B.ρ g (p a))

include r p hp in
/-- Pull back the two group arguments and apply the coefficient map to a cocycle. -/
def pullbackCocycles₂ : cocycles₂ A →+ cocycles₂ B where
  toFun z := ⟨fun gh => p (z (r gh.1, r gh.2)), by
    rw [mem_cocycles₂_iff]
    intro g h j
    change p (z (r (g * h), r j)) + p (z (r g, r h)) =
      B.ρ g (p (z (r h, r j))) + p (z (r g, r (h * j)))
    simp only [map_mul, ← hp, ← map_add]
    exact congrArg p ((mem_cocycles₂_iff (z : G × G → A)).1 z.property (r g) (r h) (r j))⟩
  map_zero' := by
    apply cocycles₂_ext
    intro g h
    exact map_zero p
  map_add' x y := by
    apply cocycles₂_ext
    intro g h
    exact map_add p (x (r g, r h)) (y (r g, r h))

/-- Pullback preserves two-coboundaries. -/
theorem pullbackCocycles₂_boundary (z : cocycles₂ A) (hz : H2π A z = 0) :
    H2π B (pullbackCocycles₂ r p hp z) = 0 := by
  obtain ⟨b, hb⟩ := (H2π_eq_zero_iff z).1 hz
  apply (H2π_eq_zero_iff _).2
  refine ⟨fun g => p (b (r g)), ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  have he := congrArg p (congrFun hb (r g, r h))
  change p (A.ρ (r g) (b (r h)) - b (r g * r h) + b (r g)) = p (z (r g, r h)) at he
  change B.ρ g (p (b (r h))) - p (b (r (g * h))) + p (b (r g)) = p (z (r g, r h))
  rw [map_mul]
  rwa [map_add, map_sub, hp] at he

include r p hp in
/-- Pull back the group arguments and apply the equivariant coefficient map on H². -/
def H2EquivariantPullback : H2 A →+ H2 B := by
  let qA := (H2π A).hom.toAddMonoidHom
  let qB := (H2π B).hom.toAddMonoidHom
  let e := QuotientAddGroup.quotientKerEquivOfSurjective qA
    ((ModuleCat.epi_iff_surjective (H2π A)).1 inferInstance)
  exact (QuotientAddGroup.lift qA.ker (qB.comp (pullbackCocycles₂ r p hp))
    (fun z hz => pullbackCocycles₂_boundary r p hp z hz)).comp e.symm.toAddMonoidHom

private theorem H2EquivariantPullback_H2π (z : cocycles₂ A) :
    H2EquivariantPullback r p hp (H2π A z) = H2π B (pullbackCocycles₂ r p hp z) := by
  let qA := (H2π A).hom.toAddMonoidHom
  let qB := (H2π B).hom.toAddMonoidHom.comp (pullbackCocycles₂ r p hp)
  let e := QuotientAddGroup.quotientKerEquivOfSurjective qA
    ((ModuleCat.epi_iff_surjective (H2π A)).1 inferInstance)
  let hq (a : cocycles₂ A) (ha : a ∈ qA.ker) : qB a = 0 :=
    pullbackCocycles₂_boundary r p hp a ha
  have he : e.symm (H2π A z) = QuotientAddGroup.mk z := by
    apply e.injective
    exact e.apply_symm_apply _
  change QuotientAddGroup.lift qA.ker qB hq (e.symm (H2π A z)) = _
  exact (congrArg (QuotientAddGroup.lift qA.ker qB hq) he).trans rfl

/-- A commuting square of group and coefficient maps identifies cross-universe pullback with
ordinary functoriality on the compared representations. -/
theorem equivariantH2AddEquiv_pullback
    {T G' H' : Type w} [CommRing T] [Group G'] [Group H'] {A' : Rep T G'} {B' : Rep T H'}
    (e : G ≃* G') (f : A ≃+ A') (hf : ∀ g a, f (A.ρ g a) = A'.ρ (e g) (f a))
    (e' : H ≃* H') (f' : B ≃+ B') (hf' : ∀ g b, f' (B.ρ g b) = B'.ρ (e' g) (f' b))
    (r' : H' →* G') (φ : Rep.res r' A' ⟶ B')
    (hr : ∀ g, e (r g) = r' (e' g)) (hφ : ∀ a, f' (p a) = φ (f a)) (z : H2 A) :
    equivariantH2AddEquiv e' f' hf' (H2EquivariantPullback r p hp z) =
      groupCohomology.map r' φ 2 (equivariantH2AddEquiv e f hf z) := by
  induction z using H2_induction_on with
  | h z =>
    rw [H2EquivariantPullback_H2π r p hp, equivariantH2AddEquiv_H2π e' f' hf',
      equivariantH2AddEquiv_H2π e f hf,
      H2π_comp_map_apply]
    apply congrArg (H2π B')
    apply cocycles₂_ext
    intro g h
    have ha (x : H') : r (e'.symm x) = e.symm (r' x) := by
      apply e.injective
      rw [hr, e'.apply_symm_apply, e.apply_symm_apply]
    change f' (p (z (r (e'.symm g), r (e'.symm h)))) = φ (f (z (e.symm (r' g), e.symm (r' h))))
    rw [ha g, ha h, hφ]

end groupCohomology
