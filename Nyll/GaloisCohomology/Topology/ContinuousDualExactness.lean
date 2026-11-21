/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousDual
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness
public import Nyll.GaloisCohomology.ProfiniteIntegers.ZModCircle
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Isomorphisms

/-! # Short exact sequences of discrete contragredients -/

@[expose] public section

open CategoryTheory ContRepresentation

noncomputable section

namespace TopRep

universe u r

section Coefficients

variable {R : Type r} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type u} [Group G]

/-- The reversed coefficient sequence uses precomposition with the original
maps. -/
def discreteLinearDualShortComplex (M : TopRep.{u} R G)
    (S : ShortComplex (TopRep.{u} R G)) : ShortComplex (TopRep.{u} R G) where
  X₁ := discreteLinearDual S.X₃ M
  X₂ := discreteLinearDual S.X₂ M
  X₃ := discreteLinearDual S.X₁ M
  f := discreteLinearDualPullback M S.g
  g := discreteLinearDualPullback M S.f
  zero := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro l
    apply LinearMap.ext
    intro a
    change discreteLinearDualMap S.X₃ M l (S.g (S.f a)) = 0
    rw [show S.g (S.f a) = 0 from ConcreteCategory.congr_hom S.zero a, map_zero]

theorem discreteLinearDualPullback_injective (M : TopRep.{u} R G)
    {A B : TopRep.{u} R G} (f : A ⟶ B) (hf : Function.Surjective f) :
    Function.Injective (discreteLinearDualPullback M f) := by
  intro l m hlm
  apply LinearMap.ext
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact congrArg (fun d => discreteLinearDualMap A M d a) hlm

/-- A dual coefficient vanishing on the first map factors through the
original quotient map, via its linear kernel quotient. -/
theorem discreteLinearDualShortComplex_exact (M : TopRep.{u} R G)
    (S : ShortComplex (TopRep.{u} R G)) (hg : Function.Surjective S.g)
    (hexact : ∀ b : S.X₂, S.g b = 0 → ∃ a : S.X₁, S.f a = b)
    (l : discreteLinearDual S.X₂ M) (hl : discreteLinearDualPullback M S.f l = 0) :
    ∃ m : discreteLinearDual S.X₃ M, discreteLinearDualPullback M S.g m = l := by
  let g := S.g.hom.toContinuousLinearMap.toLinearMap
  let l₀ := discreteLinearDualMap S.X₂ M l
  have hker : g.ker ≤ l₀.ker := by
    intro b hb
    obtain ⟨a, rfl⟩ := hexact b hb
    exact congrArg (fun d => discreteLinearDualMap S.X₁ M d a) hl
  let e := g.quotKerEquivOfSurjective hg
  let m : discreteLinearDual S.X₃ M := (g.ker.liftQ l₀ hker).comp e.symm.toLinearMap
  refine ⟨m, LinearMap.ext fun b => ?_⟩
  change (g.ker.liftQ l₀ hker) (e.symm (g b)) = l₀ b
  rw [← g.quotKerEquivOfSurjective_apply_mk hg b, e.symm_apply_apply]
  rfl

end Coefficients

/-- A character of a subgroup of an `n`-torsion abelian group extends with
values in the same finite cyclic group. Divisibility gives the extension in
the circle, and the exponent forces its image into `ZMod n`. -/
theorem exists_addHom_zmod_extension {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) [NeZero n] (f : A →+ B) (hf : Function.Injective f)
    (hn : ∀ b : B, n • b = 0) (l : A →+ ZMod n) :
    ∃ m : B →+ ZMod n, m.comp f = l := by
  let j : ZMod n →+ UnitAddCircle := ZMod.toAddCircle
  obtain ⟨β, hβ⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    f hf (j.comp l)
  have hβn (b : B) : n • β b = 0 := by
    rw [← map_nsmul, hn, map_zero]
  choose m hm using fun b => ZMod.exists_toAddCircle_eq_of_nsmul_eq_zero n (β b) (hβn b)
  have hj := ZMod.toAddCircle_injective n
  let m₀ : B →+ ZMod n :=
    { toFun := m
      map_zero' := by
        apply hj
        simp only [hm, map_zero]
      map_add' := fun b c => by
        apply hj
        simp only [map_add, hm] }
  refine ⟨m₀, AddMonoidHom.ext fun a => hj ?_⟩
  change ZMod.toAddCircle (m (f a)) = j (l a)
  rw [hm]
  exact DFunLike.congr_fun hβ a

/-- A finite cyclic functional that kills the kernel of an additive map
extends across that map whenever the target is annihilated by its modulus. -/
theorem exists_addHom_zmod_extension_of_ker_le {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) [NeZero n] (f : A →+ B) (l : A →+ ZMod n)
    (hker : f.ker ≤ l.ker) (hn : ∀ b : B, n • b = 0) :
    ∃ m : B →+ ZMod n, m.comp f = l := by
  let q := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hk : q.ker ≤ l.ker := fun x hx => hker (congrArg Subtype.val hx)
  let e := q.liftOfSurjective hq ⟨l, hk⟩
  have he : e.comp q = l := q.liftOfRightInverse_comp (Function.surjInv hq)
    (Function.rightInverse_surjInv hq) ⟨l, hk⟩
  obtain ⟨m, hm⟩ := exists_addHom_zmod_extension (A := ↥f.range) (B := B) n f.range.subtype
    Subtype.val_injective hn e
  exact ⟨m, AddMonoidHom.ext fun a =>
    (DFunLike.congr_fun hm (q a)).trans (DFunLike.congr_fun he a)⟩

/-- For a cyclic dualizing coefficient of order `n`, pullback along an
injection of `n`-torsion representations is surjective. -/
theorem discreteLinearDualPullback_surjective_of_zmod {G : Type u} [Group G]
    {A B : TopRep.{u} ℤ G} (M : TopRep.{u} ℤ G) (n : ℕ) [NeZero n]
    (e : M ≃+ ZMod n) (f : A ⟶ B) (hf : Function.Injective f)
    (hn : ∀ b : B, n • b = 0) : Function.Surjective (discreteLinearDualPullback M f) := by
  intro l
  let : Module ℤ A := A.hV2
  let : Module ℤ B := B.hV2
  let : Module ℤ M := M.hV2
  let f₀ := f.hom.toContinuousLinearMap.toLinearMap.toAddMonoidHom
  let l₀ := e.toAddMonoidHom.comp (discreteLinearDualMap A M l).toAddMonoidHom
  obtain ⟨m, hm⟩ := exists_addHom_zmod_extension n f₀ hf hn l₀
  let m₀ := e.symm.toAddMonoidHom.comp m
  let m₁ : B →ₗ[ℤ] M :=
    { toFun := m₀
      map_add' := m₀.map_add
      map_smul' := fun i b => by
        change m₀ (B.hV2.smul i b) = M.hV2.smul i (m₀ b)
        rw [int_smul_eq_zsmul B.hV2, int_smul_eq_zsmul M.hV2, map_zsmul] }
  refine ⟨m₁, LinearMap.ext fun a => ?_⟩
  change e.symm (m (f a)) = discreteLinearDualMap A M l a
  apply e.injective
  rw [e.apply_symm_apply]
  exact DFunLike.congr_fun hm a

/-- Both projection identities and the scalar restriction–transfer
composites descend a perfect additive pairing across a prime-to-p index. -/
theorem bijective_addHom_pairing_of_primeToIndex
    {A B A' B' : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    (p d : ℕ) [Fact p.Prime] (hd : ¬ p ∣ d)
    (P : A →+ (B →+ ZMod p)) (P' : A' →+ (B' →+ ZMod p))
    (rA : A →+ A') (rB : B →+ B') (cA : A' →+ A) (cB : B' →+ B)
    (hpA : ∀ a : A, p • a = 0) (hpB : ∀ b : B, p • b = 0) (hpB' : ∀ b : B', p • b = 0)
    (hA : ∀ a, cA (rA a) = d • a) (hB : ∀ b, cB (rB b) = d • b)
    (hleft : ∀ a b, P' (rA a) b = P a (cB b))
    (hright : ∀ a b, P' a (rB b) = P (cA a) b) (hP' : Function.Bijective P') :
    Function.Bijective P := by
  have hrestr {V W : Type u} [AddCommGroup V] [AddCommGroup W]
      (r : V →+ W) (c : W →+ V) (hann : ∀ v : V, p • v = 0)
      (hcr : ∀ v : V, c (r v) = d • v) : Function.Injective r := by
    apply (injective_iff_map_eq_zero r).mpr
    intro v hv
    by_contra hne
    have ho : addOrderOf v = p := addOrderOf_eq_prime (hann v) hne
    have hzero : d • v = 0 := (hcr v).symm.trans (hv ▸ map_zero c)
    exact hd (ho ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  refine ⟨(injective_iff_map_eq_zero P).mpr ?_, ?_⟩
  · intro a ha
    apply hrestr rA cA hpA hA
    rw [map_zero]
    apply hP'.injective
    ext b
    rw [hleft, ha, map_zero]
    rfl
  · intro l
    let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    obtain ⟨l', hl⟩ := exists_addHom_zmod_extension p rB (hrestr rB cB hpB hB) hpB' l
    obtain ⟨a', ha⟩ := hP'.surjective l'
    refine ⟨cA a', AddMonoidHom.ext fun b => ?_⟩
    rw [← hright, ha]
    exact DFunLike.congr_fun hl b

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- The reversed coefficient sequence supplies the long exact sequence of
the same continuous cohomology once coefficient homomorphisms extend. -/
theorem continuousModuleComplex_discreteLinearDual_shortExact
    (M : TopRep.{u} ℤ G) [DiscreteTopology M]
    (S : ShortComplex (TopRep.{u} ℤ G))
    [Finite S.X₂] [Finite S.X₃] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hg : Function.Surjective S.g)
    (hexact : ∀ b : S.X₂, S.g b = 0 → ∃ a : S.X₁, S.f a = b)
    (hextend : Function.Surjective (discreteLinearDualPullback M S.f))
    (h₂ : Continuous (fun p : G × S.X₂ => S.X₂.ρ p.1 p.2))
    (h₃ : Continuous (fun p : G × S.X₃ => S.X₃.ρ p.1 p.2))
    (hM : Continuous (fun p : G × M => M.ρ p.1 p.2)) :
    ((discreteLinearDualShortComplex M S).map (continuousModuleComplexFunctor G)).ShortExact := by
  let T := discreteLinearDualShortComplex M S
  let : DiscreteTopology T.X₁ := discreteLinearDual_discrete S.X₃ M
  let : DiscreteTopology T.X₂ := discreteLinearDual_discrete S.X₂ M
  let : DiscreteTopology T.X₃ := discreteLinearDual_discrete S.X₁ M
  apply continuousModuleComplex_shortExact G T
  · exact discreteLinearDualPullback_injective M S.g hg
  · exact hextend
  · exact discreteLinearDualShortComplex_exact M S hg hexact
  · exact discreteLinearDual_action_continuous S.X₃ M h₃ hM
  · exact discreteLinearDual_action_continuous S.X₂ M h₂ hM

end TopRep
