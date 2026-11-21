/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology

/-!
# Exactness of the original integral Tate connecting maps

The native long exact sequence supplies actual preimages in the existing
independent-universe Tate objects. If the two adjacent middle groups vanish,
the specified connecting map itself is bijective and hence gives the
dimension-shifting equivalence. No new Tate object or chosen comparison map
is introduced.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G]

/-- The same original short exact sequence stays short exact under its single
group/carrier lift and the existing integer coefficient transport. -/
theorem native_shortExact {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact) :
    (S.map (nativeFunctor G)).ShortExact := by
  simpa only [nativeFunctor, ShortComplex.map_comp] using
    IntegralGroupCohomology.coefficient_shortExact
      (Rep.universeLiftFunctor_shortExact ℤ G hS)

variable [Fintype G] {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact)

/-- A class killed by the actual connecting map comes from the middle term. -/
theorem exists_tate_preimage_of_δ_eq_zero (n : ℤ) (x : tate S.X₃ n)
    (hx : tateδ hS n x = 0) :
    ∃ y : tate S.X₂ n, (tateFunctor G n).map S.g y = x := by
  exact (ShortComplex.moduleCat_exact_iff _).mp
    (TateCohomology.exact₃ (native_shortExact hS) n) x hx

/-- Exactness at the middle term of the original integral Tate sequence. -/
theorem exists_tate_preimage_of_map_g_eq_zero (hS : S.ShortExact) (n : ℤ) (x : tate S.X₂ n)
    (hx : (tateFunctor G n).map S.g x = 0) :
    ∃ y : tate S.X₁ n, (tateFunctor G n).map S.f y = x := by
  exact (ShortComplex.moduleCat_exact_iff _).mp
    ((TateCohomology.map_tateComplexFunctor_shortExact
      (native_shortExact hS)).homology_exact₂ n) x hx

/-- The original Tate coefficient map followed by the boundary is zero on classes. -/
theorem tateδ_map_g_eq_zero (n : ℤ) (x : tate S.X₂ n) :
    tateδ hS n ((tateFunctor G n).map S.g x) = 0 := by
  let T := S.map (nativeFunctor G)
  exact congrArg (fun m : tateCohomology T.X₂ n ⟶ tateCohomology T.X₁ (n + 1) => m x)
    (TateCohomology.map_δ (native_shortExact hS) n)

/-- The original Tate boundary followed by the next coefficient map is zero on classes. -/
theorem tate_map_f_δ_eq_zero (n : ℤ) (x : tate S.X₃ n) :
    (tateFunctor G (n + 1)).map S.f (tateδ hS n x) = 0 := by
  let T := S.map (nativeFunctor G)
  exact congrArg (fun m : tateCohomology T.X₃ n ⟶ tateCohomology T.X₂ (n + 1) => m x)
    (TateCohomology.δ_map (native_shortExact hS) n)

/-- A class killed by the next coefficient map is the boundary of a class in
the quotient term, using the existing native connecting map. -/
theorem exists_tate_δ_preimage_of_map_eq_zero (n : ℤ) (x : tate S.X₁ (n + 1))
    (hx : (tateFunctor G (n + 1)).map S.f x = 0) :
    ∃ y : tate S.X₃ n, tateδ hS n y = x := by
  exact (ShortComplex.moduleCat_exact_iff _).mp
    (TateCohomology.exact₁ (native_shortExact hS) n) x hx

/-- Vanishing of the middle term in the source degree makes the actual
connecting map injective. -/
theorem tateδ_injective_of_isZero_middle (n : ℤ)
    (hzero : Limits.IsZero (tate S.X₂ n)) : Function.Injective (tateδ hS n) := by
  let : Subsingleton (tate S.X₂ n) := ModuleCat.subsingleton_of_isZero hzero
  intro x y hxy
  have hδ : tateδ hS n (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := exists_tate_preimage_of_δ_eq_zero hS n (x - y) hδ
  have hz0 : z = 0 := Subsingleton.elim _ _
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- Vanishing of the middle term in the target degree makes the actual
connecting map surjective. -/
theorem tateδ_surjective_of_isZero_middle (n : ℤ)
    (hzero : Limits.IsZero (tate S.X₂ (n + 1))) :
    Function.Surjective (tateδ hS n) := by
  let : Subsingleton (tate S.X₂ (n + 1)) := ModuleCat.subsingleton_of_isZero hzero
  intro x
  exact exists_tate_δ_preimage_of_map_eq_zero hS n x (Subsingleton.elim _ _)

/-- The connecting map is bijective when both adjacent middle groups vanish. -/
theorem tateδ_bijective_of_isZero_middle (n : ℤ)
    (hzero : Limits.IsZero (tate S.X₂ n))
    (hnext : Limits.IsZero (tate S.X₂ (n + 1))) :
    Function.Bijective (tateδ hS n) :=
  ⟨tateδ_injective_of_isZero_middle hS n hzero,
    tateδ_surjective_of_isZero_middle hS n hnext⟩

/-- The dimension-shifting equivalence whose forward map is precisely the
existing connecting homomorphism. -/
def tateδEquiv (n : ℤ) (hzero : Limits.IsZero (tate S.X₂ n))
    (hnext : Limits.IsZero (tate S.X₂ (n + 1))) :
    tate S.X₃ n ≃ₗ[ℤ] tate S.X₁ (n + 1) :=
  LinearEquiv.ofBijective (tateδ hS n).hom
    (tateδ_bijective_of_isZero_middle hS n hzero hnext)

/-- The equivalence does not replace the native connecting map by an arbitrary
isomorphism of its source and target. -/
theorem tateδEquiv_apply (n : ℤ) (hzero : Limits.IsZero (tate S.X₂ n))
    (hnext : Limits.IsZero (tate S.X₂ (n + 1))) (x : tate S.X₃ n) :
    tateδEquiv hS n hzero hnext x = tateδ hS n x := rfl

end IntegralGroupCohomology.Universe
