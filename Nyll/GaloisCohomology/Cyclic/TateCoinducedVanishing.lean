/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import Nyll.GaloisCohomology.Cyclic.TateComparison

/-!
# Actual Tate vanishing for coinduction from a trivial subgroup

The boundary degrees are proved by explicit primitives: a point function has
constant norm, and a norm-zero function is a sum of translated point-function
differences. Shapiro and the finite-index induction/coinduction equivalence
give the other degrees. All objects are Mathlib's original representations
and Tate complexes.
-/

@[expose] public section

noncomputable section

universe r u

open CategoryTheory
open scoped BigOperators

namespace Rep

variable {R : Type r} {G : Type u} [CommRing R] [Group G]
  {S : Subgroup G} [Subsingleton S] (A : Rep.{u} R S)

attribute [local instance] Classical.propDecidable

/-- The point function at the identity, in the actual coinduced representation. -/
def coindPoint : A →ₗ[R] coind S.subtype A := by
  classical
  refine
    { toFun := fun a => ⟨fun g => if g = 1 then a else 0, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro s g
    obtain rfl : s = 1 := Subsingleton.elim s 1
    change (if (1 : G) * g = 1 then _ else _) =
      A.ρ 1 (if g = 1 then _ else _)
    rw [one_mul, map_one, one_apply_eq_self]
  · intro a b
    apply Subtype.ext
    funext g
    change (if g = 1 then a + b else 0) =
      (if g = 1 then a else 0) + (if g = 1 then b else 0)
    by_cases hg : g = 1 <;> simp only [hg, ite_true, ite_false, add_zero]
  · intro r a
    apply Subtype.ext
    funext g
    change (if g = 1 then r • a else 0) = r • (if g = 1 then a else 0)
    by_cases hg : g = 1 <;> simp only [hg, ite_true, ite_false, smul_zero]

/-- Evaluation of the point function uses the original coefficient. -/
theorem coindPoint_apply (a : A) (g : G) :
    (coindPoint A a).1 g = if g = 1 then a else 0 := by
  classical
  rfl

variable [Fintype G]

omit [Subsingleton S] in
/-- The norm on the original coinduced representation is the finite translated sum. -/
theorem coind_norm_apply (f : coind S.subtype A) (h : G) :
    ((coind S.subtype A).norm.asHom.hom f).1 h = ∑ g : G, f.1 (h * g) := by
  change ((∑ g : G, (coind S.subtype A).ρ g) f).1 h = _
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

end Rep

namespace TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
  {S : Subgroup G} [Subsingleton S] (A : Rep.{u} R S)

/-- Every invariant coinduced function is the norm of an actual point function. -/
theorem isZero_coind_subsingleton_zero :
    Limits.IsZero (tateCohomology (Rep.coind S.subtype A) 0) := by
  classical
  let C := Rep.coind S.subtype A
  let T := ShortComplex.mk C.norm.asHom.toModuleCatHom (groupCohomology.d₀₁ C)
    (Rep.norm_comp_d_eq_zero C)
  have hT : T.Exact := by
    apply (ShortComplex.moduleCat_exact_iff T).mpr
    intro x hx
    have hfix (g : G) : C.ρ g x = x := by
      have h := congrFun hx g
      change C.ρ g x - x = 0 at h
      exact sub_eq_zero.mp h
    have hconst (g : G) : x.1 g = x.1 1 := by
      have h := congrArg (fun f : C => f.1 1) (hfix g)
      change x.1 (1 * g) = x.1 1 at h
      simpa only [one_mul] using h
    refine ⟨Rep.coindPoint A (x.1 1), ?_⟩
    apply Subtype.ext
    funext h
    change (C.norm.asHom.hom (Rep.coindPoint A (x.1 1))).1 h = x.1 h
    rw [Rep.coind_norm_apply]
    change (∑ g : G, if h * g = 1 then x.1 1 else 0) = x.1 h
    rw [Finset.sum_eq_single h⁻¹
      (fun g _ hg => ite_eq_right (fun hprod => hg (mul_eq_one_iff_inv_eq.mp hprod).symm))
      (fun hmissing => (hmissing (Finset.mem_univ _)).elim)]
    simpa only [mul_inv_cancel, ite_true] using (hconst h).symm
  exact Limits.IsZero.of_iso (T.exact_iff_isZero_homology.mp hT) (isoZeroBoundary C)

/-- A norm-zero coinduced function is an actual chain boundary, without a
cyclicity hypothesis on the acting group. -/
theorem isZero_coind_subsingleton_negOne :
    Limits.IsZero (tateCohomology (Rep.coind S.subtype A) (-1)) := by
  classical
  let C := Rep.coind S.subtype A
  let T := ShortComplex.mk (groupHomology.d₁₀ C) C.norm.asHom.toModuleCatHom
    (Rep.comp_eq_zero C)
  have hT : T.Exact := by
    apply (ShortComplex.moduleCat_exact_iff T).mpr
    intro x hx
    have hsum : ∑ g : G, x.1 g = 0 := by
      have h := congrArg (fun f : C => f.1 1) hx
      change (C.norm.asHom.hom x).1 1 = 0 at h
      rw [Rep.coind_norm_apply] at h
      simpa only [one_mul] using h
    refine ⟨∑ g : G, Finsupp.single g (Rep.coindPoint A (x.1 g)), ?_⟩
    change groupHomology.d₁₀ C
      (∑ g : G, Finsupp.single g (Rep.coindPoint A (x.1 g))) = x
    rw [map_sum]
    have hdiff : (∑ g : G, groupHomology.d₁₀ C (Finsupp.single g (Rep.coindPoint A (x.1 g)))) =
        ∑ g : G, (C.ρ g⁻¹ (Rep.coindPoint A (x.1 g)) - Rep.coindPoint A (x.1 g)) :=
      Finset.sum_congr rfl (fun g _ => groupHomology.d₁₀_single C g _)
    rw [hdiff]
    rw [Finset.sum_sub_distrib, ← map_sum, hsum, map_zero, sub_zero]
    apply Subtype.ext
    funext h
    let eval : C →ₗ[R] A := (LinearMap.proj h).comp (Representation.coindV S.subtype A.ρ).subtype
    change eval (∑ g : G, C.ρ g⁻¹ (Rep.coindPoint A (x.1 g))) = x.1 h
    rw [map_sum]
    change (∑ g : G, if h * g⁻¹ = 1 then x.1 g else 0) = x.1 h
    rw [Finset.sum_eq_single h
      (fun g _ hg => ite_eq_right (fun hprod => hg (mul_inv_eq_one.mp hprod).symm))
      (fun hmissing => (hmissing (Finset.mem_univ _)).elim)]
    simp only [mul_inv_cancel, ite_true]
  exact Limits.IsZero.of_iso (T.exact_iff_isZero_homology.mp hT) (isoNegOneBoundary C)

/-- Coinduction from any subsingleton subgroup is acyclic for the original
Tate complex in every integer degree. -/
theorem isZero_coind_subsingleton (n : ℤ) :
    Limits.IsZero (tateCohomology (Rep.coind S.subtype A) n) := by
  classical
  cases n with
  | ofNat n =>
      cases n with
      | zero => exact isZero_coind_subsingleton_zero A
      | succ n =>
          have hzero := isZero_groupCohomology_succ_of_subsingleton A n
          exact Limits.IsZero.of_iso hzero
            ((isoGroupCohomology (n + 1)).app (Rep.coind S.subtype A) ≪≫
              groupCohomology.coindIso A (n + 1))
  | negSucc n =>
      cases n with
      | zero => exact isZero_coind_subsingleton_negOne A
      | succ n =>
          have hzero := isZero_groupHomology_succ_of_subsingleton (A := A) n
          exact Limits.IsZero.of_iso hzero
            ((isoGroupHomology (Int.negSucc (n + 1)) (n + 1) (by omega)).app
                (Rep.coind S.subtype A) ≪≫
              (groupHomology.functor R G (n + 1)).mapIso (Rep.indCoindIso A).symm ≪≫
                groupHomology.indIso S A (n + 1))

end TateCohomology
