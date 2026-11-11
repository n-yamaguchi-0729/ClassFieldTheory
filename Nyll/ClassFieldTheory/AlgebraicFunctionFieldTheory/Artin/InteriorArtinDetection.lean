/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.FiniteSupportDensity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Approximation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtin

/-!
# Interior local reciprocity detects the full absolute abelian map

A continuous idele character trivial on principal ideles and on every
local factor outside a finite set is trivial. Finite local products first
factor the character through the exceptional completions. Actual weak
approximation then makes the principal values dense in that finite product.

Consequently two continuous maps from the whole absolute abelian Galois
group agree as soon as their actual Artin values agree at every place away
from a finite boundary. No boundary ray quotient, and hence no removal of
wild inertia, occurs in this detection theorem.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve LocalClassFieldTheory

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
  {B : Type*} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]

/-- A continuous idele character supported at finitely many actual places
is trivial if it kills every actual principal idele. -/
theorem ideleHom_eq_one_of_principal_and_away
    [HasPrincipalDivisors k K]
    (S : Finset (Place k K)) (h : IdeleGroup k K →ₜ* B)
    (hprincipal : ∀ x : Kˣ, h (IdeleGroup.principalIdele k K x) = 1)
    (haway : ∀ v : Place k K, v ∉ S →
      ∀ u : v.adicCompletionˣ, h (IdeleGroup.placeIdele v u) = 1) :
    ∀ a, h a = 1 := by
  classical
  let b : (∀ v : S, v.val.adicCompletionˣ) →ₜ* B :=
    { toFun := fun a => ∏ v : S, h (IdeleGroup.placeIdele v.val (a v))
      map_one' := by
        apply Finset.prod_eq_one
        intro v hv
        rw [Pi.one_apply, map_one, map_one]
      map_mul' := by
        intro a d
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
      continuous_toFun := continuous_finsetProd _ fun v hv =>
        h.continuous_toFun.comp
          ((IdeleGroup.continuous_placeIdele v.val).comp (continuous_apply v)) }
  let r : IdeleGroup k K →ₜ* (∀ v : S, v.val.adicCompletionˣ) :=
    { toFun := fun a v => a v.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      continuous_toFun := continuous_pi fun v => RestrictedProduct.continuous_eval v.val }
  have hfactor : h = b.comp r := by
    apply RestrictedProduct.continuousMonoidHom_ext_mulSingle
      (fun v : Place k K => v.adicCompletionIntegers.units)
    intro v u
    change h (IdeleGroup.placeIdele v u) =
      ∏ w : S, h (IdeleGroup.placeIdele w.val
        (IdeleGroup.component w.val (IdeleGroup.placeIdele v u)))
    by_cases hv : v ∈ S
    · let z : S := ⟨v, hv⟩
      rw [Finset.prod_eq_single z]
      · rw [IdeleGroup.component_placeIdele_same]
      · intro w hw hwz
        have hwv : w.val ≠ v := fun heq => hwz (Subtype.ext heq)
        rw [IdeleGroup.component_placeIdele_of_ne v w.val u hwv, map_one, map_one]
      · exact fun hz => (hz (Finset.mem_univ z)).elim
    · rw [haway v hv u]
      symm
      apply Finset.prod_eq_one
      intro w hw
      have hwv : w.val ≠ v := fun heq => hv (heq ▸ w.property)
      rw [IdeleGroup.component_placeIdele_of_ne v w.val u hwv, map_one, map_one]
  let d (x : Kˣ) (v : S) : v.val.adicCompletionˣ :=
    Units.map (algebraMap K v.val.adicCompletion) x
  have hd : DenseRange d :=
    denseRange_pi_placeCompletionUnits (fun v : S => v.val) Subtype.val_injective
  have hbprincipal (x : Kˣ) : b (d x) = 1 := by
    have hx := hprincipal x
    rw [hfactor] at hx
    exact hx
  have hb (a : ∀ v : S, v.val.adicCompletionˣ) : b a = 1 := by
    have hrange : Set.range d ⊆ {a | b a = 1} := by
      rintro a ⟨x, rfl⟩
      exact hbprincipal x
    exact closure_minimal hrange
      (isClosed_eq b.continuous_toFun continuous_const) (hd a)
  intro a
  rw [hfactor]
  exact hb (r a)

/-- All local reciprocity values outside any fixed finite boundary
determine a continuous map on the original idele class group. -/
theorem ideleClassHom_ext_away [HasPrincipalDivisors k K]
    (S : Finset (Place k K)) (f g : IdeleClassGroup k K →ₜ* B)
    (haway : ∀ v : Place k K, v ∉ S → ∀ u : v.adicCompletionˣ,
      f (IdeleClassGroup.mk (IdeleGroup.placeIdele v u)) =
        g (IdeleClassGroup.mk (IdeleGroup.placeIdele v u))) : f = g := by
  let q : IdeleGroup k K →ₜ* IdeleClassGroup k K :=
    ⟨IdeleClassGroup.mk, QuotientGroup.continuous_mk⟩
  let h := (f / g).comp q
  have hprincipal (x : Kˣ) : h (IdeleGroup.principalIdele k K x) = 1 := by
    have hx : IdeleClassGroup.mk (IdeleGroup.principalIdele k K x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    change (f / g) (IdeleClassGroup.mk (IdeleGroup.principalIdele k K x)) = 1
    rw [hx, map_one]
  have hl (v : Place k K) (hv : v ∉ S) (u : v.adicCompletionˣ) :
      h (IdeleGroup.placeIdele v u) = 1 := by
    change f (IdeleClassGroup.mk (IdeleGroup.placeIdele v u)) /
      g (IdeleClassGroup.mk (IdeleGroup.placeIdele v u)) = 1
    exact div_eq_one.mpr (haway v hv u)
  have hzero := ideleHom_eq_one_of_principal_and_away S h hprincipal hl
  apply DFunLike.ext
  intro c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup k K) c
  exact div_eq_one.mp (hzero a)

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K]

/-- Actual interior Artin values detect maps from the full absolute
abelian Galois group, including every wild direction at the boundary. -/
theorem absoluteAbelianHom_ext_interiorArtin
    (S : Finset (Place k K)) (f g : localAbsoluteAbelianProfinite K →ₜ* B)
    (haway : ∀ v : Place k K, v ∉ S → ∀ u : v.adicCompletionˣ,
      f (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v u))) =
        g (absoluteArtin k K (IdeleClassGroup.mk (IdeleGroup.placeIdele v u)))) : f = g := by
  have hclass := ideleClassHom_ext_away S
    (f.comp (absoluteArtin k K)) (g.comp (absoluteArtin k K)) haway
  have hrange : Set.range (absoluteArtin k K) ⊆ {a | f a = g a} := by
    rintro a ⟨c, rfl⟩
    exact DFunLike.congr_fun hclass c
  apply DFunLike.ext
  intro a
  exact closure_minimal hrange
    (isClosed_eq f.continuous_toFun g.continuous_toFun) (absoluteArtin_denseRange k K a)

end FunctionField
