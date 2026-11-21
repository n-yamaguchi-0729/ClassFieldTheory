/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.Module.LocalizedModule.Int
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# A trace-dual family for the ring of integers

Localizing linear forms on the projective integral closure identifies them
with trace pairings. The resulting finite expansion can be transported to
the field tensor product and to each completion factor.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors
open Module NumberField

noncomputable section
namespace AlgebraicNumberTheory.Discriminant

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- A finite projective presentation of the ring of integers over the base
gives an integral trace-dual expansion on the fraction fields. -/
theorem exists_ringOfIntegers_traceDual_expansion :
    ∃ (n : ℕ) (b : Fin n → 𝓞 L) (y : Fin n → L),
      (∀ i, y i ∈ Submodule.traceDual (𝓞 K) K (1 : Submodule (𝓞 L) L)) ∧
      ∀ x : L, ∑ i, Algebra.trace K L (x * (b i : L)) • y i = x := by
  classical
  let A := 𝓞 K
  let B := 𝓞 L
  let j : B →ₗ[A] L := (IsScalarTower.toAlgHom A B L).toLinearMap
  let k : A →ₗ[A] K := Algebra.linearMap A K
  let : IsLocalizedModule A⁰ j :=
    (isLocalizedModule_iff_isLocalization (S := A⁰) (R := A) (A := B) (Aₛ := L)).mpr
      (IsIntegralClosure.isLocalization A K L B)
  let : IsLocalizedModule A⁰ k :=
    (isLocalizedModule_iff_isLocalization (S := A⁰) (R := A) (A := A) (Aₛ := K)).mpr inferInstance
  have represent (f : B →ₗ[A] A) : ∃ y : L,
      ∀ z : B, Algebra.trace K L (y * (z : L)) = algebraMap A K (f z) := by
    let f' := IsLocalizedModule.lift A⁰ j (k.comp f) (IsLocalizedModule.map_units k)
    let φ := f'.extendScalarsOfIsLocalization A⁰ K
    refine ⟨((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L)).symm φ, ?_⟩
    intro z
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
    change f' (j z) = (k.comp f) z
    exact IsLocalizedModule.lift_apply A⁰ j (k.comp f) (IsLocalizedModule.map_units k) z
  let : Module.Finite ℤ B := IsNoetherian.finite _ _
  let : Module.Finite A B := Module.Finite.of_restrictScalars_finite ℤ A B
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (fun _ _ h => Subtype.ext ((algebraMap K L).injective (congrArg Subtype.val h)))
  let : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  let : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, F, G, _, _, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  choose y hy using fun i : Fin n => represent (LinearMap.proj i ∘ₗ G)
  let b : Fin n → B := fun i => F (Pi.single i 1)
  have expand (z : B) : ∑ i, algebraMap A K (G z i) • (b i : L) = (z : L) := by
    have hz : G z = ∑ i, G z i • Pi.single i (1 : A) := by
      ext i
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single i, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj.symm, smul_zero]
      · exact fun hi => (hi (Finset.mem_univ i)).elim
    calc
      _ = j (F (∑ i, G z i • Pi.single i (1 : A))) := by
        rw [map_sum F, map_sum j]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, map_smul]
        exact algebraMap_smul K (G z i) (b i : L)
      _ = (z : L) := by
        rw [← hz]
        exact congrArg j (LinearMap.congr_fun hFG z)
  refine ⟨n, b, y, ?_, ?_⟩
  · intro i
    rw [Submodule.mem_traceDual]
    intro _ hz
    obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hz
    rw [Algebra.traceForm_apply, hy]
    exact ⟨_, rfl⟩
  · intro x
    let q := (∑ i, Algebra.trace K L (x * (b i : L)) • y i) - x
    have hpair (z : B) : Algebra.trace K L (q * (z : L)) = 0 := by
      dsimp only [q]
      rw [sub_mul, map_sub, Finset.sum_mul, map_sum, sub_eq_zero]
      conv_rhs => rw [← expand z, Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, hy]
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul, mul_comm]
    let f := (Algebra.traceForm K L q).restrictScalars A
    have hf : f = 0 := by
      apply IsLocalizedModule.ext A⁰ j (IsLocalizedModule.map_units k)
      ext z
      exact hpair z
    apply sub_eq_zero.mp
    apply (traceForm_nondegenerate K L).1 q
    intro z
    exact DFunLike.congr_fun hf z

end AlgebraicNumberTheory.Discriminant
