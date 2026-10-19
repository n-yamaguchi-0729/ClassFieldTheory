/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierBoundedClasses
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierRayNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormCompositum
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
import Nyll.GaloisCohomology.ArtinSchreier.FiniteExtension
import Nyll.GaloisCohomology.ArtinSchreier.RestrictionDegree
import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Actual finite extensions splitting all bounded Artin–Schreier classes

Choose one bounded representative for each of the finitely many parameter
classes and take the compositum of their actual root extensions. Restriction
to those factors proves exponent p. Their conductor bounds and the existing
compositum norm theorem give the ray norm inclusion. Every bounded class
splits in this field, so the root-character degree bound supplies the required
lower bound on its degree.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

private theorem finiteSup_exponent_ray_norm
    (p : ℕ) (m : RayClass.Modulus k K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    ∀ {ι : Type} (A : ι → FiniteGaloisIntermediateField K (SeparableClosure K)),
      (∀ i, IsAbelianGalois K (A i)) →
      (∀ i (σ : Gal(A i/K)), σ ^ p = 1) →
      (∀ i, RayClass.rayClassSubgroup (p • m) ≤
        (IdeleClassGroup.norm (k := k) (K := K) (L := A i)).range) →
      ∀ (s : Finset ι), s.Nonempty →
        IsAbelianGalois K ↥(s.sup A) ∧
        (∀ σ : Gal(↥(s.sup A)/K), σ ^ p = 1) ∧
        RayClass.rayClassSubgroup (p • m) ≤
          (IdeleClassGroup.norm (k := k) (K := K) (L := ↥(s.sup A))).range := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ ι A hAb hExp hNorm s hs
  have hcombine (E F : FiniteGaloisIntermediateField K (SeparableClosure K))
      (hE : IsAbelianGalois K E) (hF : IsAbelianGalois K F)
      (hEp : ∀ σ : Gal(E/K), σ ^ p = 1) (hFp : ∀ σ : Gal(F/K), σ ^ p = 1)
      (hEN : RayClass.rayClassSubgroup (p • m) ≤
        (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range)
      (hFN : RayClass.rayClassSubgroup (p • m) ≤
        (IdeleClassGroup.norm (k := k) (K := K) (L := F)).range) :
      IsAbelianGalois K ↥(E ⊔ F) ∧
      (∀ σ : Gal(↥(E ⊔ F)/K), σ ^ p = 1) ∧
      RayClass.rayClassSubgroup (p • m) ≤
        (IdeleClassGroup.norm (k := k) (K := K) (L := ↥(E ⊔ F))).range := by
    have hab : IsAbelianGalois K ↥(E ⊔ F) :=
      IsAbelianGalois.sup E.toIntermediateField F.toIntermediateField
    refine ⟨hab, ?_, ?_⟩
    · intro σ
      apply IntermediateField.restrictNormalHomSupProd_injective
        E.toIntermediateField F.toIntermediateField
      rw [map_pow, map_one]
      exact Prod.ext (hEp _) (hFp _)
    · change RayClass.rayClassSubgroup (p • m) ≤
        (IdeleClassGroup.norm (k := k) (K := K)
          (L := ↥(E.toIntermediateField ⊔ F.toIntermediateField))).range
      rw [finiteAbelian_norm_range_sup k K E.toIntermediateField F.toIntermediateField]
      exact le_inf hEN hFN
  let P : FiniteGaloisIntermediateField K (SeparableClosure K) → Prop := fun E =>
    IsAbelianGalois K E ∧ (∀ σ : Gal(E/K), σ ^ p = 1) ∧
      RayClass.rayClassSubgroup (p • m) ≤
        (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range
  change P (s.sup A)
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    rw [Finset.sup_singleton]
    exact ⟨hAb i, hExp i, hNorm i⟩
  | cons i s _ _ ih =>
    rw [Finset.sup_cons]
    exact hcombine (A i) (s.sup A) (hAb i) ih.1 (hExp i) ih.2.1 (hNorm i) ih.2.2

/-- The actual finite compositum of bounded AS root extensions has enough
degree to split all bounded parameter classes and contains the required
ray subgroup in its actual norm image. -/
theorem exists_artinSchreier_bounded_extension
    (p : ℕ) [Fact p.Prime] [CharP K p] (m : RayClass.Modulus k K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    ∃ E : IntermediateField K (SeparableClosure K),
      ∃ (_ : FiniteDimensional K E) (_ : IsAbelianGalois K E),
        (∀ σ : Gal(E/K), σ ^ p = 1) ∧
        RayClass.rayClassSubgroup (p • m) ≤
          (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range ∧
        Nat.card (boundedArtinSchreierClasses p (p • (AlgebraicCurve.Modulus.toDivisor m))) ≤
          Module.finrank K E := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  classical
  have hcurve : IsCurveOver k K := isCurveOver k K
  have hess : Algebra.EssFiniteType k K := essFiniteType k K
  have hplace : Nonempty (Place k K) := nonempty_place k K
  have hzero : FiniteDimensional k (LSpace (0 : Divisor k K)) :=
    finiteDimensional_lSpace_zero k K
  let W := boundedArtinSchreierClasses p (p • (AlgebraicCurve.Modulus.toDivisor m))
  have hWfinite : Finite W :=
    boundedArtinSchreierClasses_finite p (p • (AlgebraicCurve.Modulus.toDivisor m))
  let wFintype : Fintype W := Fintype.ofFinite W
  have hrep (w : W) : ∃ a : K, a ∈ LSpace (p • (AlgebraicCurve.Modulus.toDivisor m)) ∧
      (a : K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) = w.val :=
    w.property
  choose a ha hclass using hrep
  choose A hcyclic β hβ hgen using fun w : W =>
    ArtinSchreierTheory.exists_finite_cyclic_extension p K (SeparableClosure K) (a w)
  have hAb (w : W) : IsAbelianGalois K (A w) := by
    have hc : IsCyclic Gal(A w/K) := hcyclic w
    exact IsAbelianGalois.of_isCyclic K (A w)
  have hExp (w : W) (σ : Gal(A w/K)) : σ ^ p = 1 := by
    have hchar : CharP (A w) p := (Algebra.charP_iff K (A w) p).mp inferInstance
    apply orderOf_dvd_iff_pow_eq_one.mp
    apply (orderOf_dvd_natCard σ).trans
    rw [IsGalois.card_aut_eq_finrank K (A w)]
    exact ArtinSchreierTheory.finrank_dvd_prime_of_adjoin_eq_top
      p (a w) (β w) (hβ w) (hgen w)
  have hNorm (w : W) : RayClass.rayClassSubgroup (p • m) ≤
      (IdeleClassGroup.norm (k := k) (K := K) (L := A w)).range := by
    have habelian : IsAbelianGalois K (A w) := hAb w
    have hprincipal : HasPrincipalDivisors k (A w) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K (A w)).toHasPrincipalDivisors
    apply artinSchreier_rayClassSubgroup_le_norm p m (a w) (β w) (hβ w) (hgen w)
    intro v
    simpa only [Finsupp.smul_apply, Modulus.toDivisor_apply, nsmul_eq_mul, Nat.cast_mul]
      using ha w v
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) := Finset.univ.sup A
  obtain ⟨hEab, hEp, hEN⟩ :=
    finiteSup_exponent_ray_norm k K p m A hAb hExp hNorm Finset.univ Finset.univ_nonempty
  have hcharE : CharP E p := (Algebra.charP_iff K E p).mp inferInstance
  have hsplit : W ≤ (ArtinSchreierTheory.classMap p (algebraMap K E)).ker := by
    intro w hw
    let q : W := ⟨w, hw⟩
    have hAE : (A q).toIntermediateField ≤ E.toIntermediateField :=
      Finset.le_sup (f := A) (Finset.mem_univ q)
    let ι : A q →ₐ[K] E := IntermediateField.inclusion hAE
    have hroot : (ι (β q)) ^ p - ι (β q) = algebraMap K E (a q) := by
      rw [← map_pow, ← map_sub, hβ q, ι.commutes]
    have hz : ArtinSchreierTheory.classMap p (algebraMap K E)
        (a q : K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨ι (β q), hroot⟩
    exact (congrArg (ArtinSchreierTheory.classMap p (algebraMap K E)) (hclass q).symm).trans hz
  have hkernelFinite : Finite (ArtinSchreierTheory.classMap p (algebraMap K E)).ker :=
    ArtinSchreierTheory.finite_classMap_kernel p
  let f : W → (ArtinSchreierTheory.classMap p (algebraMap K E)).ker :=
    fun w => ⟨w.val, hsplit w.property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : (ArtinSchreierTheory.classMap p (algebraMap K E)).ker => z.val) h
  have hcard : Nat.card W ≤ Nat.card (ArtinSchreierTheory.classMap p (algebraMap K E)).ker :=
    Nat.card_le_card_of_injective f hf
  refine ⟨E.toIntermediateField, E.finiteDimensional, hEab, hEp, hEN, ?_⟩
  exact hcard.trans (ArtinSchreierTheory.card_classMap_kernel_le_finrank p K E hEp)

end FunctionField
