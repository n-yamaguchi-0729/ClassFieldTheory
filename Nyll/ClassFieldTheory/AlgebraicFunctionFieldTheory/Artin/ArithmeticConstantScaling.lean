/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.OriginalArithmeticDegree
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# Original arithmetic degree through a finite constant extension

The original finite base remains fixed at every constant-extension stage.
Its arithmetic degree is the normalized degree multiplied by the actual
degree of the full constant field. This comparison uses the original
scalar maps and the literal inclusions of both constant closures into the
same ambient field.

Consequently an original arithmetic marking determines normalized degree
at stages with the same constant degree. No geometric-integrality
assumption over the smaller original finite base is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open LocalClassFieldTheory ClassFormation

universe u v

namespace LocalClassFieldTheory

/-- Finite-base scaling for a supplied tower of fields. The intermediate
field used by the intrinsic Frobenius theorem is the actual image of the
given scalar map; its canonical range equivalence preserves its degree. -/
theorem residueAbsoluteDegreeIn_restrictScalars_tower
    (k E Ω : Type*) [Field k] [Fintype k] [Field E] [Fintype E] [Field Ω]
    [Algebra k E] [FiniteDimensional k E]
    [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [Algebra.IsAlgebraic k Ω] [Algebra.IsAlgebraic E Ω] [IsAlgClosed Ω]
    (σ : Ω ≃ₐ[E] Ω) :
    residueAbsoluteDegreeIn k Ω (σ.restrictScalars k) =
      Multiplicative.ofAdd
        (Module.finrank k E • (residueAbsoluteDegreeIn E Ω σ).toAdd) := by
  let ι : E →ₐ[k] Ω := IsScalarTower.toAlgHom k E Ω
  let E' : IntermediateField k Ω := ι.fieldRange
  let b : E ≃ₐ[k] E' := ι.equivFieldRange
  have : FiniteDimensional k E' := Module.Finite.of_surjective
    b.toLinearMap b.surjective
  have : Finite E' := Finite.of_surjective b b.surjective
  let _ : Fintype E' := Fintype.ofFinite E'
  have hb (a : E) :
      (RingEquiv.refl Ω) (algebraMap E Ω a) = algebraMap E' Ω (b a) := rfl
  let σ' : Ω ≃ₐ[E'] Ω :=
    { σ.toRingEquiv with
      commutes' := fun a => by
        obtain ⟨a, rfl⟩ := b.surjective a
        change σ (algebraMap E Ω a) = algebraMap E Ω a
        exact σ.commutes a }
  have hdegree := residueAbsoluteDegreeIn_semilinear_conjugation
    E Ω b.toRingEquiv (RingEquiv.refl Ω) hb σ
  change residueAbsoluteDegreeIn E' Ω σ' = residueAbsoluteDegreeIn E Ω σ at hdegree
  have hrank : Module.finrank k E' = Module.finrank k E :=
    b.toLinearEquiv.finrank_eq.symm
  have h := residueAbsoluteDegreeIn_restrictScalars k Ω E' σ'
  change residueAbsoluteDegreeIn k Ω (σ.restrictScalars k) =
    Multiplicative.ofAdd
      (Module.finrank k E' • (residueAbsoluteDegreeIn E' Ω σ').toAdd) at h
  rw [hrank, hdegree] at h
  exact h

end LocalClassFieldTheory

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- The actual arithmetic degree over the original finite base is the
normalized full-constant degree scaled by the actual constant extension
degree. Both constant closures retain their literal embeddings into `Ω`. -/
theorem absoluteConstantDegree_eq_fullConstantDegree_scaled
    (σ : Gal(Ω/K)) :
    absoluteConstantDegree k K Ω σ =
      Multiplicative.ofAdd
        (Module.finrank k (algebraicClosure k K) •
          ((fullConstantDegreeData k K Ω).degree σ).toAdd) := by
  let C := algebraicClosure k K
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite C := FieldTheory.finite_algebraicClosure_of_finite_base k K
  let _ : Fintype k := Fintype.ofFinite k
  let _ : Fintype C := Fintype.ofFinite C
  have : IsAlgClosed (separableClosure k Ω) :=
    IsAlgClosure.isAlgClosed (R := k) (K := separableClosure k Ω)
  have : IsAlgClosed (separableClosure C Ω) :=
    IsAlgClosure.isAlgClosed (R := C) (K := separableClosure C Ω)
  have hmem (x : Ω) : x ∈ separableClosure C Ω ↔ x ∈ separableClosure k Ω := by
    rw [separableClosure.eq_restrictScalars_of_isSeparable k C Ω]
    rfl
  let e : separableClosure C Ω ≃+* separableClosure k Ω :=
    { toFun := fun x => ⟨x.val, (hmem x.val).mp x.property⟩
      invFun := fun x => ⟨x.val, (hmem x.val).mpr x.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have he (a : k) : e (algebraMap k (separableClosure C Ω) a) =
      algebraMap k (separableClosure k Ω) ((RingEquiv.refl k) a) := by
    apply Subtype.ext
    change algebraMap k Ω a = algebraMap k Ω a
    rfl
  let δ : separableClosure C Ω ≃ₐ[C] separableClosure C Ω :=
    absoluteConstantRestriction C K Ω σ
  let δk := δ.restrictScalars k
  let δ' : separableClosure k Ω ≃ₐ[k] separableClosure k Ω :=
    { e.symm.trans (δk.toRingEquiv.trans e) with
      commutes' := fun a => by
        change e (δk (e.symm (algebraMap k (separableClosure k Ω) a))) =
          algebraMap k (separableClosure k Ω) a
        have hpre : e.symm (algebraMap k (separableClosure k Ω) a) =
            algebraMap k (separableClosure C Ω) a := by
          apply e.injective
          rw [e.apply_symm_apply, he]
          rfl
        rw [hpre, δk.commutes, he]
        rfl
        }
  have hδ : δ' = absoluteConstantRestriction k K Ω σ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change ((δ (e.symm x) : separableClosure C Ω) : Ω) =
      ((absoluteConstantRestriction k K Ω σ x : separableClosure k Ω) : Ω)
    exact ((σ.restrictScalars C).restrictNormal_commutes
      (separableClosure C Ω) (e.symm x)).trans
        ((σ.restrictScalars k).restrictNormal_commutes (separableClosure k Ω) x).symm
  have : Algebra.IsAlgebraic k (separableClosure C Ω) :=
    Algebra.IsAlgebraic.trans k C (separableClosure C Ω)
  have htransport := residueAbsoluteDegreeIn_semilinear_conjugation
    k (separableClosure C Ω) (RingEquiv.refl k) e he δk
  change residueAbsoluteDegreeIn k (separableClosure k Ω) δ' =
    residueAbsoluteDegreeIn k (separableClosure C Ω) δk at htransport
  have hscale := residueAbsoluteDegreeIn_restrictScalars_tower
    k C (separableClosure C Ω) δ
  change residueAbsoluteDegreeIn k (separableClosure k Ω)
      (absoluteConstantRestriction k K Ω σ) =
    Multiplicative.ofAdd
      (Module.finrank k C • (residueAbsoluteDegreeIn C (separableClosure C Ω) δ).toAdd)
  rw [← hδ]
  exact htransport.trans hscale

end FunctionField

namespace AlgebraicGeometry.FiniteEtale

variable (k F Ω : Type u) [Field k] [Finite k] [Field F] [Field Ω]
    [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (p : Spec (.of F) ⟶ X)

/-- The arithmetic label of the original generic source uses the actual
constant degree of that source, even when the source curve has larger
constants than its original finite base. -/
theorem originalArithmeticDegree_fieldSource_scaled
    (hbase : (ξ F Ω ≫ p) ≫ f = ξ k Ω) (σ : Gal(Ω/F)) :
    originalArithmeticDegree k F Ω f p (fieldSourceAbsoluteGaloisHom F Ω p σ) =
      Multiplicative.ofAdd
        (Module.finrank k (algebraicClosure k F) •
          ((FunctionField.fullConstantDegreeData k F Ω).degree σ).toAdd) := by
  rw [originalArithmeticDegree_fieldSource k F Ω f p hbase]
  exact FunctionField.absoluteConstantDegree_eq_fullConstantDegree_scaled k F Ω σ

end AlgebraicGeometry.FiniteEtale

namespace FunctionField.RayClass

variable (k K : Type u) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]
    [Algebra k (SeparableClosure K)] [IsScalarTower k K (SeparableClosure K)]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (p : Spec (.of K) ⟶ X)

/-- On the same original Galois representative, the marked arithmetic
degree is the actual ray degree multiplied by the finite constant degree. -/
theorem originalArithmeticDegree_fieldSource_ray_scaled
    (m : Modulus k K)
    (hbase : (Spec.algebraMap K (SeparableClosure K) ≫ p) ≫ f =
      Spec.algebraMap k (SeparableClosure K))
    (σ : Gal(SeparableClosure K/K)) :
    originalArithmeticDegree k K (SeparableClosure K) f p
        (fieldSourceAbsoluteGaloisHom K (SeparableClosure K) p σ) =
      Multiplicative.ofAdd
        (Module.finrank k (algebraicClosure k K) •
          (rayAbelianDegree m
            (QuotientGroup.mk' (artinRaySubgroup m)
              (localAbsoluteAbelianizationQuotientMap K σ))).toAdd) := by
  change originalArithmeticDegree k K (SeparableClosure K) f p
      (fieldSourceAbsoluteGaloisHom K (SeparableClosure K) p σ) =
    Multiplicative.ofAdd
      (Module.finrank k (algebraicClosure k K) •
        ((fullConstantDegreeData k K (SeparableClosure K)).degree σ).toAdd)
  exact originalArithmeticDegree_fieldSource_scaled k K (SeparableClosure K) f p hbase σ

end FunctionField.RayClass

namespace FunctionField.RayClass

variable (k K : Type*) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Every normalized degree is represented in the original ray quotient,
because it is already represented in the original absolute Galois group. -/
theorem rayAbelianDegree_surjective (m : Modulus k K) :
    Function.Surjective (rayAbelianDegree m) := by
  intro z
  obtain ⟨σ, hσ⟩ := (fullConstantDegreeData k K (SeparableClosure K)).degree_surjective z
  exact ⟨QuotientGroup.mk' (artinRaySubgroup m)
    (localAbsoluteAbelianizationQuotientMap K σ), hσ⟩

/-- Equal positive constant degrees allow cancellation of the actual
arithmetic scaling, so a marked ray isomorphism preserves normalized degree. -/
theorem rayAbelianDegree_eq_of_scaled_eq
    {k' K' : Type*} [Field k'] [Finite k'] [Field K']
    [Algebra k' K'] [Algebra (RatFunc k') K'] [IsScalarTower k' (RatFunc k') K']
    [FunctionField k' K'] [AlgebraicCurve.HasPrincipalDivisors k' K']
    (m : Modulus k K) (m' : Modulus k' K')
    (hrank : Module.finrank k (algebraicClosure k K) =
      Module.finrank k' (algebraicClosure k' K'))
    (x : localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m)
    (y : localAbsoluteAbelianProfinite K' ⧸ artinRaySubgroup m')
    (hdegree :
      Multiplicative.ofAdd
          (Module.finrank k (algebraicClosure k K) • (rayAbelianDegree m x).toAdd) =
        Multiplicative.ofAdd
          (Module.finrank k' (algebraicClosure k' K') • (rayAbelianDegree m' y).toAdd)) :
    rayAbelianDegree m x = rayAbelianDegree m' y := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  have hn : 0 < Module.finrank k (algebraicClosure k K) := Module.finrank_pos
  apply Multiplicative.ext
  apply zHatMulNat_injective hn
  change Module.finrank k (algebraicClosure k K) • (rayAbelianDegree m x).toAdd =
    Module.finrank k (algebraicClosure k K) • (rayAbelianDegree m' y).toAdd
  rw [← hrank] at hdegree
  exact congrArg Multiplicative.toAdd hdegree

/-- An isomorphism preserving the original scaled arithmetic markings
also preserves their actual constant degrees and normalized ray degrees.
Equality of constant degrees is derived from the index of the original
arithmetic image, rather than added as an input. -/
theorem rayAbelianDegree_map_of_scaled_marking
    {k' K' : Type*} [Field k'] [Finite k'] [Field K']
    [Algebra k' K'] [Algebra (RatFunc k') K'] [IsScalarTower k' (RatFunc k') K']
    [FunctionField k' K'] [AlgebraicCurve.HasPrincipalDivisors k' K']
    (m : Modulus k K) (m' : Modulus k' K')
    (γ : (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) ≃*
      (localAbsoluteAbelianProfinite K' ⧸ artinRaySubgroup m'))
    (hmark : ∀ x,
      Multiplicative.ofAdd
          (Module.finrank k (algebraicClosure k K) • (rayAbelianDegree m x).toAdd) =
        Multiplicative.ofAdd
          (Module.finrank k' (algebraicClosure k' K') •
            (rayAbelianDegree m' (γ x)).toAdd)) :
    Module.finrank k (algebraicClosure k K) =
        Module.finrank k' (algebraicClosure k' K') ∧
      ∀ x, rayAbelianDegree m' (γ x) = rayAbelianDegree m x := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Algebra.EssFiniteType k' K' := essFiniteType k' K'
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  have : Finite (algebraicClosure k' K') :=
    FieldTheory.finite_algebraicClosure_of_finite_base k' K'
  let n := Module.finrank k (algebraicClosure k K)
  let n' := Module.finrank k' (algebraicClosure k' K')
  have hn : 0 < n := Module.finrank_pos
  have hn' : 0 < n' := Module.finrank_pos
  have hrange : (zHatMulNat n).toAddMonoidHom.range =
      (zHatMulNat n').toAddMonoidHom.range := by
    apply AddSubgroup.ext
    intro z
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨x, hx⟩ := rayAbelianDegree_surjective k K m (Multiplicative.ofAdd a)
      refine ⟨(rayAbelianDegree m' (γ x)).toAdd, ?_⟩
      have h := congrArg Multiplicative.toAdd (hmark x)
      rw [hx] at h
      exact h.symm.trans ha
    · rintro ⟨a, ha⟩
      obtain ⟨y, hy⟩ := rayAbelianDegree_surjective k' K' m' (Multiplicative.ofAdd a)
      obtain ⟨x, rfl⟩ := γ.surjective y
      refine ⟨(rayAbelianDegree m x).toAdd, ?_⟩
      have h := congrArg Multiplicative.toAdd (hmark x)
      rw [hy] at h
      exact h.trans ha
  have hrank : n = n' := by
    rw [← zHatMulNat_range_index n hn, ← zHatMulNat_range_index n' hn']
    exact congrArg (fun S : AddSubgroup ZHat => S.index) hrange
  refine ⟨hrank, fun x => ?_⟩
  exact (rayAbelianDegree_eq_of_scaled_eq k K m m' hrank x (γ x) (hmark x)).symm

end FunctionField.RayClass
