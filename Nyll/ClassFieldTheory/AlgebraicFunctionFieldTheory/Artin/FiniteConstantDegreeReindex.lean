/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteConstantDegree
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.SeparableClosure
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# Normalized arithmetic degree is independent of finite constant enlargement

An actual scalar-field isomorphism that keeps the embedded constants
identifies their separable closures by the identity on ambient elements.
The proved semilinear Frobenius comparison therefore preserves the original
constant degree. The full constants before and after a finite enlargement
have the same actual elements, so their normalized degrees coincide.
-/

@[expose] public section

noncomputable section

open ClassFormation LocalClassFieldTheory

namespace FunctionField


/-- Relabeling the same actual finite scalar subfield does not alter the
arithmetic degree of an original source automorphism. -/
theorem absoluteConstantDegree_eq_of_scalarRingEquiv
    (k₁ k₂ K Ω : Type*) [Field k₁] [Finite k₁] [Field k₂] [Finite k₂]
    [Field K] [Field Ω] [Algebra k₁ K] [Algebra k₂ K] [Algebra K Ω]
    [Algebra k₁ Ω] [Algebra k₂ Ω]
    [IsScalarTower k₁ K Ω] [IsScalarTower k₂ K Ω] [IsSepClosed Ω]
    (τ : k₁ ≃+* k₂)
    (hτ : ∀ c, algebraMap k₂ K (τ c) = algebraMap k₁ K c)
    (σ : Gal(Ω/K)) :
    absoluteConstantDegree k₁ K Ω σ = absoluteConstantDegree k₂ K Ω σ := by
  let _ : Fintype k₁ := Fintype.ofFinite k₁
  let _ : Fintype k₂ := Fintype.ofFinite k₂
  let : Algebra k₁ k₂ := τ.toRingHom.toAlgebra
  let τa : k₁ ≃ₐ[k₁] k₂ := { τ with commutes' := fun _ => rfl }
  have : FiniteDimensional k₁ k₂ := τa.toLinearEquiv.finiteDimensional
  have : IsScalarTower k₁ k₂ K :=
    IsScalarTower.of_algebraMap_eq (fun c => (hτ c).symm)
  have : IsScalarTower k₁ k₂ Ω := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k₁ Ω c = algebraMap k₂ Ω (τ c)
    rw [IsScalarTower.algebraMap_apply k₁ K Ω,
      IsScalarTower.algebraMap_apply k₂ K Ω, hτ c])
  have : IsAlgClosed (separableClosure k₁ Ω) :=
    IsAlgClosure.isAlgClosed (R := k₁) (K := separableClosure k₁ Ω)
  have : IsAlgClosed (separableClosure k₂ Ω) :=
    IsAlgClosure.isAlgClosed (R := k₂) (K := separableClosure k₂ Ω)
  have hmem (x : Ω) : x ∈ separableClosure k₁ Ω ↔ x ∈ separableClosure k₂ Ω := by
    rw [separableClosure.eq_restrictScalars_of_isSeparable k₁ k₂ Ω]
    rfl
  let e : separableClosure k₁ Ω ≃+* separableClosure k₂ Ω :=
    { toFun := fun x => ⟨x.val, (hmem x.val).mp x.property⟩
      invFun := fun x => ⟨x.val, (hmem x.val).mpr x.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have he (c : k₁) : e (algebraMap k₁ (separableClosure k₁ Ω) c) =
      algebraMap k₂ (separableClosure k₂ Ω) (τ c) := by
    apply Subtype.ext
    change algebraMap k₁ Ω c = algebraMap k₂ Ω (τ c)
    exact IsScalarTower.algebraMap_apply k₁ k₂ Ω c
  let δ := absoluteConstantRestriction k₁ K Ω σ
  let δ' : separableClosure k₂ Ω ≃ₐ[k₂] separableClosure k₂ Ω :=
    { e.symm.trans (δ.toRingEquiv.trans e) with
      commutes' := fun a => by
        change e (δ (e.symm (algebraMap k₂ (separableClosure k₂ Ω) a))) =
          algebraMap k₂ (separableClosure k₂ Ω) a
        have hpre : e.symm (algebraMap k₂ (separableClosure k₂ Ω) a) =
            algebraMap k₁ (separableClosure k₁ Ω) (τ.symm a) := by
          apply e.injective
          rw [e.apply_symm_apply, he, τ.apply_symm_apply]
        rw [hpre, δ.commutes, he, τ.apply_symm_apply] }
  have hδ : δ' = absoluteConstantRestriction k₂ K Ω σ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change ((δ (e.symm x) : separableClosure k₁ Ω) : Ω) =
      ((absoluteConstantRestriction k₂ K Ω σ x : separableClosure k₂ Ω) : Ω)
    exact ((σ.restrictScalars k₁).restrictNormal_commutes
      (separableClosure k₁ Ω) (e.symm x)).trans
        ((σ.restrictScalars k₂).restrictNormal_commutes (separableClosure k₂ Ω) x).symm
  have hd := residueAbsoluteDegreeIn_semilinear_conjugation
    k₁ (separableClosure k₁ Ω) τ e he δ
  change residueAbsoluteDegreeIn k₂ (separableClosure k₂ Ω) δ' =
    residueAbsoluteDegreeIn k₁ (separableClosure k₁ Ω) δ at hd
  change residueAbsoluteDegreeIn k₁ (separableClosure k₁ Ω) δ =
    residueAbsoluteDegreeIn k₂ (separableClosure k₂ Ω)
      (absoluteConstantRestriction k₂ K Ω σ)
  rw [← hδ]
  exact hd.symm

variable (k E K : Type*) [Field k] [Finite k] [Field E] [Finite E] [Field K]
  [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
  [Algebra.IsIntegral k E]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc E) K] [IsScalarTower E (RatFunc E) K] [FunctionField E K]

omit [Algebra.IsIntegral k E] in
/-- Normalizing by the actual full constants gives the same source degree
before and after any finite enlargement of the specified constants. -/
theorem fullConstantDegreeData_forgetConstants
    (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]
    (σ : Gal(Ω/K)) :
    (fullConstantDegreeData k K Ω).degree σ = (fullConstantDegreeData E K Ω).degree σ := by
  let C := algebraicClosure k K
  let D := algebraicClosure E K
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Algebra.EssFiniteType E K := essFiniteType E K
  have : Finite C := FieldTheory.finite_algebraicClosure_of_finite_base k K
  have : Finite D := FieldTheory.finite_algebraicClosure_of_finite_base E K
  have hmem (x : K) : x ∈ C ↔ x ∈ D := by
    change x ∈ algebraicClosure k K ↔ x ∈ algebraicClosure E K
    rw [algebraicClosure.eq_restrictScalars_of_isAlgebraic k E K]
    rfl
  let τ : C ≃+* D :=
    { toFun := fun x => ⟨x.val, (hmem x.val).mp x.property⟩
      invFun := fun x => ⟨x.val, (hmem x.val).mpr x.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  change absoluteConstantDegree C K Ω σ = absoluteConstantDegree D K Ω σ
  exact absoluteConstantDegree_eq_of_scalarRingEquiv C D K Ω τ (fun _ => rfl) σ

omit [Algebra.IsIntegral k E] in
/-- The original absolute abelian degree itself is unchanged, on every
original abelianized Galois element. -/
theorem absoluteAbelianDegree_forgetConstants :
    absoluteAbelianDegree k K = absoluteAbelianDegree E K := by
  apply ContinuousMonoidHom.ext
  intro a
  refine QuotientGroup.induction_on a ?_
  intro σ
  exact fullConstantDegreeData_forgetConstants k E K (SeparableClosure K) σ

end FunctionField
