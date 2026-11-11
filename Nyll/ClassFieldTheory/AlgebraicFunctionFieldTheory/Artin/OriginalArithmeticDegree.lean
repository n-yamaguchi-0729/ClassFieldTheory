/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteConstantDegreeReindex
public import Nyll.SchemeTheory.FunctionFields.GeometricFullConstants
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticNormalizer
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# The original arithmetic projection and normalized ray degree

The arithmetic label of an original field-source automorphism is its literal
constant restriction, up to the existing inner base-point correction. The
canonical Frobenius degree kills that correction. If the original finite base
is already the full constant field, its degree is exactly the normalized
degree used by ray reconstruction. The comparison uses the actual inclusions
of both constant closures into the same ambient field.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open LocalClassFieldTheory ClassFormation

universe u

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- When every actual algebraic constant belongs to the specified base,
normalizing by the full constants leaves the original arithmetic degree
unchanged. No equality of constant-field types is assumed. -/
theorem fullConstantDegreeData_eq_absoluteConstantDegree
    (hfull : ∀ x : K, IsAlgebraic k x → x ∈ (algebraMap k K).range)
    (σ : Gal(Ω/K)) :
    (fullConstantDegreeData k K Ω).degree σ = absoluteConstantDegree k K Ω σ := by
  let C := algebraicClosure k K
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite C := FieldTheory.finite_algebraicClosure_of_finite_base k K
  have hs : Function.Surjective (Algebra.ofId k C) := by
    intro c
    obtain ⟨a, ha⟩ := hfull (c : K) (mem_algebraicClosure_iff.mp c.property)
    exact ⟨a, Subtype.ext ha⟩
  let b : k ≃ₐ[k] C := AlgEquiv.ofBijective (Algebra.ofId k C)
    ⟨(algebraMap k C).injective, hs⟩
  let τ : C ≃+* k := b.symm.toRingEquiv
  have hτ (c : C) : algebraMap k K (τ c) = (c : K) :=
    congrArg (fun x : C => (x : K)) (b.apply_symm_apply c)
  change absoluteConstantDegree C K Ω σ = absoluteConstantDegree k K Ω σ
  exact absoluteConstantDegree_eq_of_scalarRingEquiv C k K Ω τ hτ σ

end FunctionField

namespace AlgebraicGeometry.FiniteEtale

variable (k F Ω : Type u) [Field k] [Finite k] [Field F] [Field Ω]
    [Algebra k F] [Algebra k Ω] [Algebra F Ω] [IsScalarTower k F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (p : Spec (.of F) ⟶ X)

/-- Frobenius degree of the original marked arithmetic fundamental-group
projection, using the actual constant closure in the supplied source field. -/
def originalArithmeticDegree : π₁ᵉᵗ(ξ F Ω ≫ p) →ₜ* ZHatMul := by
  let _ : Fintype k := Fintype.ofFinite k
  have : IsAlgClosed (separableClosure k Ω) :=
    IsAlgClosure.isAlgClosed (R := k) (K := separableClosure k Ω)
  exact (residueAbsoluteDegreeIn k (separableClosure k Ω)).comp
    (arithmeticFundamentalGroupHom k (separableClosure k Ω) f (ξ F Ω ≫ p))

omit [Algebra k F] [IsScalarTower k F Ω] [IsSepClosure F Ω] [IsIntegral X] in
/-- Relabeling the original finite-field arithmetic quotient by its
canonical Frobenius degree leaves its actual geometric kernel unchanged. -/
theorem originalArithmeticDegree_ker :
    (originalArithmeticDegree k F Ω f p).toMonoidHom.ker =
      (arithmeticFundamentalGroupHom k (separableClosure k Ω) f
        (ξ F Ω ≫ p)).toMonoidHom.ker := by
  let _ : Fintype k := Fintype.ofFinite k
  have : IsAlgClosed (separableClosure k Ω) :=
    IsAlgClosure.isAlgClosed (R := k) (K := separableClosure k Ω)
  apply Subgroup.ext
  intro γ
  change residueAbsoluteDegreeIn k (separableClosure k Ω)
      (arithmeticFundamentalGroupHom k (separableClosure k Ω) f (ξ F Ω ≫ p) γ) = 1 ↔
    arithmeticFundamentalGroupHom k (separableClosure k Ω) f (ξ F Ω ≫ p) γ = 1
  constructor
  · intro h
    apply (residueAbsoluteFrobeniusEquivIn k (separableClosure k Ω)).symm.injective
    exact h.trans (map_one (residueAbsoluteDegreeIn k (separableClosure k Ω))).symm
  · intro h
    rw [h, map_one]

/-- Measuring the original arithmetic label in any supplied closure of the
finite constants gives the actual constant degree. The embedding of that
closure into the source field is constructed internally; it is not additional
marking data. -/
theorem arithmeticDegree_fieldSource_eq_absoluteConstantDegree
    (κ : Type u) [Field κ] [Algebra k κ] [IsSepClosure k κ] [IsAlgClosed κ]
    (hbase : (ξ F Ω ≫ p) ≫ f = ξ k Ω) (σ : Gal(Ω/F)) :
    let _ : Fintype k := Fintype.ofFinite k
    residueAbsoluteDegreeIn k κ
        (arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ p)
          (fieldSourceAbsoluteGaloisHom F Ω p σ)) =
      FunctionField.absoluteConstantDegree k F Ω σ := by
  intro hk
  have : IsAlgClosed (separableClosure k Ω) :=
    IsAlgClosure.isAlgClosed (R := k) (K := separableClosure k Ω)
  let e : κ ≃ₐ[k] separableClosure k Ω :=
    IsSepClosure.equiv k κ (separableClosure k Ω)
  let ι : κ →ₐ[k] Ω := (separableClosure k Ω).val.comp e.toAlgHom
  let : Algebra κ Ω := ι.toRingHom.toAlgebra
  let : IsScalarTower k κ Ω :=
    IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  let δ : Gal(κ/k) := (σ.restrictScalars k).restrictNormal κ
  have hδ : AlgEquiv.autCongr e δ =
      FunctionField.absoluteConstantRestriction k F Ω σ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change (e (δ (e.symm x)) : Ω) =
      (FunctionField.absoluteConstantRestriction k F Ω σ x : Ω)
    calc
      (e (δ (e.symm x)) : Ω) = σ (e (e.symm x) : Ω) :=
        (σ.restrictScalars k).restrictNormal_commutes κ (e.symm x)
      _ = σ (x : Ω) :=
        congrArg (fun y : separableClosure k Ω => σ (y : Ω)) (e.apply_symm_apply x)
      _ = (FunctionField.absoluteConstantRestriction k F Ω σ x : Ω) :=
        ((σ.restrictScalars k).restrictNormal_commutes (separableClosure k Ω) x).symm
  have hd := residueAbsoluteDegreeIn_semilinear_conjugation
    k κ (RingEquiv.refl k) e.toRingEquiv (fun a => e.commutes a) δ
  change residueAbsoluteDegreeIn k (separableClosure k Ω) (AlgEquiv.autCongr e δ) =
    residueAbsoluteDegreeIn k κ δ at hd
  rw [hδ] at hd
  obtain ⟨α, hα⟩ := exists_fieldSource_arithmetic_restriction_label
    k F κ Ω f p hbase
  rw [hα, map_mul, map_mul, map_inv]
  change
    (residueAbsoluteDegreeIn k κ α * residueAbsoluteDegreeIn k κ δ) *
        (residueAbsoluteDegreeIn k κ α)⁻¹ =
      residueAbsoluteDegreeIn k (separableClosure k Ω)
        (FunctionField.absoluteConstantRestriction k F Ω σ)
  rw [mul_comm (residueAbsoluteDegreeIn k κ α), mul_assoc, mul_inv_cancel, mul_one]
  exact hd.symm

/-- On the original field source, arithmetic degree is its literal constant
degree. The existing inner base-point correction cancels in the abelian
Frobenius coordinate. -/
theorem originalArithmeticDegree_fieldSource
    (hbase : (ξ F Ω ≫ p) ≫ f = ξ k Ω) (σ : Gal(Ω/F)) :
    originalArithmeticDegree k F Ω f p (fieldSourceAbsoluteGaloisHom F Ω p σ) =
      FunctionField.absoluteConstantDegree k F Ω σ := by
  let _ : Fintype k := Fintype.ofFinite k
  have : IsAlgClosed (separableClosure k Ω) :=
    IsAlgClosure.isAlgClosed (R := k) (K := separableClosure k Ω)
  exact arithmeticDegree_fieldSource_eq_absoluteConstantDegree
    k F Ω f p (separableClosure k Ω) hbase σ

/-- The original arithmetic degree agrees with the marking in a common
constant closure on the entire original fundamental group. Surjectivity of
the actual generic field source promotes the representative calculation. -/
theorem originalArithmeticDegree_eq_commonClosure
    (κ : Type u) [Field κ] [Algebra k κ] [IsSepClosure k κ] [IsAlgClosed κ]
    [IsNormalIntegral X] [IsPreimmersion p] [IsDominant p] [QuasiCompact p]
    (hbase : (ξ F Ω ≫ p) ≫ f = ξ k Ω) :
    let _ : Fintype k := Fintype.ofFinite k
    originalArithmeticDegree k F Ω f p =
      (residueAbsoluteDegreeIn k κ).comp
        (arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ p)) := by
  intro hk
  apply ContinuousMonoidHom.ext
  intro γ
  obtain ⟨σ, rfl⟩ := fieldSourceAbsoluteGaloisHom_surjective F Ω p γ
  change originalArithmeticDegree k F Ω f p
      (fieldSourceAbsoluteGaloisHom F Ω p σ) =
    residueAbsoluteDegreeIn k κ
      (arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ p)
        (fieldSourceAbsoluteGaloisHom F Ω p σ))
  rw [originalArithmeticDegree_fieldSource k F Ω f p hbase]
  exact (arithmeticDegree_fieldSource_eq_absoluteConstantDegree
    k F Ω f p κ hbase σ).symm

/-- The native ray-degree marking and the common constant-closure marking
have exactly the same original geometric subgroup. No comparison of kernels
is assumed when passing between their first and mixed quotients. -/
theorem originalArithmeticDegree_ker_commonClosure
    (κ : Type u) [Field κ] [Algebra k κ] [IsSepClosure k κ] [IsAlgClosed κ]
    [IsNormalIntegral X] [IsPreimmersion p] [IsDominant p] [QuasiCompact p]
    (hbase : (ξ F Ω ≫ p) ≫ f = ξ k Ω) :
    (originalArithmeticDegree k F Ω f p).toMonoidHom.ker =
      (arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ p)).toMonoidHom.ker := by
  let _ : Fintype k := Fintype.ofFinite k
  rw [originalArithmeticDegree_eq_commonClosure k F Ω f p κ hbase]
  apply Subgroup.ext
  intro γ
  change residueAbsoluteDegreeIn k κ
      (arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ p) γ) = 1 ↔
    arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ p) γ = 1
  constructor
  · intro h
    apply (residueAbsoluteFrobeniusEquivIn k κ).symm.injective
    exact h.trans (map_one (residueAbsoluteDegreeIn k κ)).symm
  · intro h
    rw [h, map_one]

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F]

/-- The degree used by reconstruction agrees with the actual marked
arithmetic projection whenever the original finite base is the full constants. -/
theorem originalArithmeticDegree_fieldSource_fullConstants
    (hbase : (ξ F Ω ≫ p) ≫ f = ξ k Ω)
    (hfull : ∀ x : F, IsAlgebraic k x → x ∈ (algebraMap k F).range)
    (σ : Gal(Ω/F)) :
    originalArithmeticDegree k F Ω f p (fieldSourceAbsoluteGaloisHom F Ω p σ) =
      (FunctionField.fullConstantDegreeData k F Ω).degree σ := by
  rw [originalArithmeticDegree_fieldSource k F Ω f p hbase]
  exact (FunctionField.fullConstantDegreeData_eq_absoluteConstantDegree k F Ω hfull σ).symm

/-- For an original geometrically integral curve, its supplied generic
field automatically has the specified full constants. Thus the arithmetic
degree and normalized reconstruction degree coincide directly from the
original structural-map square. -/
theorem originalArithmeticDegree_fieldSource_geometricallyIntegral
    [GeometricallyIntegral f] [IsDominant p] [IsPreimmersion p]
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k F)))
    (σ : Gal(Ω/F)) :
    originalArithmeticDegree k F Ω f p (fieldSourceAbsoluteGaloisHom F Ω p σ) =
      (FunctionField.fullConstantDegreeData k F Ω).degree σ := by
  have hbase : (ξ F Ω ≫ p) ≫ f = ξ k Ω := by
    rw [Category.assoc, hp]
    rw [← Spec.map_comp]
    exact congrArg (fun h : k →+* Ω => Spec.map (CommRingCat.ofHom h))
      (IsScalarTower.algebraMap_eq k F Ω).symm
  exact originalArithmeticDegree_fieldSource_fullConstants k F Ω f p hbase
    (GeometricallyIntegral.genericFieldSource_fullConstants f p hp) σ

end AlgebraicGeometry.FiniteEtale

namespace FunctionField.RayClass

variable (k K : Type u) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]
    [Algebra k (SeparableClosure K)] [IsScalarTower k K (SeparableClosure K)]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (p : Spec (.of K) ⟶ X)

/-- The degree on the original ray quotient is the degree of the original
arithmetic fundamental-group label on every original Galois representative.
Thus the normalization required for local reconstruction comes from the
marked arithmetic projection. -/
theorem rayAbelianDegree_fieldSource
    (m : Modulus k K)
    (hbase : (Spec.algebraMap K (SeparableClosure K) ≫ p) ≫ f =
      Spec.algebraMap k (SeparableClosure K))
    (hfull : ∀ x : K, IsAlgebraic k x → x ∈ (algebraMap k K).range)
    (σ : Gal(SeparableClosure K/K)) :
    rayAbelianDegree m
        (QuotientGroup.mk' (artinRaySubgroup m)
          (localAbsoluteAbelianizationQuotientMap K σ)) =
      originalArithmeticDegree k K (SeparableClosure K) f p
        (fieldSourceAbsoluteGaloisHom K (SeparableClosure K) p σ) := by
  change (fullConstantDegreeData k K (SeparableClosure K)).degree σ = _
  exact (originalArithmeticDegree_fieldSource_fullConstants k K (SeparableClosure K)
    f p hbase hfull σ).symm

/-- The ray-degree comparison on an original geometrically integral curve
requires no additional full-constants or degree-compatibility hypothesis. -/
theorem rayAbelianDegree_fieldSource_geometricallyIntegral
    [GeometricallyIntegral f] [IsDominant p] [IsPreimmersion p]
    (m : Modulus k K)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (σ : Gal(SeparableClosure K/K)) :
    rayAbelianDegree m
        (QuotientGroup.mk' (artinRaySubgroup m)
          (localAbsoluteAbelianizationQuotientMap K σ)) =
      originalArithmeticDegree k K (SeparableClosure K) f p
        (fieldSourceAbsoluteGaloisHom K (SeparableClosure K) p σ) := by
  change (fullConstantDegreeData k K (SeparableClosure K)).degree σ = _
  exact (originalArithmeticDegree_fieldSource_geometricallyIntegral
    k K (SeparableClosure K) f p hp σ).symm

end FunctionField.RayClass
