/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
public import Nyll.ClassFieldTheory.Algebra.CyclicOrderCorrection
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantGaloisRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantGaloisTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantFieldExtension
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteConstantsInClosure
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantTowerDecompositionKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
public import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# Constant corrections of decomposition automorphisms

In a sufficiently large actual constant compositum, a decomposition
automorphism can be corrected by an automorphism fixing the original upper
field. The correction preserves its restriction and forces its action on the
constants to retain a prescribed order divisor. The correcting automorphism
comes from the exact image of the actual decomposition group on constants.
Taking the corrected cyclic fixed field then produces a concrete auxiliary
base over which adjoining these constants recovers the entire compositum.
-/

@[expose] public section

noncomputable section

namespace FunctionField

open AlgebraicCurve
open scoped AlgebraicCurve.Place

section FixedField

variable {k K Ω : Type*} [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : FiniteGaloisIntermediateField K Ω)
    (C : IntermediateField k Ω) [FiniteDimensional k C]

/-- When constant restriction detects the order of an automorphism, adjoining
the actual constants to its cyclic fixed field recovers the entire compositum. -/
theorem constantGaloisTower_fixedField_adjoin_eq_top
    (τ : Gal((IntermediateField.adjoin L (C : Set Ω))/K))
    (horder : orderOf (AlgEquiv.restrictNormalHom L τ) ∣
      orderOf (constantGaloisTowerRestriction L C τ)) :
    let _ : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
    IntermediateField.adjoin (IntermediateField.fixedField (Subgroup.zpowers τ))
      (Set.range (constantEmbedding (K := L) C)) = ⊤ := by
  intro hkLΩ
  let E := IntermediateField.adjoin L (C : Set Ω)
  have : FiniteDimensional K E := finiteDimensional_constantExtension_over_base L C
  have : IsGalois K E := isGalois_constantExtension_over_base L C
  let H : Subgroup Gal(E/K) := Subgroup.zpowers τ
  let F : IntermediateField K E := IntermediateField.fixedField H
  let B : IntermediateField K E :=
    IntermediateField.adjoin K (Set.range (constantEmbedding (K := L) C))
  let R : Gal(E/K) →* Gal(C/k) := constantGaloisTowerRestriction L C
  have hfaithful : Set.InjOn R H :=
    ClassFieldTheory.injOn_zpowers_of_jointly_injective_orderOf_dvd
      (AlgEquiv.restrictNormalHom L) R (constantGaloisTower_restrictions_injective L C)
      τ horder
  have hfix : (F ⊔ B).fixingSubgroup = ⊥ := by
    rw [IntermediateField.fixingSubgroup_sup,
      IntermediateField.fixingSubgroup_fixedField]
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro σ hσ
    have hσC : R σ = 1 := by
      apply AlgEquiv.ext
      intro c
      apply (constantEmbedding (K := L) C).injective
      calc
        constantEmbedding (K := L) C (R σ c) =
            σ (constantEmbedding (K := L) C c) :=
          constantGaloisTowerRestriction_commutes L C σ c
        _ = constantEmbedding (K := L) C c :=
          (IntermediateField.mem_fixingSubgroup_iff B σ).mp hσ.2
            (constantEmbedding (K := L) C c)
            (IntermediateField.subset_adjoin K _ ⟨c, rfl⟩)
    exact hfaithful hσ.1 (Subgroup.one_mem H) (hσC.trans (map_one R).symm)
  have hgen : F ⊔ B = ⊤ := by
    calc
      F ⊔ B = IntermediateField.fixedField (F ⊔ B).fixingSubgroup :=
        (IsGalois.fixedField_fixingSubgroup (F ⊔ B)).symm
      _ = IntermediateField.fixedField (⊥ : Subgroup Gal(E/K)) :=
        congrArg IntermediateField.fixedField hfix
      _ = ⊤ := IntermediateField.fixedField_bot
  apply IntermediateField.restrictScalars_injective K
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.restrictScalars_top]
  exact hgen

end FixedField

private theorem restrictNormalHom_mul_of_fixes_field {F M E : Type*}
    [Field F] [Field M] [Field E] [Algebra F M] [Algebra F E] [Algebra M E]
    [IsScalarTower F M E] [Normal F M] (δ : Gal(E/M)) (ρ : Gal(E/F)) :
    AlgEquiv.restrictNormalHom M (δ.restrictScalars F * ρ) =
      AlgEquiv.restrictNormalHom M ρ := by
  have hδ : AlgEquiv.restrictNormalHom M (δ.restrictScalars F) = 1 := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap M E).injective
    calc
      algebraMap M E (AlgEquiv.restrictNormalHom M (δ.restrictScalars F) x) =
          δ.restrictScalars F (algebraMap M E x) :=
        AlgEquiv.restrictNormal_commutes (δ.restrictScalars F) M x
      _ = δ (algebraMap M E x) := rfl
      _ = algebraMap M E x := δ.commutes x
      _ = algebraMap M E ((1 : Gal(M/F)) x) := rfl
  rw [map_mul, hδ, one_mul]

private theorem exists_corrected_decomposition_automorphism
    {k K L E G : Type*} [Field k] [Field K] [Field L] [Field E] [Group G]
    [Algebra k K] [Algebra k L] [Algebra k E] [Algebra K L] [Algebra K E] [Algebra L E]
    [IsScalarTower k K E] [IsScalarTower k L E] [IsScalarTower K L E]
    [Normal K L] [FiniteDimensional K E] [FiniteDimensional L E]
    (W : Place k E) (ρ : IdeleGroup.decompositionGroup (K := K) W)
    (δ : IdeleGroup.decompositionGroup (K := L) W)
    (R : Gal(E/K) →* G) (η : G) (m : ℕ)
    (hδ : R (δ.1.restrictScalars K) = η) (hη : m ∣ orderOf (η * R ρ.1)) :
    ∃ τ : IdeleGroup.decompositionGroup (K := K) W,
      AlgEquiv.restrictNormalHom L τ.1 = AlgEquiv.restrictNormalHom L ρ.1 ∧
        m ∣ orderOf (R τ.1) := by
  let τ := δ.1.restrictScalars K * ρ.1
  have hτ : τ ∈ IdeleGroup.decompositionGroup (K := K) W := by
    change (SemilinearAut.ofAlgAut (δ.1.restrictScalars k) *
      SemilinearAut.ofAlgAut (ρ.1.restrictScalars k)) • W = W
    rw [mul_smul, IdeleGroup.decompositionGroup_smul_eq W ρ]
    exact IdeleGroup.decompositionGroup_smul_eq W δ
  refine ⟨⟨τ, hτ⟩, restrictNormalHom_mul_of_fixes_field δ.1 ρ.1, ?_⟩
  change m ∣ orderOf (R (δ.1.restrictScalars K * ρ.1))
  rw [map_mul, hδ]
  exact hη

private theorem exists_frobenius_order_correction
    {k C : Type*} [Field k] [Field C] [Algebra k C] [Fintype k] [FiniteDimensional k C]
    (r m n s : ℕ) (hs : 0 < s) (hn : n = m * s.factorial)
    (hdegree : Module.finrank k C = r * n) (γ : Gal(C/k)) :
    let g := FiniteField.frobeniusAlgEquivOfAlgebraic k C
    ∃ η : Gal(C/k), η ∈ Subgroup.zpowers (g ^ s) ∧ r * m ∣ orderOf (η * γ) := by
  intro g
  let : Finite C := Module.finite_of_finite k
  have hg : orderOf g = (r * m) * s.factorial := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hdegree, hn, ← mul_assoc]
  have hγ : γ ∈ Subgroup.zpowers g := by
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k C).surjective γ
    rw [← hi]
    exact Subgroup.pow_mem (Subgroup.zpowers g) (Subgroup.mem_zpowers g) i.val
  exact ClassFieldTheory.exists_zpowers_mul_orderOf_dvd g (r * m) s hs hg γ hγ

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsSepClosed Ω] (L : FiniteGaloisIntermediateField K Ω)

/-- A correction fixing `L` preserves a decomposition automorphism's
restriction to `L`, while retaining the requested factor in the order of its
actual constant action. -/
theorem exists_constantDecomposition_corrected_lift (n : ℕ) [NeZero n] :
    let _ : Algebra (RatFunc k) L :=
      ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower (RatFunc k) K L :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) L :=
      IsScalarTower.to₁₂₄ k (RatFunc k) K L
    let _ : FunctionField k L := FiniteDimensional.trans (RatFunc k) K L
    let _ : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
    let _ : Algebra.EssFiniteType k L := essFiniteType k L
    let _ : Finite (algebraicClosure k L) :=
      FieldTheory.finite_algebraicClosure_of_finite_base k L
    let _ : IsScalarTower k (algebraicClosure k L) Ω :=
      IsScalarTower.to₁₂₄ k (algebraicClosure k L) L Ω
    let C : IntermediateField k Ω :=
      (finiteConstantsInClosure (algebraicClosure k L) Ω n).toIntermediateField.restrictScalars k
    let _ : FiniteDimensional k C := FiniteDimensional.trans k (algebraicClosure k L)
      (finiteConstantsInClosure (algebraicClosure k L) Ω n).toIntermediateField
    let E := fullConstantDegreeStage k L Ω n
    let _ : IsScalarTower k K E := IsScalarTower.to₁₂₄ k K L E
    let _ : FiniteDimensional K E := finiteDimensional_constantExtension_over_base L C
    let R : Gal(E/K) →* Gal(C/k) := constantGaloisTowerRestriction L C
    ∀ (W : Place k E) (m : ℕ), n = m * (W.restrict L).deg.factorial →
      ∀ ρ : IdeleGroup.decompositionGroup (K := K) W,
        ∃ τ : IdeleGroup.decompositionGroup (K := K) W,
          AlgEquiv.restrictNormalHom L τ.1 = AlgEquiv.restrictNormalHom L ρ.1 ∧
            m ∣ orderOf (R τ.1) := by
  intro aRL hRKL hkRL hLfield hkLΩ hess hA hkAΩ C hCfinite E hkKE hKEfinite R W m hn ρ
  let A := algebraicClosure k L
  let D := (finiteConstantsInClosure A Ω n).toIntermediateField
  let mAD : Module A D := (inferInstance : Algebra A D).toModule
  have hkAD : IsScalarTower k A D := IntermediateField.isScalarTower D
  have hfreeAD : Module.Free A D := Module.Free.of_divisionRing A D
  let _ : Fintype k := Fintype.ofFinite k
  let r : ℕ := Module.finrank k A
  let s : ℕ := (W.restrict L).deg
  have hs : 0 < s := by
    have : IsCurveOver k L := isCurveOver k L
    have : FiniteDimensional k (W.restrict L).ResidueField :=
      IsCurveOver.finite_residueField (W.restrict L)
    exact Module.finrank_pos
  have hdegree : Module.finrank k C = r * n := by
    change Module.finrank k D = r * n
    have hmul : Module.finrank k A * Module.finrank A D = Module.finrank k D :=
      Module.finrank_mul_finrank k A D
    have hdim : Module.finrank A D = n := finrank_finiteConstantsInClosure A Ω n
    exact hmul.symm.trans (congrArg (fun d : ℕ => r * d) hdim)
  obtain ⟨η, hη, horder⟩ := exists_frobenius_order_correction r m n s hs hn hdegree (R ρ.1)
  obtain ⟨δ, hδ, hδC⟩ :=
    exists_constantDecomposition_frobeniusPower_lift k L Ω n W η hη
  have hRestriction : R (δ.restrictScalars K) = η :=
    (constantGaloisTowerRestriction_restrictScalars L C δ).trans hδC
  exact exists_corrected_decomposition_automorphism W ρ ⟨δ, hδ⟩ R η m hRestriction
    ((dvd_mul_left m r).trans horder)


/-- Every actual decomposition automorphism admits a lift to a finite constant
compositum whose cyclic fixed field generates that compositum after adjoining
the actual constants. The extension degree and the upper place are constructed.
-/
theorem exists_constantDecomposition_auxiliaryField
    (w : Place k L) (σ : IdeleGroup.decompositionGroup (K := K) w) :
    ∃ n : ℕ, ∃ _ : NeZero n,
      let _ : Algebra (RatFunc k) L :=
        ((algebraMap K L).comp (algebraMap (RatFunc k) K)).toAlgebra
      let _ : IsScalarTower (RatFunc k) K L :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      let _ : IsScalarTower k (RatFunc k) L :=
        IsScalarTower.to₁₂₄ k (RatFunc k) K L
      let _ : FunctionField k L := FiniteDimensional.trans (RatFunc k) K L
      let _ : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
      let _ : Algebra.EssFiniteType k L := essFiniteType k L
      let _ : Finite (algebraicClosure k L) :=
        FieldTheory.finite_algebraicClosure_of_finite_base k L
      let _ : IsScalarTower k (algebraicClosure k L) Ω :=
        IsScalarTower.to₁₂₄ k (algebraicClosure k L) L Ω
      let C : IntermediateField k Ω :=
        (finiteConstantsInClosure (algebraicClosure k L) Ω n).toIntermediateField.restrictScalars k
      let _ : FiniteDimensional k C := FiniteDimensional.trans k (algebraicClosure k L)
        (finiteConstantsInClosure (algebraicClosure k L) Ω n).toIntermediateField
      let E := fullConstantDegreeStage k L Ω n
      let _ : IsScalarTower k K E := IsScalarTower.to₁₂₄ k K L E
      let _ : FiniteDimensional K E := finiteDimensional_constantExtension_over_base L C
      let iC : C →ₐ[k] E := constantEmbedding (K := L) C
      ∃ W : Place k E, ∃ τ : IdeleGroup.decompositionGroup (K := K) W,
        W.restrict L = w ∧ AlgEquiv.restrictNormalHom L τ.1 = σ.1 ∧
          IntermediateField.adjoin (IntermediateField.fixedField (Subgroup.zpowers τ.1))
            (Set.range iC) = ⊤ := by
  let n : ℕ := orderOf σ.1 * w.deg.factorial
  have hn : NeZero n := ⟨Nat.mul_ne_zero (Nat.ne_of_gt (orderOf_pos σ.1))
    (Nat.factorial_ne_zero w.deg)⟩
  refine ⟨n, hn, ?_⟩
  intro aRL hRKL hkRL hLfield hkLΩ hess hA hkAΩ C hCfinite E hkKE hKEfinite iC
  have hKEgalois : IsGalois K E := isGalois_constantExtension_over_base L C
  obtain ⟨W, hW⟩ := Place.exists_restrict_eq (M := E) w
  let σW : IdeleGroup.decompositionGroup (K := K) (W.restrict L) :=
    ⟨σ.1, by rw [hW]; exact σ.2⟩
  obtain ⟨ρ, hρ⟩ := IdeleGroup.exists_decompositionGroup_lift (K := K) (L := L) W σW
  have hdegree : n = orderOf σ.1 * (W.restrict L).deg.factorial := by
    rw [hW]
  obtain ⟨τ, hτ, horder⟩ :=
    exists_constantDecomposition_corrected_lift k K Ω L n W (orderOf σ.1) hdegree ρ
  have hrestrict : AlgEquiv.restrictNormalHom L τ.1 = σ.1 := hτ.trans hρ
  refine ⟨W, τ, hW, hrestrict, ?_⟩
  let R : Gal(E/K) →* Gal(C/k) := constantGaloisTowerRestriction L C
  have horder' : orderOf (AlgEquiv.restrictNormalHom L τ.1) ∣ orderOf (R τ.1) :=
    (congrArg orderOf hrestrict).symm ▸ horder
  exact constantGaloisTower_fixedField_adjoin_eq_top L C τ.1 horder'

end FunctionField
