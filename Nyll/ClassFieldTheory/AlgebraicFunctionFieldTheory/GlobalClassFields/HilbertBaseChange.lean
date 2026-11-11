/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ConstantHilbertNorm
public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalFiniteNormSquare
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassField
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.OnePlaceNorm
public import Mathlib.FieldTheory.Galois.Abelian
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Actual embeddings between pointed Hilbert fields

The original finite norm sends the upper prescribed-splitting subgroup into
the lower subgroup. Global norm reciprocity then places the actual compositum
with the lower Hilbert field inside the upper Hilbert field. All inclusions
are inclusions of the original field images in the chosen separable closure.
-/

@[expose] public section

noncomputable section

universe u v w x y z

open AlgebraicCurve

namespace FunctionField

private theorem finiteNorm_comap_norm_le_of_injective
    {k : Type u} {K : Type v} {F : Type x} {L : Type w} {M : Type y}
    [Field k] [Finite k]
    [Field K] [Field F] [Field L] [Field M]
    [Algebra k K] [Algebra k F] [Algebra k L] [Algebra k M]
    [Algebra K F] [Algebra K L] [Algebra K M] [Algebra F M] [Algebra L M]
    [IsScalarTower k K F] [IsScalarTower k K L] [IsScalarTower k K M]
    [IsScalarTower k F M] [IsScalarTower k L M]
    [IsScalarTower K F M] [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [FiniteDimensional K F] [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional F M] [IsAbelianGalois F M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
    [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]
    (hr : Function.Injective
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp
        (AlgEquiv.restrictScalarsHom K : Gal(M/F) →* Gal(M/K)))) :
    ((IdeleClassGroup.norm (k := k) (K := K) (L := L)).range).comap
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := F)) ≤
      (IdeleClassGroup.norm (k := k) (K := F) (L := M)).range := by
  intro c hc
  apply (abelianFiniteArtin_eq_one_iff_mem_norm k F M c).mp
  apply hr
  have h := (abelianFiniteArtin_finiteNorm_restrictNormal
    (K := K) (F := F) (L := L) (M := M) c).trans
      ((abelianFiniteArtin_eq_one_iff_mem_norm k K L _).mpr hc)
  simpa only [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply, map_one] using h

variable {k : Type u} {K : Type v} {L : Type w}
    [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual finite norm respects the zero-modulus subgroup with the
specified splitting places. -/
theorem finiteNorm_splitRaySubgroup_zero_le [Algebra.IsSeparable K L]
    (S : Finset (Place k K)) (T : Finset (Place k L))
    (hTS : ∀ w ∈ T, w.restrict K ∈ S) :
    (RayClass.splitRaySubgroup 0 T).map
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L)) ≤
      RayClass.splitRaySubgroup 0 S := by
  apply Subgroup.map_le_iff_le_comap.mpr
  rw [RayClass.splitRaySubgroup]
  apply sup_le
  · intro c hc
    have hc0 : (IdeleClassGroup.divisorClass c).toAdd = 0 := by
      have hker : c ∈ (IdeleClassGroup.divisorClass (k := k) (K := L)).ker := by
        rw [IdeleClassGroup.divisorClass_ker]
        simpa only [RayClass.rayClassSubgroup, RayClass.congruenceSubgroup_zero,
          IdeleClassGroup.integralSubgroup] using hc
      exact congrArg Multiplicative.toAdd hker
    have hn0 : (IdeleClassGroup.divisorClass
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L) c)).toAdd = 0 := by
      rw [IdeleClassGroup.divisorClass_finiteNorm, hc0, map_zero]
    have hnker : IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L) c ∈
        (IdeleClassGroup.divisorClass (k := k) (K := K)).ker :=
      Multiplicative.ext hn0
    have hnray : IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L) c ∈
        RayClass.rayClassSubgroup (0 : RayClass.Modulus k K) := by
      rw [IdeleClassGroup.divisorClass_ker] at hnker
      simpa only [RayClass.rayClassSubgroup, RayClass.congruenceSubgroup_zero,
        IdeleClassGroup.integralSubgroup] using hnker
    exact (show RayClass.rayClassSubgroup 0 ≤ RayClass.splitRaySubgroup 0 S from
      le_sup_left) hnray
  · apply iSup_le
    intro w
    apply iSup_le
    intro hw
    rintro c ⟨x, rfl⟩
    change IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L)
      (QuotientGroup.mk (IdeleGroup.placeIdele w x)) ∈ RayClass.splitRaySubgroup 0 S
    rw [IdeleClassGroup.finiteNorm_mk, IdeleGroup.norm_placeIdele]
    exact RayClass.placeIdele_mem_splitRaySubgroup 0 S (hTS w hw)
      (IdeleGroup.localNorm (K := K) w x)

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [IsAbelianGalois K L]

private theorem finiteAbelian_adjoin_image
    {F : Type x} {E : Type y} {Ω : Type z} [Field F] [Field E] [Field Ω]
    [Algebra K F] [Algebra K E] [Algebra K Ω] [Algebra F Ω]
    [IsScalarTower K F Ω]
    [FiniteDimensional K F] [FiniteDimensional K E]
    [IsAbelianGalois K F] [IsAbelianGalois K E]
    (i : E →ₐ[K] Ω) :
    FiniteDimensional F (IntermediateField.adjoin F (i.fieldRange : Set Ω)) ∧
      IsAbelianGalois F (IntermediateField.adjoin F (i.fieldRange : Set Ω)) := by
  let iF : F →ₐ[K] Ω := IsScalarTower.toAlgHom K F Ω
  let A : IntermediateField K Ω := i.fieldRange
  let B : IntermediateField K Ω := iF.fieldRange
  have hAfinite : FiniteDimensional K A :=
    FiniteDimensional.of_surjective i.equivFieldRange.toLinearMap i.equivFieldRange.surjective
  have hBfinite : FiniteDimensional K B :=
    FiniteDimensional.of_surjective iF.equivFieldRange.toLinearMap iF.equivFieldRange.surjective
  have hAabelian : IsAbelianGalois K A :=
    IsAbelianGalois.of_algHom i.equivFieldRange.symm.toAlgHom
  have hBabelian : IsAbelianGalois K B :=
    IsAbelianGalois.of_algHom iF.equivFieldRange.symm.toAlgHom
  let M : IntermediateField F Ω :=
    IntermediateField.adjoin F (A : Set Ω)
  have hMrestrict : M.restrictScalars K = B ⊔ A := by
    calc
      M.restrictScalars K =
          (IntermediateField.adjoin B (A : Set Ω)).restrictScalars K :=
        IntermediateField.restrictScalars_adjoin_of_algEquiv iF.equivFieldRange
          (funext fun _ => rfl) _
      _ = B ⊔ A := by
        rw [IntermediateField.restrictScalars_adjoin_eq_sup, IntermediateField.adjoin_self]
  let aKM : Algebra K M := IntermediateField.algebra' M
  let mKM : Module K M := aKM.toModule
  have hKMfinite : FiniteDimensional K M := by
    change FiniteDimensional K (M.restrictScalars K)
    rw [hMrestrict]
    infer_instance
  have hKMabelian : IsAbelianGalois K M := by
    change IsAbelianGalois K (M.restrictScalars K)
    rw [hMrestrict]
    infer_instance
  have hKLM : IsScalarTower K F M :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      Subtype.ext (IsScalarTower.algebraMap_apply K F Ω a))
  have hLMfinite : FiniteDimensional F M := FiniteDimensional.right K F M
  have hLMabelian : IsAbelianGalois F M := IsAbelianGalois.tower_top K F M
  exact ⟨hLMfinite, hLMabelian⟩

private theorem adjoin_image_restrict_injective
    {F : Type x} {E : Type y} {Ω : Type z} [Field F] [Field E] [Field Ω]
    [Algebra K F] [Algebra K E] [Algebra K Ω] [Algebra F Ω]
    [IsScalarTower K F Ω] [Normal K E] (i : E →ₐ[K] Ω) :
    let A : IntermediateField K Ω := i.fieldRange
    let M : IntermediateField F Ω := IntermediateField.adjoin F (A : Set Ω)
    let _ : Algebra K M := IntermediateField.algebra' M
    let _ : IsScalarTower K F M :=
      IsScalarTower.of_algebraMap_eq (fun a =>
        Subtype.ext (IsScalarTower.algebraMap_apply K F Ω a))
    let j : E →ₐ[K] M :=
      (IntermediateField.inclusion
        (show A ≤ M.restrictScalars K from
          IntermediateField.subset_adjoin F (A : Set Ω))).comp
        i.equivFieldRange.toAlgHom
    let _ : Algebra E M := j.toRingHom.toAlgebra
    let _ : IsScalarTower K E M :=
      IsScalarTower.of_algebraMap_eq (fun a => (j.commutes a).symm)
    Function.Injective
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E).comp
        (AlgEquiv.restrictScalarsHom K : Gal(M/F) →* Gal(M/K))) := by
  intro A M aKM hKFM j aEM hKEM σ τ h
  have hhom : σ.toAlgHom = τ.toAlgHom := by
    apply IntermediateField.adjoin_algHom_ext
    rintro x ⟨a, rfl⟩
    change σ (j a) = τ (j a)
    exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) E a).symm.trans
      ((congrArg j (DFunLike.congr_fun h a)).trans
        (AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) E a))
  exact AlgEquiv.ext fun a => DFunLike.congr_fun hhom a

private theorem finiteNorm_comap_norm_le_image
    (E : Type y) [Field E] [Algebra k E] [Algebra K E]
    [IsScalarTower k K E] [FiniteDimensional K E] [IsAbelianGalois K E]
    [HasPrincipalDivisors k E]
    (N : IntermediateField L (SeparableClosure L))
    [FiniteDimensional L N] [IsAbelianGalois L N]
    (H : Subgroup (IdeleClassGroup k L)) :
    let _ : Algebra K (SeparableClosure L) :=
      ((algebraMap L (SeparableClosure L)).comp (algebraMap K L)).toAlgebra
    let _ : IsScalarTower K L (SeparableClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : Algebra k (SeparableClosure L) :=
      ((algebraMap L (SeparableClosure L)).comp (algebraMap k L)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure L) :=
      ((algebraMap L (SeparableClosure L)).comp (algebraMap (RatFunc k) L)).toAlgebra
    let _ : IsScalarTower k L (SeparableClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) L (SeparableClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun a =>
        congrArg (algebraMap L (SeparableClosure L))
          (IsScalarTower.algebraMap_apply k (RatFunc k) L a))
    ∀ i : E →ₐ[K] SeparableClosure L,
      H ≤ ((IdeleClassGroup.norm (k := k) (K := K) (L := E)).range).comap
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L)) →
      (IdeleClassGroup.norm (k := k) (K := L) (L := N)).range ≤ H →
      i.fieldRange ≤ N.restrictScalars K := by
  intro aKΩ hKLΩ akΩ aRΩ hkLΩ hRLΩ hkRΩ i hSource hTarget
  have hkKΩ : IsScalarTower k K (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      congrArg (algebraMap L (SeparableClosure L))
        (IsScalarTower.algebraMap_apply k K L a))
  let A : IntermediateField K (SeparableClosure L) := i.fieldRange
  let M : IntermediateField L (SeparableClosure L) :=
    IntermediateField.adjoin L (A : Set (SeparableClosure L))
  let aKM : Algebra K M := IntermediateField.algebra' M
  let mKM : Module K M := aKM.toModule
  have hKLM : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      Subtype.ext (IsScalarTower.algebraMap_apply K L (SeparableClosure L) a))
  have hMextension := finiteAbelian_adjoin_image (K := K) (F := L) (E := E)
    (Ω := SeparableClosure L) i
  have hLMfinite : FiniteDimensional L M := hMextension.1
  have hLMabelian : IsAbelianGalois L M := hMextension.2
  have hkKM : IsScalarTower k K M :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      Subtype.ext (IsScalarTower.algebraMap_apply k K (SeparableClosure L) a))
  let j : E →ₐ[K] M :=
    (IntermediateField.inclusion
      (show A ≤ M.restrictScalars K from
        IntermediateField.subset_adjoin L (A : Set (SeparableClosure L)))).comp
      i.equivFieldRange.toAlgHom
  let aH₀M : Algebra E M := j.toRingHom.toAlgebra
  let sH₀M : SMul E M := aH₀M.toSMul
  have hKH₀M : IsScalarTower K E M :=
    IsScalarTower.of_algebraMap_eq (fun a => (j.commutes a).symm)
  have hkH₀M : IsScalarTower k E M :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      rw [IsScalarTower.algebraMap_apply k K E,
        IsScalarTower.algebraMap_apply k K M]
      exact (j.commutes (algebraMap k K a)).symm)
  have hpM : HasPrincipalDivisors k M :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k L M).toHasPrincipalDivisors
  let r : Gal(M/L) →* Gal(E/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) E).comp (AlgEquiv.restrictScalarsHom K)
  have hr : Function.Injective r :=
    adjoin_image_restrict_injective (K := K) (F := L) (E := E)
      (Ω := SeparableClosure L) i
  have hNorm :
      ((IdeleClassGroup.norm (k := k) (K := K) (L := E)).range).comap
          (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L)) ≤
        (IdeleClassGroup.norm (k := k) (K := L) (L := M)).range :=
    finiteNorm_comap_norm_le_of_injective (k := k) (K := K) (F := L) (L := E) (M := M) hr
  have hMsub : M ≤ N :=
    (finiteAbelian_norm_range_le_iff k L N M).mp
      (hTarget.trans (hSource.trans hNorm))
  intro x hx
  exact hMsub (IntermediateField.subset_adjoin L (A : Set (SeparableClosure L)) hx)

/-- Every image of the lower pointed Hilbert field lies in the upper
pointed Hilbert field after a finite abelian base extension. In particular,
the containment does not depend on a choice of Hilbert-field embedding. -/
theorem hilbertClassFieldImage_le_of_finiteAbelian_baseChange
    (S : Finset (Place k K)) (hS : S.Nonempty)
    (T : Finset (Place k L)) (hT : T.Nonempty)
    (hTS : ∀ w ∈ T, w.restrict K ∈ S) :
    let H₀ := hilbertClassField k K S hS
    let H₁ := hilbertClassField k L T hT
    let _ : Algebra K (SeparableClosure L) :=
      ((algebraMap L (SeparableClosure L)).comp (algebraMap K L)).toAlgebra
    let _ : IsScalarTower K L (SeparableClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∀ i : H₀.val →ₐ[K] SeparableClosure L,
      i.fieldRange ≤ H₁.val.restrictScalars K := by
  intro H₀ H₁ aKΩ hKLΩ i
  have hSplit : (RayClass.splitRaySubgroup 0 T).map
      (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L)) ≤
      RayClass.splitRaySubgroup 0 S :=
    finiteNorm_splitRaySubgroup_zero_le (k := k) (K := K) (L := L) S T hTS
  let mKΩ : Module K (SeparableClosure L) := aKΩ.toModule
  let akSK : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRSK : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKSK : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKSK : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRSK : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K a))
  have hpH₀ : HasPrincipalDivisors k H₀.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H₀.val).toHasPrincipalDivisors
  let akΩ : Algebra k (SeparableClosure L) :=
    ((algebraMap L (SeparableClosure L)).comp (algebraMap k L)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure L) :=
    ((algebraMap L (SeparableClosure L)).comp (algebraMap (RatFunc k) L)).toAlgebra
  have hkLΩ : IsScalarTower k L (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRLΩ : IsScalarTower (RatFunc k) L (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      congrArg (algebraMap L (SeparableClosure L))
        (IsScalarTower.algebraMap_apply k (RatFunc k) L a))
  have hkKΩ : IsScalarTower k K (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      congrArg (algebraMap L (SeparableClosure L))
        (IsScalarTower.algebraMap_apply k K L a))
  have hpH₁ : HasPrincipalDivisors k H₁.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k L H₁.val).toHasPrincipalDivisors
  have hSplitNorm : RayClass.splitRaySubgroup 0 T ≤
      ((IdeleClassGroup.norm (k := k) (K := K) (L := H₀.val)).range).comap
        (IdeleClassGroup.finiteNorm (k := k) (K := K) (L := L)) := by
    rw [hilbertClassField_norm k K S hS]
    exact Subgroup.map_le_iff_le_comap.mp hSplit
  exact finiteNorm_comap_norm_le_image (k := k) (K := K) (L := L) H₀.val H₁.val
    (RayClass.splitRaySubgroup 0 T) i hSplitNorm (hilbertClassField_norm k L T hT).le

/-- A finite abelian base extension supplies an actual embedding of the
lower prescribed-splitting Hilbert field into the upper one. -/
theorem nonempty_hilbertClassField_baseChangeEmbedding
    (S : Finset (Place k K)) (hS : S.Nonempty)
    (T : Finset (Place k L)) (hT : T.Nonempty)
    (hTS : ∀ w ∈ T, w.restrict K ∈ S) :
    let H₀ := hilbertClassField k K S hS
    let H₁ := hilbertClassField k L T hT
    let _ : Algebra K H₁.val :=
      ((algebraMap L H₁.val).comp (algebraMap K L)).toAlgebra
    let _ : IsScalarTower K L H₁.val :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Nonempty (H₀.val →ₐ[K] H₁.val) := by
  intro H₀ H₁ aKH₁ hKLH₁
  let aKΩ : Algebra K (SeparableClosure L) :=
    ((algebraMap L (SeparableClosure L)).comp (algebraMap K L)).toAlgebra
  have hKLΩ : IsScalarTower K L (SeparableClosure L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let i : H₀.val →ₐ[K] SeparableClosure L := IsSepClosed.lift
  have hi : i.fieldRange ≤ H₁.val.restrictScalars K :=
    hilbertClassFieldImage_le_of_finiteAbelian_baseChange S hS T hT hTS i
  exact ⟨(IntermediateField.inclusion hi).comp i.equivFieldRange.toAlgHom⟩

/-- In any common overfield the original images of the pointed Hilbert
fields increase with the finite abelian base extension. Normality makes
this statement independent of all separable-closure choices. -/
theorem hilbertClassFieldImage_mono
    (S : Finset (Place k K)) (hS : S.Nonempty)
    (T : Finset (Place k L)) (hT : T.Nonempty)
    (hTS : ∀ w ∈ T, w.restrict K ∈ S)
    (Ω : Type z) [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] :
    let H₀ := hilbertClassField k K S hS
    let H₁ := hilbertClassField k L T hT
    let _ : Algebra K H₁.val :=
      ((algebraMap L H₁.val).comp (algebraMap K L)).toAlgebra
    let _ : IsScalarTower K L H₁.val :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∀ (i₀ : H₀.val →ₐ[K] Ω) (i₁ : H₁.val →ₐ[L] Ω),
      i₀.fieldRange ≤ (i₁.restrictScalars K).fieldRange := by
  intro H₀ H₁ aKH₁ hKLH₁ i₀ i₁
  obtain ⟨j⟩ := nonempty_hilbertClassField_baseChangeEmbedding S hS T hT hTS
  have hrange : i₀.fieldRange = ((i₁.restrictScalars K).comp j).fieldRange :=
    ClassFieldTheory.fieldRange_eq_of_normal i₀ ((i₁.restrictScalars K).comp j)
  rw [hrange]
  rintro x ⟨a, rfl⟩
  exact ⟨j a, rfl⟩

end FunctionField
