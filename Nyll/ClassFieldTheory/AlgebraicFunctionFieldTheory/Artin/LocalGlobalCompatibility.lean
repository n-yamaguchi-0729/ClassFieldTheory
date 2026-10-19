/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Abelian
import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalConstantGeneratedCompatibility
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalFactor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalFactorRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalNormNaturality
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativeEmbeddedNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantDecompositionAuxiliaryField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionGalois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantGaloisRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.CyclicFixedFieldLift
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.OnePlaceNorm
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization

/-!
# Local and global reciprocity for finite abelian function-field extensions

Cyclic fixed fields and constructed constant extensions reduce the comparison
to the proved constant-generated case and the actual norm compatibility.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place
open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

namespace FunctionField

private theorem norm_placeIdele_of_restrict_eq
    {k K F : Type} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]
    [FiniteDimensional K F]
    (v : Place k K) (w : Place k F) (h : w.restrict K = v)
    (z : w.adicCompletionˣ) :
    IdeleGroup.norm (K := K) (L := F) (IdeleGroup.placeIdele w z) =
      IdeleGroup.placeIdele v (IdeleGroup.localNormOver v w h z) := by
  subst v
  exact IdeleGroup.norm_placeIdele w z

private theorem classNorm_placeIdele_of_restrict_eq
    {k K F : Type} [Field k] [Field K] [Field F]
    [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
    (v : Place k K) (w : Place k F) (h : w.restrict K = v)
    (z : w.adicCompletionˣ) :
    IdeleClassGroup.norm (k := k) (K := K) (L := F)
        (IdeleClassGroup.mk (k := k) (K := F) (IdeleGroup.placeIdele w z)) =
      IdeleClassGroup.mk (k := k) (K := K)
        (IdeleGroup.placeIdele v (IdeleGroup.localNormOver v w h z)) := by
  change IdeleClassGroup.norm (k := k) (K := K) (L := F)
      (QuotientGroup.mk (IdeleGroup.placeIdele w z)) =
    QuotientGroup.mk (IdeleGroup.placeIdele v (IdeleGroup.localNormOver v w h z))
  exact (IdeleClassGroup.norm_mk (k := k) (K := K) (L := F)
    (IdeleGroup.placeIdele w z)).trans
      (congrArg (QuotientGroup.mk : IdeleGroup k K → IdeleClassGroup k K)
        (norm_placeIdele_of_restrict_eq v w h z))

private theorem fixedField_adjoin_restrictScalars
    {K J Ω C : Type} [Field K] [Field J] [Field Ω] [Field C]
    [Algebra K J] [Algebra K Ω] [Algebra J Ω] [IsScalarTower K J Ω]
    (E : IntermediateField J Ω) [Algebra C E]
    (τ : Gal(E/K))
    (hgen : IntermediateField.adjoin (IntermediateField.fixedField (Subgroup.zpowers τ))
      (Set.range (algebraMap C E)) = ⊤) :
    let EI : IntermediateField K Ω := E.restrictScalars K
    let _ : Algebra C EI := (inferInstance : Algebra C E)
    IntermediateField.adjoin
      (IntermediateField.fixedField (F := K) (E := EI)
        (Subgroup.zpowers (G := Gal(EI/K)) τ))
      (Set.range (algebraMap C EI)) = ⊤ := by
  exact hgen

private theorem localGlobalArtinFactor_restrictScalars_view
    {k K J Ω : Type} [Field k] [Finite k] [Field K] [Field J] [Field Ω]
    [Algebra k K] [Algebra k J] [Algebra k Ω]
    [Algebra K J] [Algebra K Ω] [Algebra J Ω]
    [IsScalarTower k K J] [IsScalarTower k K Ω] [IsScalarTower k J Ω]
    [IsScalarTower K J Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (E : IntermediateField J Ω) [IsScalarTower k K E]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k E]
    (W : Place k E) :
    let EI : IntermediateField K Ω := E.restrictScalars K
    let _ : Algebra k EI := IntermediateField.algebra' EI
    have _ : IsScalarTower k K EI := IntermediateField.isScalarTower EI
    have _ : FiniteDimensional K EI := (inferInstance : FiniteDimensional K E)
    have _ : IsAbelianGalois K EI := (inferInstance : IsAbelianGalois K E)
    have _ : HasPrincipalDivisors k EI := (inferInstance : HasPrincipalDivisors k E)
    let WI : Place k EI := W
    localGlobalArtinFactor (K := K) WI =
      localGlobalArtinFactor (K := K) W := by
  rfl

private theorem localGlobalArtinFactor_restrictNormal_of_restrict_eq
    {k K L M : Type} [Field k] [Finite k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower k L M]
    [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]
    (W : Place k M) (τ : IdeleGroup.decompositionGroup (K := K) W)
    (w : Place k L) (σ : IdeleGroup.decompositionGroup (K := K) w)
    (hW : W.restrict L = w) (hτ : AlgEquiv.restrictNormalHom L τ.1 = σ.1) :
    localGlobalArtinFactor w σ =
      AlgEquiv.restrictNormalHom L (localGlobalArtinFactor W τ) := by
  subst w
  exact localGlobalArtinFactor_restrictNormal W τ σ hτ

section CyclicReduction

variable {k K C : Type} [Field k] [Finite k] [Field K] [Field C]
    [Algebra k K] [Algebra k (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [Algebra k C] [FiniteDimensional k C]
    [Algebra (RatFunc k) K] [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) K] [IsScalarTower k (RatFunc k) (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)] [FunctionField k K]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    [Algebra C E] [IsScalarTower k C E]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k E]

private theorem abelianFiniteArtin_localNorm_placeIdele
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F]
    [HasPrincipalDivisors k F] (hFE : F ≤ E) :
    let aFE : Algebra F E := (IntermediateField.inclusion hFE).toRingHom.toAlgebra
    let _ : SMul F E := aFE.toSMul
    let _ : Module F E := aFE.toModule
    have _ : IsScalarTower K F E :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsScalarTower k F E := IsScalarTower.to₁₃₄ k K F E
    have _ : FiniteDimensional F E := FiniteDimensional.right K F E
    have _ : IsAbelianGalois F E := IsAbelianGalois.tower_top K F E
    ∀ (W : Place k E) (y : (W.restrict F).adicCompletionˣ),
      abelianFiniteArtin k K E
          (IdeleClassGroup.mk (k := k) (K := K)
            (IdeleGroup.placeIdele (W.restrict K)
              (IdeleGroup.localNormOver (W.restrict K) (W.restrict F)
                (restrict_restrict (F := K) (E := F) W) y))) =
        (abelianFiniteArtin k F E
          (IdeleClassGroup.mk (k := k) (K := F)
            (IdeleGroup.placeIdele (W.restrict F) y))).restrictScalars K := by
  intro aFE sFE mFE hKFE hkFE hFEfinite hFEabelian W y
  let c : IdeleClassGroup k F :=
    IdeleClassGroup.mk (k := k) (K := F) (IdeleGroup.placeIdele (W.restrict F) y)
  have hnorm := abelianFiniteArtin_norm_restrictScalars k K F E hFE c
  have hclass := classNorm_placeIdele_of_restrict_eq
    (K := K) (F := F) (W.restrict K) (W.restrict F)
    (restrict_restrict (F := K) (E := F) W) y
  exact (congrArg (abelianFiniteArtin k K E) hclass).symm.trans hnorm

private theorem localGlobalArtinFactor_constantGenerated_descent
    (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [IsGalois K F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [IsScalarTower (RatFunc k) K F] [FunctionField k F]
    [HasPrincipalDivisors k F] (hFE : F ≤ E) :
    let aFE : Algebra F E := (IntermediateField.inclusion hFE).toRingHom.toAlgebra
    let _ : SMul F E := aFE.toSMul
    let _ : Module F E := aFE.toModule
    have _ : IsScalarTower K F E :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsScalarTower k F E := IsScalarTower.to₁₃₄ k K F E
    have _ : FiniteDimensional F E := FiniteDimensional.right K F E
    have _ : IsAbelianGalois F E := IsAbelianGalois.tower_top K F E
    ∀ (_ : Algebra.adjoin F (Set.range (algebraMap C E)) = ⊤)
      (W : Place k E) (τ : IdeleGroup.decompositionGroup (K := F) W),
      localGlobalArtinFactor (K := K) W ⟨τ.1.restrictScalars K, τ.2⟩ =
        τ.1.restrictScalars K := by
  intro aFE sFE mFE hKFE hkFE hFEfinite hFEabelian hgenA W τ
  have hEfield : FunctionField k E :=
    IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
      (k := k) (K := K) (Ω := SeparableClosure K) E
  let τF : Gal(E/F) := τ.1
  let τFD : IdeleGroup.decompositionGroup (K := F) W := τ
  let τK : IdeleGroup.decompositionGroup (K := K) W := ⟨τ.1.restrictScalars K, τ.2⟩
  obtain ⟨y, hy⟩ := localDecompositionArtin_surjective (K := F) W τFD
  have hyτ : localArtin (K := F) W y = τF := congrArg Subtype.val hy
  let c : IdeleClassGroup k F :=
    IdeleClassGroup.mk (k := k) (K := F) (IdeleGroup.placeIdele (W.restrict F) y)
  have hyglobal : abelianFiniteArtin k F E c = τF :=
    (localArtin_constantGenerated (k := k) (C := C) (K := F) (E := E)
      hgenA W y).symm.trans hyτ
  have hFK : (W.restrict F).restrict K = W.restrict K :=
    restrict_restrict (F := K) (E := F) W
  let b : (W.restrict K).adicCompletionˣ :=
    IdeleGroup.localNormOver (W.restrict K) (W.restrict F) hFK y
  have hlocalNorm := localArtin_norm_restrictScalars (K := K) (L := F) W y
  have hbτ : localArtin (K := K) W b = τK.1 :=
    hlocalNorm.symm.trans (congrArg (AlgEquiv.restrictScalars K) hyτ)
  have haτ : abelianFiniteArtin k K E
      (IdeleClassGroup.mk (k := k) (K := K)
        (IdeleGroup.placeIdele (W.restrict K) b)) = τK.1 :=
    (abelianFiniteArtin_localNorm_placeIdele (k := k) (K := K) E F hFE W y).trans
      (congrArg (AlgEquiv.restrictScalars K) hyglobal)
  have hbD : localDecompositionArtin (K := K) W b = τK := Subtype.ext hbτ
  have heval := localGlobalArtinFactor_apply_localDecompositionArtin W b
  rw [hbD] at heval
  exact heval.trans haτ

/-- A decomposition element whose cyclic fixed field generates the extension
with finite constants has its expected one-place global Artin value. -/
theorem localGlobalArtinFactor_cyclicFixedField
    (W : Place k E) (τ : IdeleGroup.decompositionGroup (K := K) W)
    (hgen : IntermediateField.adjoin (IntermediateField.fixedField (Subgroup.zpowers τ.1))
      (Set.range (algebraMap C E)) = ⊤) :
    localGlobalArtinFactor W τ = τ.1 := by
  have hconstants := cyclicFixedField_lift_adjoin_eq_top_and_fixed
    E τ.1 (Set.range (algebraMap C E)) hgen
  extract_lets (config := { descend := false, merge := false }) F0 F aFE at hconstants
  let sFE : SMul F E := aFE.toSMul
  let mFE : Module F E := aFE.toModule
  have hKFE : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkFE : IsScalarTower k F E := IsScalarTower.to₁₃₄ k K F E
  -- Both intermediate fields inherit the ambient rational parameter from
  -- IntermediateField.algebra'; keep that canonical action and its towers.
  have hKFfinite : FiniteDimensional K F := FiniteDimensional.of_injective
    (IntermediateField.inclusion (IntermediateField.lift_le F0)).toLinearMap
    (IntermediateField.inclusion (IntermediateField.lift_le F0)).injective
  have hFEfinite : FiniteDimensional F E := FiniteDimensional.right K F E
  have hKFabelian : IsAbelianGalois K F := IsAbelianGalois.tower_bot K F E
  have hFEabelian : IsAbelianGalois F E := IsAbelianGalois.tower_top K F E
  have hFfield : FunctionField k F :=
    IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
      (k := k) (K := K) (Ω := SeparableClosure K) F
  have hFcurve : IsCurveOver k F := isCurveOver k F
  have hFprincipal : HasPrincipalDivisors k F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨hgenA, hfixed⟩ := hconstants
  let τF : Gal(E/F) := { τ.1.toRingEquiv with commutes' := hfixed }
  let τFD : IdeleGroup.decompositionGroup (K := F) W := ⟨τF, τ.2⟩
  exact localGlobalArtinFactor_constantGenerated_descent (k := k) (K := K) (C := C)
    E F (IntermediateField.lift_le F0) hgenA W τFD

end CyclicReduction

section EmbeddedExtension

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra k (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    (L : FiniteGaloisIntermediateField K (SeparableClosure K))
    [IsAbelianGalois K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

omit [IsAbelianGalois K L] [HasPrincipalDivisors k L] in
private theorem localGlobalArtinFactor_auxiliary_restrictScalars
    [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k L (SeparableClosure K)]
    (C : Type) [Field C] [Algebra k C] [FiniteDimensional k C]
    (E : FiniteGaloisIntermediateField L (SeparableClosure K))
    [IsScalarTower k K E] [FiniteDimensional K E] [IsAbelianGalois K E]
    [Algebra C E] [IsScalarTower k C E] [HasPrincipalDivisors k E]
    (W : Place k E) (τ : IdeleGroup.decompositionGroup (K := K) W)
    (hgen : IntermediateField.adjoin (IntermediateField.fixedField (Subgroup.zpowers τ.1))
      (Set.range (algebraMap C E)) = ⊤) :
    localGlobalArtinFactor W τ = τ.1 := by
  let EI : IntermediateField K (SeparableClosure K) := E.toIntermediateField.restrictScalars K
  have hEI : FiniteDimensional K EI := (inferInstance : FiniteDimensional K E)
  have hEIabelian : IsAbelianGalois K EI := (inferInstance : IsAbelianGalois K E)
  let aCEI : Algebra C EI := (inferInstance : Algebra C E)
  have hkCEI : IsScalarTower k C EI := (inferInstance : IsScalarTower k C E)
  have hEIprincipal : HasPrincipalDivisors k EI := (inferInstance : HasPrincipalDivisors k E)
  let WI : Place k EI := W
  let τI : IdeleGroup.decompositionGroup (K := K) WI := τ
  have hgenI := fixedField_adjoin_restrictScalars E.toIntermediateField τ.1 hgen
  have hvalue := localGlobalArtinFactor_cyclicFixedField
    (k := k) (K := K) (C := C) EI WI τI hgenI
  have hview : localGlobalArtinFactor (K := K) WI = localGlobalArtinFactor (K := K) W :=
    localGlobalArtinFactor_restrictScalars_view
      (k := k) (K := K) (J := L) E.toIntermediateField W
  have hview_apply := DFunLike.congr_fun hview τI
  exact hview_apply.symm.trans hvalue

private theorem localGlobalArtinFactor_auxiliary_descent
    [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k L (SeparableClosure K)]
    (C : Type) [Field C] [Algebra k C] [FiniteDimensional k C]
    (E : FiniteGaloisIntermediateField L (SeparableClosure K))
    [IsScalarTower k K E] [FiniteDimensional K E] [IsAbelianGalois K E]
    [Algebra C E] [IsScalarTower k C E] [HasPrincipalDivisors k E]
    (W : Place k E) (τ : IdeleGroup.decompositionGroup (K := K) W)
    (hgen : IntermediateField.adjoin (IntermediateField.fixedField (Subgroup.zpowers τ.1))
      (Set.range (algebraMap C E)) = ⊤)
    (w : Place k L) (σ : IdeleGroup.decompositionGroup (K := K) w)
    (hW : W.restrict L = w) (hτ : AlgEquiv.restrictNormalHom L τ.1 = σ.1) :
    localGlobalArtinFactor w σ = σ.1 := by
  have hτfactor := localGlobalArtinFactor_auxiliary_restrictScalars k K L C E W τ hgen
  let r : Gal(E/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  have hrest := localGlobalArtinFactor_restrictNormal_of_restrict_eq
    (k := k) (K := K) (L := L) (M := E) W τ w σ hW hτ
  have hvalue : r (localGlobalArtinFactor W τ) = r τ.1 := congrArg r hτfactor
  exact hrest.trans (hvalue.trans hτ)

/-- The local-global comparison for an actual embedded finite abelian extension. -/
theorem localArtin_eq_abelianFiniteArtin_placeIdele_of_intermediateField
    (w : Place k L) (x : (w.restrict K).adicCompletionˣ) :
    localArtin (K := K) w x = abelianFiniteArtin k K L
      (IdeleClassGroup.mk (k := k) (K := K) (IdeleGroup.placeIdele (w.restrict K) x)) := by
  have hfactor : localGlobalArtinFactor w =
      (IdeleGroup.decompositionGroup (K := K) w).subtype := by
    apply MonoidHom.ext
    intro σ
    obtain ⟨n, hn, haux⟩ :=
      exists_constantDecomposition_auxiliaryField k K (SeparableClosure K) L w σ
    -- Keep the exact structures, constant field, extension, and embedding supplied
    -- by the constructed witness. Rebuilding them introduces competing action paths.
    extract_lets (config := { descend := false, merge := false })
      aRL hRKL hkRL hLfield hkLΩ hLft hAfinite hkAΩ C hCfinite E hkKE hKEfinite iC at haux
    obtain ⟨W, τ, hW, hτ, hgen⟩ := haux
    have hKEabelian : IsAbelianGalois K E := isAbelianGalois_constantExtension_over_base L C
    let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.to₁₂₄ k (RatFunc k) K (SeparableClosure K)
    have hEcurve : IsCurveOver k E :=
      ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E
    have hEprincipal : HasPrincipalDivisors k E := IsCurveOver.hasPrincipalDivisors
    let aCE : Algebra C E := constantAlgebra (K := L) C
    let sCE : SMul C E := aCE.toSMul
    have hkCE : IsScalarTower k C E := constantScalarTower (K := L) C
    exact localGlobalArtinFactor_auxiliary_descent k K L C E W τ hgen w σ hW hτ
  have h := localGlobalArtinFactor_apply_localDecompositionArtin w x
  rw [hfactor] at h
  exact h


end EmbeddedExtension

section ArbitraryExtension

variable (k K L : Type) [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual local arithmetic Artin map is the restriction of the native
finite global Artin map to the corresponding one-place idele. -/
theorem localArtin_eq_abelianFiniteArtin_placeIdele
    (w : Place k L) (x : (w.restrict K).adicCompletionˣ) :
    localArtin (K := K) w x = abelianFiniteArtin k K L
      (IdeleClassGroup.mk (k := k) (K := K) (IdeleGroup.placeIdele (w.restrict K) x)) := by
  let Ω := SeparableClosure K
  let akΩ : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  have hkKΩ : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let M : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := LocalClassFieldTheory.finiteGaloisFieldRange K L }
  let e : L ≃ₐ[K] M := LocalClassFieldTheory.finiteGaloisFieldRangeEquiv K L
  have hKMabelian : IsAbelianGalois K M := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hMcurve : IsCurveOver k M :=
    ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K M
  have hMprincipal : HasPrincipalDivisors k M := IsCurveOver.hasPrincipalDivisors
  let aLM : Algebra L M := e.toRingHom.toAlgebra
  have hKLM : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq (fun a => (e.commutes a).symm)
  have hkLM : IsScalarTower k L M := IsScalarTower.to₁₃₄ k K L M
  have hLMfinite : FiniteDimensional L M := FiniteDimensional.right K L M
  have hLMgal : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  obtain ⟨u, hu⟩ := Place.exists_restrict_eq (M := M) w
  subst w
  have hbase : (u.restrict L).restrict K = u.restrict K :=
    restrict_restrict (F := K) (E := L) u
  let x' : (u.restrict K).adicCompletionˣ := hbase ▸ x
  have transport (v v' : Place k K) (h : v = v') (z : v.adicCompletionˣ) :
      ((h.symm ▸ (h ▸ z)) : v.adicCompletionˣ) = z ∧
        IdeleGroup.placeIdele v' (h ▸ z) = IdeleGroup.placeIdele v z := by
    subst v'
    exact ⟨rfl, rfl⟩
  obtain ⟨hx, hplace⟩ := transport ((u.restrict L).restrict K) (u.restrict K) hbase x
  have hlocal : AlgEquiv.restrictNormalHom L (localArtin (K := K) u x') =
      localArtin (K := K) (u.restrict L) (hbase.symm ▸ x') :=
    localArtin_restrictNormal (K := K) (L := L) u x'
  rw [hx] at hlocal
  rw [← hlocal, localArtin_eq_abelianFiniteArtin_placeIdele_of_intermediateField k K M u x',
    abelianFiniteArtin_restrictNormal, hplace]

end ArbitraryExtension

end FunctionField
