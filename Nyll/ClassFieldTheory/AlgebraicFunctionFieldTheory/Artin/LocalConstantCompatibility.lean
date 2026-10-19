/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalResidueNormalization
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteConstantNormalization
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalGlobalFactor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionUnramified
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionSystem

/-!
# Local reciprocity on actual constant extensions

Both the local symbol and the constant-degree character induce arithmetic
Frobenius on the actual residue field at an order-one element. The faithful
residue action of the constant extension then identifies these actual global
automorphisms. Enlarging the displayed constants changes neither the valuation
ring nor its residue action.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsSepClosed Ω]

/-- The local symbol of an order-one element in a constant extension agrees
with the actual constant Frobenius character of its one-place idele. -/
theorem localArtin_fullConstant_uniformizer (n : ℕ) [NeZero n]
    (w : Place k (fullConstantDegreeStage k K Ω n))
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (IdeleGroup.localOrder (w.restrict K) x).toAdd = 1) :
    let _ : IsCyclic Gal((fullConstantDegreeStage k K Ω n)/K) :=
      isCyclic_fullConstantDegreeStage k K Ω n
    let _ : IsAbelianGalois K (fullConstantDegreeStage k K Ω n) :=
      IsAbelianGalois.of_isCyclic K (fullConstantDegreeStage k K Ω n)
    localArtin (K := K) w x =
      IdeleClassGroup.constantFrobeniusCharacter k K Ω n
        (IdeleClassGroup.mk (k := k) (K := K)
          (IdeleGroup.placeIdele (w.restrict K) x)) := by
  intro hcyclic hab
  let E := fullConstantDegreeStage k K Ω n
  let C := algebraicClosure k K
  let W : Place C E := w.extendConstants C
  let σ : IdeleGroup.decompositionGroup (K := K) w :=
    localDecompositionArtin (K := K) w x
  have hfix : SemilinearAut.ofAlgAut (σ.val.restrictScalars C) • W = W := by
    apply Place.ext
    have h := congrArg Place.toValuationSubring σ.property
    rw [SemilinearAut.smul_toValuationSubring] at h ⊢
    exact h
  let σC : IdeleGroup.decompositionGroup (K := K) W := ⟨σ.val, hfix⟩
  have hw : W.restrict K = (w.restrict K).extendConstants C := Place.ext rfl
  have hres (y : W.ResidueField) :
      IdeleGroup.decompositionResidueAut (K := K) W σC y =
        y ^ Nat.card (W.restrict K).ResidueField := by
    have hcompare : IdeleGroup.decompositionResidueAut (K := K) W σC y =
        IdeleGroup.decompositionResidueAut (K := K) w σ y := by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      have ha : (IdeleGroup.decompositionValuationEquiv W σC a : w.toValuationSubring) =
          IdeleGroup.decompositionValuationEquiv w σ a := by
        apply Subtype.ext
        exact (IdeleGroup.decompositionValuationEquiv_coe W σC a).trans
          (IdeleGroup.decompositionValuationEquiv_coe w σ a).symm
      have hW : (IdeleGroup.decompositionResidueAut (K := K) W σC
          (IsLocalRing.residue W.toValuationSubring a) : w.ResidueField) =
          IsLocalRing.residue w.toValuationSubring
            (IdeleGroup.decompositionValuationEquiv W σC a) :=
        IdeleGroup.decompositionResidueAut_residue W σC a
      have hw : IdeleGroup.decompositionResidueAut (K := K) w σ
          (IsLocalRing.residue w.toValuationSubring a) =
          IsLocalRing.residue w.toValuationSubring
            (IdeleGroup.decompositionValuationEquiv w σ a) :=
        IdeleGroup.decompositionResidueAut_residue w σ a
      exact hW.trans ((congrArg (IsLocalRing.residue w.toValuationSubring) ha).trans hw.symm)
    exact hcompare.trans (localDecompositionArtin_uniformizer_residue w
      (ramificationIndex_fullConstantDegreeStage k K Ω n w) x hx y)
  have h := (IdeleClassGroup.constantFrobeniusCharacter_uniformizer_eq_iff
    k K Ω n (w.restrict K) x hx W hw σC).mpr hres
  exact h.symm

/-- On a finite constant extension, the entire local symbol agrees with the
constant-degree character of the corresponding one-place idele. -/
theorem localArtin_fullConstant (n : ℕ) [NeZero n]
    (w : Place k (fullConstantDegreeStage k K Ω n))
    (x : (w.restrict K).adicCompletionˣ) :
    let _ : IsCyclic Gal((fullConstantDegreeStage k K Ω n)/K) :=
      isCyclic_fullConstantDegreeStage k K Ω n
    let _ : IsAbelianGalois K (fullConstantDegreeStage k K Ω n) :=
      IsAbelianGalois.of_isCyclic K (fullConstantDegreeStage k K Ω n)
    localArtin (K := K) w x =
      IdeleClassGroup.constantFrobeniusCharacter k K Ω n
        (IdeleClassGroup.mk (k := k) (K := K)
          (IdeleGroup.placeIdele (w.restrict K) x)) := by
  intro hcyclic hab
  let π : (w.restrict K).adicCompletionˣ :=
    RestrictedProduct.DiscreteValuation.chosenLocalOrderSection
      (w.restrict K).adicCompletion
      ((w.restrict K).heightOneSpectrum.valuedAdicCompletion_surjective K) 1
  have hπ : (IdeleGroup.localOrder (w.restrict K) π).toAdd = 1 :=
    RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection _ _ 1
  let m : ℤ := (IdeleGroup.localOrder (w.restrict K) x).toAdd
  let u : (w.restrict K).adicCompletionˣ := x / π ^ m
  have hu : (IdeleGroup.localOrder (w.restrict K) u).toAdd = 0 := by
    change (IdeleGroup.localOrder (w.restrict K) (x / π ^ m)).toAdd = 0
    rw [map_div, map_zpow, toAdd_div, toAdd_zpow,
      hπ, zsmul_eq_mul, mul_one]
    exact sub_self m
  obtain ⟨z, _, hz⟩ := IdeleGroup.exists_integral_localNorm_eq_of_ramificationIndex_eq_one w
    (ramificationIndex_fullConstantDegreeStage k K Ω n w) u
    ((IdeleGroup.localOrder_eq_zero_iff (w.restrict K) u).mp hu)
  have hulocal : localArtin (K := K) w u = 1 :=
    (localArtin_eq_one_iff w u).mpr ⟨z, hz⟩
  have hxlocal : localArtin (K := K) w x = localArtin (K := K) w π ^ m := by
    change localArtin (K := K) w (x / π ^ m) = 1 at hulocal
    rw [map_div, map_zpow, div_eq_one] at hulocal
    exact hulocal
  let χ : (w.restrict K).adicCompletionˣ →*
      Gal((fullConstantDegreeStage k K Ω n)/K) :=
    (IdeleClassGroup.constantFrobeniusCharacter k K Ω n).comp
      ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele (w.restrict K)))
  have huchar : χ u = 1 := by
    change IdeleClassGroup.constantFrobeniusCharacter k K Ω n
      (IdeleClassGroup.mk (k := k) (K := K) (IdeleGroup.placeIdele (w.restrict K) u)) = 1
    rw [IdeleClassGroup.constantFrobeniusCharacter_placeIdele, hu, zero_mul, zpow_zero]
  have hxchar : χ x = χ π ^ m := by
    change χ (x / π ^ m) = 1 at huchar
    rw [map_div, map_zpow, div_eq_one] at huchar
    exact huchar
  calc
    localArtin (K := K) w x = localArtin (K := K) w π ^ m := hxlocal
    _ = χ π ^ m := congrArg (fun σ => σ ^ m)
      (localArtin_fullConstant_uniformizer k K Ω n w π hπ)
    _ = χ x := hxchar.symm

/-- For the actual constant extension in the separable closure, the factor
of native global reciprocity through local reciprocity is the inclusion of
the decomposition group. -/
theorem localGlobalArtinFactor_fullConstant (n : ℕ) [NeZero n] :
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
    let _ : IsCyclic Gal((fullConstantDegreeStage k K (SeparableClosure K) n)/K) :=
      isCyclic_fullConstantDegreeStage k K (SeparableClosure K) n
    let _ : IsAbelianGalois K (fullConstantDegreeStage k K (SeparableClosure K) n) :=
      IsAbelianGalois.of_isCyclic K (fullConstantDegreeStage k K (SeparableClosure K) n)
    ∀ w : Place k (fullConstantDegreeStage k K (SeparableClosure K) n),
      localGlobalArtinFactor (K := K) w =
        (IdeleGroup.decompositionGroup (K := K) w).subtype := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ hcyclic hab w
  apply (localGlobalArtinFactor_unique w
    (IdeleGroup.decompositionGroup (K := K) w).subtype ?_).symm
  intro x
  change localArtin (K := K) w x = abelianFiniteArtin k K
    (fullConstantDegreeStage k K (SeparableClosure K) n)
      (QuotientGroup.mk (IdeleGroup.placeIdele (w.restrict K) x))
  rw [abelianFiniteArtin_fullConstant k K n]
  exact localArtin_fullConstant k K (SeparableClosure K) n w x

end FunctionField
