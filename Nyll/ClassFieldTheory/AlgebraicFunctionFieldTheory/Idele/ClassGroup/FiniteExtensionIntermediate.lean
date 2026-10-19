/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionFixed

/-!
# Arbitrary finite intermediate idele classes in the direct limit

A finite intermediate field embeds through its actual normal closure. The
base-change tower law proves independence of the containing finite Galois stage.
The image is exactly the classes fixed by the ambient subgroup fixing the
intermediate field pointwise, including when that field is not normal over the
original base.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionLimit

open FiniteExtensionSystem

variable {k K Ω : Type*} [Field k] [PerfectField k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [FunctionField k K]

/-- A finite intermediate field uses the compatible ambient rational parameter. -/
instance intermediateRatFuncTower (E : IntermediateField K Ω) :
    IsScalarTower k (RatFunc k) E :=
  IsScalarTower.of_algebraMap_eq fun x =>
    Subtype.ext (IsScalarTower.algebraMap_apply k (RatFunc k) Ω x)

/-- Every finite intermediate field is an ordinary one-variable function field. -/
instance intermediateFunctionField (E : IntermediateField K Ω) [FiniteDimensional K E] :
    FunctionField k E := Module.Finite.trans K E

/-- The actual curve and principal-divisor structure of a finite intermediate field. -/
instance intermediateIsCurveOver (E : IntermediateField K Ω) [FiniteDimensional K E] :
    AlgebraicCurve.IsCurveOver k E := FunctionField.isCurveOver k E

/-- Inclusion of any finite intermediate field into a containing finite Galois stage. -/
def includeInStage (E : IntermediateField K Ω) [FiniteDimensional K E]
    (H : FiniteGaloisIntermediateField K Ω) (h : E ≤ H) :
    IdeleClassGroup k E →* stage (k := k) H :=
  let _aEH : Algebra E H := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : FiniteDimensional E H := FiniteDimensional.right K E H
  have : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  IdeleClassGroup.baseChange (k := k) (K := E) (L := H)

/-- The actual inclusion into any containing Galois stage is injective. -/
theorem includeInStage_injective (E : IntermediateField K Ω) [FiniteDimensional K E]
    (H : FiniteGaloisIntermediateField K Ω) (h : E ≤ H) :
    Function.Injective (includeInStage (k := k) (K := K) (Ω := Ω) E H h) := by
  let _aEH : Algebra E H := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : FiniteDimensional E H := FiniteDimensional.right K E H
  have : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  exact IdeleClassGroup.baseChange_injective (k := k) (K := E) (L := H)

/-- Including an arbitrary finite intermediate field through successive Galois
stages agrees with its direct inclusion. -/
theorem includeInStage_trans (E : IntermediateField K Ω) [FiniteDimensional K E]
    (H J : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) (hHJ : H ≤ J)
    (c : IdeleClassGroup k E) :
    transition (k := k) H J hHJ (includeInStage (k := k) (K := K) (Ω := Ω) E H hEH c) =
      includeInStage (k := k) (K := K) (Ω := Ω) E J (hEH.trans hHJ) c := by
  let _aEH : Algebra E H := (IntermediateField.inclusion hEH).toRingHom.toAlgebra
  let _aHJ : Algebra H J := inclusionAlgebra hHJ
  let _aEJ : Algebra E J := (IntermediateField.inclusion (hEH.trans hHJ)).toRingHom.toAlgebra
  have : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsScalarTower K E J := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsScalarTower K H J := inclusion_baseScalarTower hHJ
  have : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsScalarTower k E J := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsScalarTower k H J := inclusion_scalarTower (k := k) hHJ
  have : IsScalarTower E H J := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : FiniteDimensional E H := FiniteDimensional.right K E H
  have : FiniteDimensional E J := FiniteDimensional.right K E J
  have : FiniteDimensional H J := inclusion_finiteDimensional hHJ
  have : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  have : IsGalois E J := IsGalois.tower_top_of_isGalois K E J
  have : IsGalois H J := inclusion_isGalois hHJ
  exact IdeleClassGroup.baseChange_trans (k := k) (K := E) (L := H) (M := J) c

variable [IsGalois K Ω]

/-- The actual normal closure of a finite intermediate field is a finite Galois stage. -/
def normalClosureStage (E : IntermediateField K Ω) [FiniteDimensional K E] :
    FiniteGaloisIntermediateField K Ω :=
  { IntermediateField.normalClosure K E Ω with
    finiteDimensional := normalClosure.is_finiteDimensional K E Ω
    isGalois := IsGalois.normalClosure K E Ω }

/-- The actual idele class group of any finite intermediate field embeds through
its normal closure into the finite-extension direct limit. -/
def ofIntermediate (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IdeleClassGroup k E →* Limit k K Ω :=
  (of (k := k) (K := K) (Ω := Ω) (normalClosureStage E)).comp
    (includeInStage (k := k) (K := K) (Ω := Ω) E (normalClosureStage E)
      (IntermediateField.le_normalClosure E))

/-- The normal-closure construction is independent of the containing finite
Galois stage used to represent the class. -/
theorem ofIntermediate_eq_of (E : IntermediateField K Ω) [FiniteDimensional K E]
    (H : FiniteGaloisIntermediateField K Ω) (h : E ≤ H) (c : IdeleClassGroup k E) :
    ofIntermediate (k := k) (K := K) (Ω := Ω) E c =
      of (k := k) (K := K) (Ω := Ω) H
        (includeInStage (k := k) (K := K) (Ω := Ω) E H h c) := by
  have hcl : normalClosureStage E ≤ H :=
    IntermediateField.normalClosure_le_iff_of_normal.mpr h
  change of (k := k) (K := K) (Ω := Ω) (normalClosureStage E)
      (includeInStage (k := k) (K := K) (Ω := Ω) E (normalClosureStage E)
        (IntermediateField.le_normalClosure E) c) = _
  rw [← of_transition (k := k) (K := K) (Ω := Ω) (normalClosureStage E) H hcl]
  exact congrArg (of (k := k) (K := K) (Ω := Ω) H)
    (includeInStage_trans (k := k) (K := K) (Ω := Ω) E (normalClosureStage E) H
      (IntermediateField.le_normalClosure E) hcl c)

/-- Every finite intermediate idele class group embeds injectively into the limit. -/
theorem ofIntermediate_injective (E : IntermediateField K Ω) [FiniteDimensional K E] :
    Function.Injective (ofIntermediate (k := k) (K := K) (Ω := Ω) E) :=
  (of_injective (k := k) (K := K) (Ω := Ω) (normalClosureStage E)).comp
    (includeInStage_injective (k := k) (K := K) (Ω := Ω) E (normalClosureStage E)
      (IntermediateField.le_normalClosure E))

/-- An ambient automorphism fixing `E` restricts to an automorphism of each
containing finite Galois stage over `E`. -/
def restrictOverIntermediate (E : IntermediateField K Ω)
    (H : FiniteGaloisIntermediateField K Ω) (h : E ≤ H)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ E.fixingSubgroup) :
    let _ : Algebra E H := (IntermediateField.inclusion h).toRingHom.toAlgebra
    H ≃ₐ[E] H :=
  let _aEH : Algebra E H := (IntermediateField.inclusion h).toRingHom.toAlgebra
  { __ := (AlgEquiv.restrictNormalHom H σ).toRingEquiv
    commutes' x := by
      apply Subtype.ext
      change algebraMap H Ω ((AlgEquiv.restrictNormalHom H σ) (algebraMap E H x)) =
        algebraMap H Ω (algebraMap E H x)
      exact (AlgEquiv.restrictNormal_commutes σ H (algebraMap E H x)).trans
        (((IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ) x.1 x.2) }

/-- Actual finite-intermediate-field classes are fixed by their pointwise
ambient fixing subgroup after inclusion into the limit. -/
theorem ofIntermediate_fixed (E : IntermediateField K Ω) [FiniteDimensional K E]
    (c : IdeleClassGroup k E) (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ E.fixingSubgroup) :
    σ • ofIntermediate (k := k) (K := K) (Ω := Ω) E c =
      ofIntermediate (k := k) (K := K) (Ω := Ω) E c := by
  let H := normalClosureStage E
  have hEH : E ≤ H := IntermediateField.le_normalClosure E
  let _aEH : Algebra E H := (IntermediateField.inclusion hEH).toRingHom.toAlgebra
  have : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : FiniteDimensional E H := FiniteDimensional.right K E H
  have : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  rw [ofIntermediate_eq_of (k := k) (K := K) (Ω := Ω) E H hEH, smul_of, stage_smul_eq_restrict]
  apply congrArg (of (k := k) (K := K) (Ω := Ω) H)
  exact IdeleClassGroup.algAut_smul_baseChange (restrictOverIntermediate E H hEH σ hσ) c

/-- Finite-stage automorphisms over a possibly nonnormal intermediate field
lift to actual ambient automorphisms fixing that field pointwise. -/
theorem exists_lift_fixing_intermediate (E : IntermediateField K Ω)
    (H : FiniteGaloisIntermediateField K Ω) (h : E ≤ H) :
    let _ : Algebra E H := (IntermediateField.inclusion h).toRingHom.toAlgebra
    let _ : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
    ∀ η : H ≃ₐ[E] H, ∃ σ : Ω ≃ₐ[K] Ω,
      AlgEquiv.restrictNormalHom H σ = η.restrictScalars K ∧ σ ∈ E.fixingSubgroup := by
  intro _aEH _ht η
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := H) (E := Ω) (η.restrictScalars K)
  refine ⟨σ, hσ, (IntermediateField.mem_fixingSubgroup_iff E σ).mpr ?_⟩
  intro x hx
  calc
    σ x = algebraMap H Ω
        ((AlgEquiv.restrictNormalHom H σ) (algebraMap E H ⟨x, hx⟩)) :=
      (AlgEquiv.restrictNormal_commutes σ H (algebraMap E H ⟨x, hx⟩)).symm
    _ = algebraMap H Ω (η (algebraMap E H ⟨x, hx⟩)) :=
      congrArg (algebraMap H Ω) (DFunLike.congr_fun hσ (algebraMap E H ⟨x, hx⟩))
    _ = x := congrArg (algebraMap H Ω) (η.commutes ⟨x, hx⟩)

/-- Every limit class fixed over an arbitrary finite intermediate field
descends to that field's actual idele class group. -/
theorem exists_ofIntermediate_of_fixed (E : IntermediateField K Ω) [FiniteDimensional K E]
    (z : Limit k K Ω)
    (hz : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ • z = z) :
    ∃ c : IdeleClassGroup k E, ofIntermediate (k := k) (K := K) (Ω := Ω) E c = z := by
  obtain ⟨F, c, hc⟩ := exists_of (k := k) (K := K) (Ω := Ω) z
  let H : FiniteGaloisIntermediateField K Ω := normalClosureStage E ⊔ F
  have hEH : E ≤ H := (IntermediateField.le_normalClosure E).trans le_sup_left
  let _aEH : Algebra E H := (IntermediateField.inclusion hEH).toRingHom.toAlgebra
  have : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
  have : FiniteDimensional E H := FiniteDimensional.right K E H
  have : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  let d : stage (k := k) H := transition (k := k) F H (show F ≤ H from le_sup_right) c
  have hd : of (k := k) (K := K) (Ω := Ω) H d = z :=
    (of_transition (k := k) (K := K) (Ω := Ω) F H le_sup_right c).trans hc
  have hfixed : ∀ η : H ≃ₐ[E] H,
      AlgebraicCurve.SemilinearAut.ofAlgAut (η.restrictScalars k) • d = d := by
    intro η
    obtain ⟨σ, hσH, hσE⟩ := exists_lift_fixing_intermediate E H hEH η
    have hfix := hz σ hσE
    rw [← hd] at hfix
    have hstage := (of_fixed_iff (k := k) (K := K) (Ω := Ω) σ H d).1 hfix
    rw [stage_smul_eq_restrict, hσH] at hstage
    exact hstage
  obtain ⟨b, hb⟩ := IdeleClassGroup.exists_baseChange_of_algAut_fixed d hfixed
  refine ⟨b, ?_⟩
  rw [ofIntermediate_eq_of (k := k) (K := K) (Ω := Ω) E H hEH]
  exact (congrArg (of (k := k) (K := K) (Ω := Ω) H) hb).trans hd

/-- The fixed part over any finite intermediate field is its actual idele class image. -/
theorem mem_range_ofIntermediate_iff_fixed (E : IntermediateField K Ω)
    [FiniteDimensional K E] (z : Limit k K Ω) :
    z ∈ (ofIntermediate (k := k) (K := K) (Ω := Ω) E).range ↔
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ • z = z := by
  constructor
  · rintro ⟨c, rfl⟩ σ hσ
    exact ofIntermediate_fixed (k := k) (K := K) (Ω := Ω) E c σ hσ
  · exact exists_ofIntermediate_of_fixed (k := k) (K := K) (Ω := Ω) E z

/-- The concrete fixed-point comparison for every finite intermediate field,
with its actual pointwise fixing subgroup. -/
def intermediateEquivFixed (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IdeleClassGroup k E ≃* FixedPoints.subgroup E.fixingSubgroup (Limit k K Ω) :=
  (MonoidHom.ofInjective (ofIntermediate_injective (k := k) (K := K) (Ω := Ω) E)).trans
    (MulEquiv.subgroupCongr (by
      apply Subgroup.ext
      intro z
      rw [mem_range_ofIntermediate_iff_fixed]
      constructor
      · intro hz σ
        exact hz σ.1 σ.2
      · intro hz σ hσ
        exact hz ⟨σ, hσ⟩))

/-- The arbitrary finite fixed-part comparison is the actual normal-closure inclusion. -/
@[simp]
theorem coe_intermediateEquivFixed (E : IntermediateField K Ω) [FiniteDimensional K E]
    (c : IdeleClassGroup k E) :
    (intermediateEquivFixed (k := k) (K := K) (Ω := Ω) E c : Limit k K Ω) =
      ofIntermediate (k := k) (K := K) (Ω := Ω) E c :=
  rfl

end FunctionField.IdeleClassGroup.FiniteExtensionLimit
