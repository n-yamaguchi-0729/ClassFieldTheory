/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FiniteCoefficientEuler

/-! # Shapiro transfer of the local Euler characteristic -/

@[expose] public section

open CategoryTheory ContinuousCohomology ContRepresentation TopRep LocalFieldTheory

noncomputable section

namespace TopRep

universe u

/-- The Euler characteristic property passes across an isomorphism of the
original continuous coefficient representations. -/
theorem hasLowDegreeEulerCharacteristic_of_iso {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    {w : ℕ → ℚ} {A B : TopRep.{u} ℤ G} (e : A ≅ B)
    (h : hasLowDegreeEulerCharacteristic G w A) : hasLowDegreeEulerCharacteristic G w B := by
  let C := continuousModuleComplexFunctor G
  let E (i : ℕ) := (C ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ)
    (ComplexShape.up ℕ) i).mapIso e
  have hc (i : ℕ) : Nat.card ((C.obj A).homology i) = Nat.card ((C.obj B).homology i) :=
    Nat.card_congr (Equiv.ofBijective (E i).hom (ConcreteCategory.bijective_of_isIso (E i).hom))
  have hCard : Nat.card A = Nat.card B := Nat.card_congr
    { toFun := e.hom.hom
      invFun := e.inv.hom
      left_inv := fun a => DFunLike.congr_fun (congrArg TopRep.Hom.hom e.hom_inv_id) a
      right_inv := fun b => DFunLike.congr_fun (congrArg TopRep.Hom.hom e.inv_hom_id) b }
  refine ⟨fun i hi => ?_, ?_⟩
  · let : Finite ((C.obj A).homology i) := h.1 i hi
    let inv : (C.obj B).homology i → (C.obj A).homology i := (E i).inv
    exact Finite.of_injective inv (ConcreteCategory.bijective_of_isIso (E i).inv).1
  change lowDegreeEulerCharacteristic (C.obj B) = w (Nat.card B)
  have hEuler : lowDegreeEulerCharacteristic (C.obj A) = w (Nat.card A) := h.2
  unfold lowDegreeEulerCharacteristic at hEuler ⊢
  rw [← hc 0, ← hc 1, ← hc 2, ← hCard, hEuler]

private def continuousModuleHomologyEquiv_of_groupEquiv {G H : Type u}
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : H ≃ₜ* G) (A : TopRep.{u} ℤ G) (i : ℕ) :
    ((continuousModuleComplexFunctor G).obj A).homology i ≃
      ((continuousModuleComplexFunctor H).obj (TopRep.res e.toMonoidHom A)).homology i := by
  let B := TopRep.res e.toMonoidHom A
  let e₁ := continuousModuleHomologyIso G A i
  let e₂ := continuousModuleHomologyIso H B i
  let r := ContinuousCohomology.map (e : H →ₜ* G) (𝟙 B) i
  have hr : Function.Bijective r := restriction_equiv_bijective e A i
  exact (Equiv.ofBijective e₁.hom (ConcreteCategory.bijective_of_isIso e₁.hom)).trans
    ((Equiv.ofBijective r hr).trans
      (Equiv.ofBijective e₂.inv (ConcreteCategory.bijective_of_isIso e₂.inv)))

end TopRep

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

private theorem openCoinducedEuler_of_homology_equiv
    {G H : Type u} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [CompactSpace G]
    {wG wH : ℕ → ℚ}
    (U : OpenSubgroup G) [IsTopologicalGroup ↥U] (A : TopRep.{u} ℤ ↥U) (B : TopRep.{u} ℤ H)
    (S : ∀ i, ((continuousModuleComplexFunctor ↥U).obj A).homology i ≃
      ((continuousModuleComplexFunctor H).obj B).homology i)
    (hEuler : hasLowDegreeEulerCharacteristic H wH B)
    (hweight : wH (Nat.card B) = wG (Nat.card (openCoinduced U A))) :
    hasLowDegreeEulerCharacteristic G wG (openCoinduced U A) := by
  let Co := openCoinduced U A
  let CG := continuousModuleComplexFunctor G
  let CU := continuousModuleComplexFunctor ↥U
  let CH := continuousModuleComplexFunctor H
  have hS (i : ℕ) : Nat.card ((CU.obj A).homology i) =
      Nat.card ((CH.obj B).homology i) := Nat.card_congr (S i)
  refine ⟨fun i hi => ?_, ?_⟩
  · let : Finite ((CH.obj B).homology i) := hEuler.1 i hi
    let EA := continuousModuleHomologyIso ↥U A i
    let EC := continuousModuleHomologyIso G Co i
    let f := (Equiv.ofBijective EC.hom (ConcreteCategory.bijective_of_isIso EC.hom)).trans
      ((openShapiroEquiv U A i hi).toEquiv.trans
        ((Equiv.ofBijective EA.inv (ConcreteCategory.bijective_of_isIso EA.inv)).trans (S i)))
    exact Finite.of_injective f f.injective
  have hshapiro : lowDegreeEulerCharacteristic (CG.obj Co) =
      lowDegreeEulerCharacteristic (CU.obj A) :=
    lowDegreeEulerCharacteristic_openCoinduced U A
  have hchange : lowDegreeEulerCharacteristic (CU.obj A) =
      lowDegreeEulerCharacteristic (CH.obj B) := by
    unfold lowDegreeEulerCharacteristic
    rw [hS 0, hS 1, hS 2]
  exact hshapiro.trans (hchange.trans (hEuler.2.trans hweight))

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)
local notation "C[" Γ "]" => continuousModuleComplexFunctor Γ

/-- Finite extension coinduction preserves the local Euler formula with the
normalized coefficient order on the actual ground field. -/
theorem localEulerCoefficient_openCoinduced (U : OpenSubgroup G)
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    (hfix : E.fixingSubgroup = U.toSubgroup)
    (A : TopRep.{u} ℤ ↥U) [Finite A]
    (hA : Continuous (fun ga : ↥U × A => A.ρ ga.1 ga.2))
    (hEuler : letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
      hasLowDegreeEulerCharacteristic Gal(SeparableClosure E/E) (localCoefficientOrderNorm E)
        (TopRep.res (fixedFieldAbsoluteEquiv K U E hfix).toMonoidHom A)) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K) (openCoinduced U A) := by
  let e := fixedFieldAbsoluteEquiv K U E hfix
  let GE := Gal(SeparableClosure E/E)
  let B := TopRep.res e.toMonoidHom A
  let Co := openCoinduced U A
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  let : IsTopologicalGroup ↥U :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (U : Subgroup G).subtype
  let : CompactSpace G :=
    (InfiniteGalois.continuousMulEquivToLimit K Ω).symm.compactSpace
  let S (i : ℕ) : ((C[↥U]).obj A).homology i ≃ ((C[GE]).obj B).homology i :=
    TopRep.continuousModuleHomologyEquiv_of_groupEquiv e A i
  have hindex : Module.finrank K E = U.toSubgroup.index := by
    rw [← hfix]
    exact IntermediateField.finrank_eq_fixingSubgroup_index Ω E
  have hweight : localCoefficientOrderNorm E (Nat.card B) =
      localCoefficientOrderNorm K (Nat.card Co) := by
    rw [localCoefficientOrderNorm_openCoinduced K U A hA,
      localCoefficientOrderNorm_finiteExtension K E (Nat.card B), hindex]
  exact openCoinducedEuler_of_homology_equiv U A B S hEuler hweight

end ClassFieldTheory.Brauer
