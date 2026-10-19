/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient
import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup

/-!
# Representing an actual finite Galois tower by its fixing subgroups

The fields, inclusions, finiteness and normality are supplied by the given
intermediate fields and the existing infinite Galois correspondence.
-/

noncomputable section

open ClassFormation LocalClassFieldTheory CyclicCohomology RamificationTheory

namespace FunctionField

/-- Actual finite Galois intermediate fields are represented by a finite closed-subgroup tower. -/
theorem exists_embeddedFixedFieldTower (K : Type) [Field K]
    (F E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [FiniteDimensional K E]
    [IsGalois K F] [IsGalois K E] (hFE : F ≤ E) :
    ∃ (H : FiniteAbstractField Gal(SeparableClosure K/K))
      (T : FiniteGaloisSubextension H.field),
      abstractFixedField K (SeparableClosure K) H.field = F ∧
      abstractFixedField K (SeparableClosure K) T.field = E ∧
      H.field.toSubgroup.Normal ∧ T.field.toSubgroup.Normal := by
  let Ω := SeparableClosure K
  have hFfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) (closedFixingSubgroup K Ω F)
        (le_baseField _)) := by
    exact (congrArg
      (fun B : ClosedSubgroup Gal(Ω/K) =>
        Finite (B.toSubgroup ⧸ F.fixingSubgroup.subgroupOf B.toSubgroup))
      (closedFixingSubgroup_bot_eq_baseField K Ω)).mp
        (baseFixingExtensionQuotient_finite K Ω F)
  have hEfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) (closedFixingSubgroup K Ω E)
        (le_baseField _)) := by
    exact (congrArg
      (fun B : ClosedSubgroup Gal(Ω/K) =>
        Finite (B.toSubgroup ⧸ E.fixingSubgroup.subgroupOf B.toSubgroup))
      (closedFixingSubgroup_bot_eq_baseField K Ω)).mp
        (baseFixingExtensionQuotient_finite K Ω E)
  let H : FiniteAbstractField Gal(Ω/K) :=
    { field := closedFixingSubgroup K Ω F, finite := hFfinite }
  have hbelow : (closedFixingSubgroup K Ω E).toSubgroup ≤ H.field.toSubgroup :=
    IntermediateField.fixingSubgroup_le hFE
  let T : FiniteGaloisSubextension H.field :=
    { field := closedFixingSubgroup K Ω E
      below := hbelow
      normal := by
        change (E.fixingSubgroup.subgroupOf F.fixingSubgroup).Normal
        infer_instance
      finite := FiniteGaloisSubextension.finite_extension_over_intermediate
        (le_baseField _) (le_baseField _) hbelow }
  refine ⟨H, T, InfiniteGalois.fixedField_fixingSubgroup F,
    InfiniteGalois.fixedField_fixingSubgroup E, ?_, ?_⟩
  · change F.fixingSubgroup.Normal
    infer_instance
  · change E.fixingSubgroup.Normal
    infer_instance

end FunctionField
