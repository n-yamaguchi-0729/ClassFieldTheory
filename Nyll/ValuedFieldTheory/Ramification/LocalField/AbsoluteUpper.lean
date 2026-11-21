/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Profinite.CompatibleSubgroupImages
public import Nyll.ValuedFieldTheory.Ramification.LocalField.Core
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Absolute upper ramification over a local field

The inverse images of the actual finite upper ramification groups define a
closed subgroup of the Galois group of the separable closure. Finite Herbrand
quotient compatibility and compactness recover every finite upper group.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace RamificationTheory.LocalField

open LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The inverse limit of the upper groups over the finite separable Galois levels. -/
def separableLocalUpperRamificationGroup (t : ℝ) : Subgroup Gal(SeparableClosure K / K) :=
  ⨅ E : FiniteGaloisIntermediateField K (SeparableClosure K),
    (localUpperRamificationGroup K E t).comap (AlgEquiv.restrictNormalHom E.toIntermediateField)

/-- Restriction detects membership in the absolute upper group. -/
theorem mem_separableLocalUpperRamificationGroup_iff (t : ℝ)
    (σ : Gal(SeparableClosure K/K)) :
    σ ∈ separableLocalUpperRamificationGroup K t ↔
      ∀ E : FiniteGaloisIntermediateField K (SeparableClosure K),
        AlgEquiv.restrictNormalHom E.toIntermediateField σ ∈ localUpperRamificationGroup K E t :=
  Subgroup.mem_iInf

/-- The absolute upper group is closed in the Krull topology. -/
theorem separableLocalUpperRamificationGroup_isClosed (t : ℝ) :
    IsClosed (separableLocalUpperRamificationGroup K t : Set Gal(SeparableClosure K / K)) := by
  rw [separableLocalUpperRamificationGroup, Subgroup.coe_iInf]
  exact isClosed_iInter fun E =>
    (localUpperRamificationGroup K E t : Set Gal(E / K)).toFinite.isClosed.preimage
      (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)

/-- The absolute upper filtration is antitone, with the same real indices as each finite level. -/
theorem separableLocalUpperRamificationGroup_antitone :
    Antitone (separableLocalUpperRamificationGroup K) := by
  intro s t hst σ hσ
  apply (mem_separableLocalUpperRamificationGroup_iff K s σ).mpr
  intro E
  exact localUpperRamificationGroup_antitone K E hst
    ((mem_separableLocalUpperRamificationGroup_iff K t σ).mp hσ E)

/-- The absolute upper group has the literal finite upper group as its image. -/
theorem separableLocalUpperRamificationGroup_map_restrict (t : ℝ)
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    (separableLocalUpperRamificationGroup K t).map
        (AlgEquiv.restrictNormalHom E.toIntermediateField) =
      localUpperRamificationGroup K E t := by
  let restrict (F : FiniteGaloisIntermediateField K (SeparableClosure K)) :
      Gal(SeparableClosure K / K) →* Gal(F / K) :=
    AlgEquiv.restrictNormalHom F.toIntermediateField
  let transition (F H : FiniteGaloisIntermediateField K (SeparableClosure K))
      (hFH : F ≤ H) : Gal(H / K) →* Gal(F / K) :=
    intermediateFieldRestrictNormalHom F.toIntermediateField H.toIntermediateField hFH
  have hcomp (F H : FiniteGaloisIntermediateField K (SeparableClosure K))
      (hFH : F ≤ H) (σ : Gal(SeparableClosure K / K)) :
      transition F H hFH (restrict H σ) = restrict F σ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact (intermediateFieldRestrictNormalHom_apply_val F.toIntermediateField H.toIntermediateField
      hFH (restrict H σ) x).trans
      ((AlgEquiv.restrictNormal_commutes σ H.toIntermediateField
        (IntermediateField.inclusion hFH x)).trans
        (AlgEquiv.restrictNormal_commutes σ F.toIntermediateField x).symm)
  exact Subgroup.map_iInf_comap_of_compact_surjective restrict
    (fun F => InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField)
    (fun _ => AlgEquiv.restrictNormalHom_surjective (SeparableClosure K)) transition hcomp
    (fun F => localUpperRamificationGroup K F t)
    (fun F => (localUpperRamificationGroup K F t : Set Gal(F / K)).toFinite.isClosed)
    (fun F H hFH => localUpperRamificationGroup_map_restrict K F.toIntermediateField
      H.toIntermediateField hFH t) E

end RamificationTheory.LocalField
