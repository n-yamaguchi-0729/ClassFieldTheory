import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.Filtered.StandardCompositum
import LocalClassFieldTheory.Concrete.Finite.Existence.StandardDominatingExtension
import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.Filtered.Core
import LocalClassFieldTheory.Concrete.LubinTateApplication.StandardFixedFieldComparison
import RamificationTheory.LocalField

/-!
# Filtered reciprocity for arbitrary finite abelian local extensions

An arbitrary finite abelian extension embeds into a standard finite
abelian compositum.  Passing to its field range inside the fixed separable
closure permits descent by restriction, and the resulting algebra
equivalence transports both filtrations back to the original extension.
-/

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open LocalClassFieldTheory
open LocalFieldTheory

/-- Characteristic-independent real filtered local reciprocity for every
finite abelian extension of a nonarchimedean local field. -/
theorem finiteAbelian_filteredLocalReciprocity
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (t : ℝ) (ht : 0 ≤ t) :
    artinPrincipalUnitStepGroup K L t =
      localUpperRamificationGroup K L t := by
  obtain ⟨d, n, hd, _hn, hEmbed⟩ :=
    exists_finiteAbelianDominatingStandardLubinTateCompositum K L
  let P := standardLubinTateFiniteAbelianCompositum K d n hd
  let F :=
    abstractFixedField K (SeparableClosure K) P.field
  letI : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) P.field
        (finiteAbelianSubextension_finite_over_absoluteBase K P)
  letI : IsAbelianGalois K F :=
    finiteAbelianSubextension_fixedField_isAbelianGalois K P
  let i : L →ₐ[K] F := hEmbed.some
  let j : L →ₐ[K] SeparableClosure K := F.val.comp i
  let E : IntermediateField K (SeparableClosure K) :=
    AlgHom.fieldRange j
  have hEF : E ≤ F := by
    rintro x ⟨y, rfl⟩
    exact (i y).property
  let e : L ≃ₐ[K] E :=
    AlgEquiv.ofInjectiveField j
  letI : FiniteDimensional K E :=
    e.toLinearEquiv.finiteDimensional
  letI : IsAbelianGalois K E :=
    IsAbelianGalois.of_algHom (IntermediateField.inclusion hEF)
  have hcover :
      ∀ s : ℝ, 0 ≤ s →
        artinPrincipalUnitStepGroup K F s =
          localUpperRamificationGroup K F s := by
    intro s hs
    exact
      standardLubinTateFiniteAbelianCompositum_filteredLocalReciprocity
        K d n hd s hs
  have hupper :
      ∀ s : ℝ,
        Subgroup.map
            (RamificationTheory.intermediateFieldRestrictNormalHom E F hEF)
            (localUpperRamificationGroup K F s) =
          localUpperRamificationGroup K E s := by
    intro s
    exact localUpperRamificationGroup_map_restrict K E F hEF s
  have hEfiltered :
      artinPrincipalUnitStepGroup K E t =
        localUpperRamificationGroup K E t :=
    filteredLocalReciprocity_descends
      K E F hEF
      (localUpperRamificationGroup K E)
      (localUpperRamificationGroup K F)
      hupper hcover t ht
  let q : Gal(E / K) ≃* Gal(L / K) :=
    AlgEquiv.autCongr e.symm
  have hArtin :
      Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) =
        artinPrincipalUnitStepGroup K L t :=
    artinPrincipalUnitStepGroup_map_standardFixedFieldEquiv
      K E L e.symm t
  have hUpper :
      Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) =
        localUpperRamificationGroup K L t :=
    localUpperRamificationGroup_map_autCongr K E L e.symm t
  calc
    artinPrincipalUnitStepGroup K L t =
        Subgroup.map q.toMonoidHom
          (artinPrincipalUnitStepGroup K E t) :=
      hArtin.symm
    _ =
        Subgroup.map q.toMonoidHom
          (localUpperRamificationGroup K E t) := by
      rw [hEfiltered]
    _ = localUpperRamificationGroup K L t := hUpper

end LocalClassFieldTheory

end
