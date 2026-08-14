import LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology
import CyclicCohomology.GaloisCohomology

/-!
# The Hilbert-90 half of the local class-field axiom at every place

The degree-minus-one assertion for the archimedean local block is independent of
the nonarchimedean local reciprocity theorem.  It follows directly from
Hilbert 90 for the algebraic localization, and therefore applies also
at archimedean places.
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable section

namespace LocalClassFieldTheory

variable {K L : Type}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Hilbert 90 makes the local `H⁻¹` group trivial for an arbitrary
nontrivial absolute value, including an infinite place. -/
theorem localHerbrandHMinusOne_subsingleton
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    Subsingleton
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1)
          σ hgen)) := by
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  letI :=
    decompositionGroupLocalUnitsAction vK hvK w
  let E :=
    localHerbrandHMinusOneEquivUnitsTateHminusOne
      vK hvK w σ hgen
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  have hzero :
      CategoryTheory.Limits.IsZero
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) (-1)) :=
    hilbert90_unitsTateHminusOne_isZero
      vK.Completion (LocalizedCompletion vK w) g hg
  letI :
      Subsingleton
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) (-1)) :=
    ModuleCat.subsingleton_of_isZero hzero
  exact
    ⟨fun x y =>
      E.injective (Subsingleton.elim (E x) (E y))⟩

/-- The same universal Hilbert-90 conclusion as a finite-cardinality
statement. -/
theorem localHerbrandHMinusOne_card_eq_one_of_absoluteValue
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    Nat.card
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup K w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup K w.1)
          σ hgen)) = 1 := by
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionModuleFinite vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  letI : Fintype (absoluteValueDecompositionGroup K w.1) :=
    Fintype.ofFinite _
  letI :=
    decompositionGroupLocalUnitsAction vK hvK w
  letI :
      Subsingleton
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup K w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup K w.1)
            σ hgen)) :=
    localHerbrandHMinusOne_subsingleton
      vK hvK w σ hgen
  exact Nat.card_unique

end LocalClassFieldTheory
