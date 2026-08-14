import Mathlib.SetTheory.Cardinal.Finite
import GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
import GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
import LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits

/-!
# The rational idele-class formation

This module identifies the fixed-field idele-class representation with
concrete relative idele class groups and transfers the cyclic low-degree Tate
cohomology calculation to prove the abstract class-field axiom.
-/

namespace GlobalClassFieldTheory

open scoped NumberField TensorProduct
open NumberField
open CyclicCohomology ClassFormation
open LocalClassFieldTheory

noncomputable section

open CategoryTheory

namespace Reciprocity

/-- The rational absolute idele-class representation satisfies the
abstract class-field axiom. -/
theorem rationalIdeleClassRepresentation_satisfiesClassFieldAxiom :
    SatisfiesClassFieldAxiom rationalIdeleClassRepresentation := by
  rintro ⟨K, hKfinite⟩
  rintro ⟨L, hLK, hnormal, hfinite, g, hg⟩
  letI := hKfinite
  letI := hnormal
  letI := hfinite
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  letI : Fintype Q := Fintype.ofFinite Q
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eQ : Q ≃* Gal(E / F) :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let g' : Gal(E / F) := eQ g
  have hg' : ∀ σ : Gal(E / F),
      σ ∈ Subgroup.zpowers g' :=
    map_cyclicGenerator eQ g hg
  letI :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  have hIdeleClassTateCard :=
    ClassFieldAxiom.ideleClass_tate_lowDegree_finite_card_eq_finrank_cyclic
      F E g' hg'
  letI : IsCyclic Q :=
    CyclicCohomology.isCyclic_of_generator g hg
  letI : CommGroup Q := IsCyclic.commGroup
  letI : IsCyclic (Gal(E / F)) :=
    CyclicCohomology.isCyclic_of_generator g' hg'
  letI : CommGroup (Gal(E / F)) := IsCyclic.commGroup
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let U :=
    Rep.ofMulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E)
  let eM : M ≅ Rep.res eQ.toMonoidHom U := by
    let e :=
      rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
    refine Rep.mkIso (Representation.Equiv.mk e.toIntLinearEquiv ?_)
    intro q
    apply LinearMap.ext
    intro x
    exact
      rationalAbstractExtensionIdeleClassEquiv_action
        K L hLK hnormal q x
  let eH0 :
      (Rep.FiniteCyclicGroup.normHomCompSub M g).homology ≅
        (Rep.FiniteCyclicGroup.normHomCompSub U g').homology :=
    (normHomCompSubHomologyIsoOfRepIso eM g) ≪≫
      normHomCompSubHomologyResEquivIso eQ U g
  let eHm1 :
      (Rep.FiniteCyclicGroup.subCompNormHom M g).homology ≅
        (Rep.FiniteCyclicGroup.subCompNormHom U g').homology :=
    (subCompNormHomHomologyIsoOfRepIso eM g) ≪≫
      subCompNormHomHomologyResEquivIso eQ U g
  let eTateH0 :
      tateCohomology M 0 ≅ tateCohomology U 0 :=
    TateCohomology.isoFiniteCyclicZero M g hg ≪≫ eH0 ≪≫
      (TateCohomology.isoFiniteCyclicZero U g' hg').symm
  let eTateHm1 :
      tateCohomology M (-1) ≅ tateCohomology U (-1) :=
    TateCohomology.isoFiniteCyclicNegOne M g hg ≪≫ eHm1 ≪≫
      (TateCohomology.isoFiniteCyclicNegOne U g' hg').symm
  letI : Finite (tateCohomology U 0) := hIdeleClassTateCard.1
  letI : Finite (tateCohomology U (-1)) := hIdeleClassTateCard.2.1
  letI : Finite (tateCohomology M 0) :=
    Finite.of_equiv
      (tateCohomology U 0) eTateH0.symm.toLinearEquiv.toEquiv
  letI : Finite (tateCohomology M (-1)) :=
    Finite.of_equiv
      (tateCohomology U (-1)) eTateHm1.symm.toLinearEquiv.toEquiv
  refine
    { finiteTateHZero := by
        change Finite (tateCohomology M 0)
        infer_instance
      finiteTateHMinusOne := by
        change Finite (tateCohomology M (-1))
        infer_instance
      tateHZero_card := ?_
      tateHMinusOne_card := ?_ }
  · change Nat.card (tateCohomology M 0) =
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        L K hLK).degree : ℕ)
    calc
      Nat.card (tateCohomology M 0) =
          Nat.card (tateCohomology U 0) :=
        Nat.card_congr eTateH0.toLinearEquiv.toEquiv
      _ = Module.finrank F E := hIdeleClassTateCard.2.2.1
      _ =
          ((DegreeData.FiniteAbstractExtension.ofInclusion
            L K hLK).degree : ℕ) :=
        (finiteAbstractExtension_degree_eq_finrank
          ℚ (SeparableClosure ℚ) K L hLK hnormal
            hKfinite hfinite).symm
  · change Nat.card (tateCohomology M (-1)) = 1
    calc
      Nat.card (tateCohomology M (-1)) =
          Nat.card (tateCohomology U (-1)) :=
        Nat.card_congr eTateHm1.toLinearEquiv.toEquiv
      _ = 1 := hIdeleClassTateCard.2.2.2

end Reciprocity

end
end GlobalClassFieldTheory
