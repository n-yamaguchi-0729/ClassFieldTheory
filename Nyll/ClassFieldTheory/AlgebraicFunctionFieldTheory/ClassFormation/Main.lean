/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.CohomologyBridge
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.CyclicClassFieldAxiom
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport

/-!
# The function-field idele-class formation

Every finite abstract cyclic extension is realized by its actual fixed fields.
The equivariant fixed-coefficient comparison transports the proved finite
cyclic idele-class Tate calculation to the abstract class-field axiom.
-/

noncomputable section

namespace FunctionField

open CategoryTheory ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- The actual finite-extension idele-class representation satisfies the class-field axiom. -/
theorem ideleClassRepresentation_satisfiesClassFieldAxiom :
    SatisfiesClassFieldAxiom (ideleClassRepresentation k K Ω) := by
  rintro ⟨H, hHfinite⟩ ⟨J, hJH, hnormal, hfinite, g, hg⟩
  have hHf := hHfinite
  have hJHf := hfinite
  have hnorm := hnormal
  have hJfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) J (le_baseField J)) :=
    FiniteGaloisSubextension.finite_extension_trans hJH (le_baseField H)
  let F := abstractFixedField K Ω H
  let E := abstractFixedField K Ω J
  have hFfinite : FiniteDimensional K F := abstractFixedField_finiteDimensional K Ω H hHfinite
  have hEfinite : FiniteDimensional K E := abstractFixedField_finiteDimensional K Ω J hJfinite
  let aFE : Algebra F E :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
  have hKFE : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkFE : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hFEfinite : FiniteDimensional F E :=
    abstractFixedField_relativeFiniteDimensional K Ω H J hJH hHfinite hfinite
  have hFEgalois : IsGalois F E := abstractRelativeFixedField_isGalois K Ω H J hJH hnormal
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let hQfintype : Fintype Q := Fintype.ofFinite Q
  let eQ : Q ≃* Gal(E/F) := abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hnormal
  let g' : Gal(E/F) := eQ g
  have hg' : ∀ σ : Gal(E/F), σ ∈ Subgroup.zpowers g' := map_cyclicGenerator eQ g hg
  have hcard := IdeleClassGroup.tate_lowDegree_finite_card_eq_finrank (k := k) g' hg'
  have hQcyclic : IsCyclic Q := isCyclic_of_generator g hg
  let hQcomm : CommGroup Q := IsCyclic.commGroup
  have hEcyclic : IsCyclic Gal(E/F) := isCyclic_of_generator g' hg'
  let hEcomm : CommGroup Gal(E/F) := IsCyclic.commGroup
  let M := extensionFixedRepresentation (ideleClassRepresentation k K Ω) H J hJH hnormal
  let U := Rep.ofMulDistribMulAction Gal(E/F) (IdeleClassGroup k E)
  let eM : M ≅ Rep.res eQ.toMonoidHom U :=
    extensionClassRepresentationIso k K Ω H J hJH hnormal hJfinite
  let eH0 : (Rep.FiniteCyclicGroup.normHomCompSub M g).homology ≅
      (Rep.FiniteCyclicGroup.normHomCompSub U g').homology :=
    normHomCompSubHomologyIsoOfRepIso eM g ≪≫ normHomCompSubHomologyResEquivIso eQ U g
  let eHm : (Rep.FiniteCyclicGroup.subCompNormHom M g).homology ≅
      (Rep.FiniteCyclicGroup.subCompNormHom U g').homology :=
    subCompNormHomHomologyIsoOfRepIso eM g ≪≫ subCompNormHomHomologyResEquivIso eQ U g
  let e0 : tateCohomology M 0 ≅ tateCohomology U 0 :=
    TateCohomology.isoFiniteCyclicZero M g hg ≪≫ eH0 ≪≫
      (TateCohomology.isoFiniteCyclicZero U g' hg').symm
  let em : tateCohomology M (-1) ≅ tateCohomology U (-1) :=
    TateCohomology.isoFiniteCyclicNegOne M g hg ≪≫ eHm ≪≫
      (TateCohomology.isoFiniteCyclicNegOne U g' hg').symm
  have h0 : Finite (tateCohomology U 0) := hcard.1
  have hm : Finite (tateCohomology U (-1)) := hcard.2.1
  refine
    { finiteTateHZero := Finite.of_equiv (tateCohomology U 0) e0.symm.toLinearEquiv.toEquiv
      finiteTateHMinusOne := Finite.of_equiv (tateCohomology U (-1)) em.symm.toLinearEquiv.toEquiv
      tateHZero_card := ?_
      tateHMinusOne_card := ?_ }
  · exact (Nat.card_congr e0.toLinearEquiv.toEquiv).trans (hcard.2.2.1.trans
      (finiteAbstractExtension_degree_eq_finrank K Ω H J hJH hnormal hHfinite hfinite).symm)
  · exact (Nat.card_congr em.toLinearEquiv.toEquiv).trans hcard.2.2.2

end FunctionField
