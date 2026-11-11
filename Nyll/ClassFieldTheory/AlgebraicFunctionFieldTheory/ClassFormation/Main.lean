/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.CohomologyBridge
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.CyclicClassFieldAxiom
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
public import Nyll.GaloisCohomology.Cyclic.IntegralCyclicNormComplexes
public import Nyll.GaloisCohomology.Cyclic.IntegralCyclicNormTransport
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology

/-!
# The function-field idele-class formation

Every finite abstract cyclic extension is realized by its actual fixed fields.
The equivariant fixed-coefficient comparison transports the proved finite
cyclic idele-class Tate calculation to the abstract class-field axiom.
-/

@[expose] public section

universe u v w

noncomputable section

namespace FunctionField

open CategoryTheory ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

open IntegralGroupCohomology.Universe in
private theorem classFieldAxiomCohomologyData_of_repIso
    {G : Type u} {P : Type v} [Group G] [TopologicalSpace G] [Group P] [Fintype P]
    (A : Rep.{w} ℤ G) (B : FiniteAbstractField G) (C : FiniteCyclicSubextension B)
    (e : (B.field.toSubgroup ⧸ extensionSubgroup B.field C.field C.below) ≃* P)
    (U : Rep.{w} ℤ P) (eM : C.fixedRepresentation A ≅ Rep.res e.toMonoidHom U)
    (hcard : Finite (tate U 0) ∧ Finite (tate U (-1)) ∧
      Nat.card (tate U 0) = Nat.card P ∧ Nat.card (tate U (-1)) = 1) :
    ClassFieldAxiomCohomologyData A B C := by
  let Q := B.field.toSubgroup ⧸ extensionSubgroup B.field C.field C.below
  let g : Q := C.generator
  let g' : P := e g
  have hg' : ∀ σ : P, σ ∈ Subgroup.zpowers g' := map_cyclicGenerator e g C.generates
  let M : Rep.{w} ℤ Q := C.fixedRepresentation A
  let eH0 : (normHomCompSub M g).homology ≅ (normHomCompSub U g').homology :=
    normHomCompSubHomologyIsoOfRepIso eM g ≪≫ normHomCompSubHomologyResEquivIso e U g
  let eHm : (subCompNormHom M g).homology ≅ (subCompNormHom U g').homology :=
    subCompNormHomHomologyIsoOfRepIso eM g ≪≫ subCompNormHomHomologyResEquivIso e U g
  let e0 : tate M 0 ≃+ tate U 0 :=
    (normHomologyEquivTateZero M g C.generates).symm.trans
      (eH0.toLinearEquiv.toAddEquiv.trans (normHomologyEquivTateZero U g' hg'))
  let em : tate M (-1) ≃+ tate U (-1) :=
    (subNormHomologyEquivTateMinusOne M g C.generates).symm.trans
      (eHm.toLinearEquiv.toAddEquiv.trans (subNormHomologyEquivTateMinusOne U g' hg'))
  have h0 : Finite (tate U 0) := hcard.1
  have hm : Finite (tate U (-1)) := hcard.2.1
  have hdegree : Nat.card Q = (C.toFiniteAbstractExtension.degree : ℕ) :=
    (Subgroup.index_eq_card (extensionSubgroup B.field C.field C.below)).symm.trans
      C.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree
  exact ⟨Finite.of_equiv (tate U 0) e0.symm.toEquiv,
    Finite.of_equiv (tate U (-1)) em.symm.toEquiv,
    (Nat.card_congr e0.toEquiv).trans (hcard.2.2.1.trans
      ((Nat.card_congr e.toEquiv).symm.trans hdegree)),
    (Nat.card_congr em.toEquiv).trans hcard.2.2.2⟩

open AlgebraicCurve IntegralGroupCohomology.Universe in
private theorem ideleClassTateCardinalities_eq_cardAut
    {k : Type u} {F : Type v} {E : Type w} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [FiniteDimensional F E] [IsGalois F E]
    [HasPrincipalDivisors k F] [HasPrincipalDivisors k E]
    [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E] [FunctionField k E]
    (g : Gal(E/F)) (hg : ∀ σ : Gal(E/F), σ ∈ Subgroup.zpowers g) :
    let U := Rep.ofMulDistribMulAction Gal(E/F) (IdeleClassGroup k E)
    Finite (tate U 0) ∧ Finite (tate U (-1)) ∧
      Nat.card (tate U 0) = Nat.card Gal(E/F) ∧ Nat.card (tate U (-1)) = 1 := by
  intro U
  have hcard : Finite (tate U 0) ∧ Finite (tate U (-1)) ∧
      Nat.card (tate U 0) = Module.finrank F E ∧ Nat.card (tate U (-1)) = 1 :=
    IdeleClassGroup.integral_tate_lowDegree_finite_card_eq_finrank (k := k) g hg
  have hdegree : Module.finrank F E = Nat.card Gal(E/F) :=
    (IsGalois.card_aut_eq_finrank F E).symm
  exact ⟨hcard.1, hcard.2.1, hcard.2.2.1.trans hdegree, hcard.2.2.2⟩

variable (k : Type u) (K : Type v) (Ω : Type w) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- The actual finite-extension idele-class representation satisfies the class-field axiom. -/
theorem ideleClassRepresentation_satisfiesClassFieldAxiom :
    SatisfiesClassFieldAxiom (ideleClassRepresentation k K Ω) := by
  intro B C
  let H := B.field
  let J := C.field
  let hJH := C.below
  have hJfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) J (le_baseField J)) :=
    FiniteGaloisSubextension.finite_extension_trans hJH (le_baseField H)
  let F := abstractFixedField K Ω H
  let E := abstractFixedField K Ω J
  let : FiniteDimensional K F := abstractFixedField_finiteDimensional K Ω H B.finite
  let : FiniteDimensional K E := abstractFixedField_finiteDimensional K Ω J hJfinite
  let : Algebra F E :=
    (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let : FiniteDimensional F E :=
    abstractFixedField_relativeFiniteDimensional K Ω H J hJH B.finite C.finite
  let : IsGalois F E := abstractRelativeFixedField_isGalois K Ω H J hJH C.normal
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let eQ : Q ≃* Gal(E/F) := abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH C.normal
  let g' : Gal(E/F) := eQ C.generator
  have hg' : ∀ σ : Gal(E/F), σ ∈ Subgroup.zpowers g' :=
    map_cyclicGenerator eQ C.generator C.generates
  let U : Rep.{w} ℤ Gal(E/F) := Rep.ofMulDistribMulAction Gal(E/F) (IdeleClassGroup k E)
  have hcardAut := ideleClassTateCardinalities_eq_cardAut (k := k) (F := F) (E := E) g' hg'
  let eM : C.fixedRepresentation (ideleClassRepresentation k K Ω) ≅ Rep.res eQ.toMonoidHom U :=
    extensionClassRepresentationIso k K Ω H J hJH C.normal hJfinite
  exact classFieldAxiomCohomologyData_of_repIso
    (ideleClassRepresentation k K Ω) B C eQ U eM hcardAut

end FunctionField
