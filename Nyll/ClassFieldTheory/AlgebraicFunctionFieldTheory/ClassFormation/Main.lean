/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.CohomologyBridge
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.CyclicClassFieldAxiom
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
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

omit [IsGalois K Ω] in
open IntegralGroupCohomology.Universe in
private theorem ideleClassRepresentation_cyclicCohomologyData_of_iso
    (B : FiniteAbstractField Gal(Ω/K)) (C : FiniteCyclicSubextension B)
    {F E : Type w} [Field F] [Field E] [Algebra k F] [Algebra k E]
    [Algebra F E] [IsScalarTower k F E]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E] [FunctionField k E]
    [FiniteDimensional F E] [IsGalois F E]
    [AlgebraicCurve.HasPrincipalDivisors k F] [AlgebraicCurve.HasPrincipalDivisors k E]
    (eQ : (B.field.toSubgroup ⧸ extensionSubgroup B.field C.field C.below) ≃* Gal(E/F)) :
    let U : Rep.{w} ℤ Gal(E/F) := Rep.ofMulDistribMulAction Gal(E/F) (IdeleClassGroup k E)
    (C.fixedRepresentation (ideleClassRepresentation k K Ω) ≅ Rep.res eQ.toMonoidHom U) →
      ClassFieldAxiomCohomologyData (ideleClassRepresentation k K Ω) B C := by
  intro U eM
  let : IsCyclic (B.field.toSubgroup ⧸ extensionSubgroup B.field C.field C.below) := C.cyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := B.field.toSubgroup ⧸ extensionSubgroup B.field C.field C.below)
  have hg' : ∀ σ : Gal(E/F), σ ∈ Subgroup.zpowers (eQ g) := map_cyclicGenerator eQ g hg
  have hcard : Finite (tate U 0) ∧ Finite (tate U (-1)) ∧
      Nat.card (tate U 0) = Nat.card Gal(E/F) ∧ Nat.card (tate U (-1)) = 1 :=
    ideleClassTateCardinalities_eq_cardAut (k := k) (eQ g) hg'
  exact ClassFieldAxiomCohomologyData.of_repIso
    (ideleClassRepresentation k K Ω) B C g hg eQ hg' U eM hcard.1 hcard.2.2.1 hcard.2.2.2

open IntegralGroupCohomology.Universe in
private theorem ideleClassRepresentation_cyclicCohomologyData
    (B : FiniteAbstractField Gal(Ω/K)) (C : FiniteCyclicSubextension B) :
    ClassFieldAxiomCohomologyData (ideleClassRepresentation k K Ω) B C := by
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
  let : (extensionSubgroup H J hJH).Normal := C.normal
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let eQ : Q ≃* Gal(E/F) := abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH C.normal
  apply ideleClassRepresentation_cyclicCohomologyData_of_iso k K Ω B C eQ
  exact extensionClassRepresentationIso k K Ω H J hJH C.normal hJfinite

/-- The actual finite-extension idele-class representation satisfies the class-field axiom. -/
theorem ideleClassRepresentation_satisfiesClassFieldAxiom :
    SatisfiesClassFieldAxiom (ideleClassRepresentation k K Ω) :=
  ideleClassRepresentation_cyclicCohomologyData k K Ω

end FunctionField
