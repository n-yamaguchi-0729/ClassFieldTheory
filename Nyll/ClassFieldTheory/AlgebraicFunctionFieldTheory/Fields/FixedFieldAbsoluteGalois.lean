/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiniteQuotients
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.InfiniteGaloisCorrespondence

/-!
# The actual absolute Galois group of a finite fixed field

The original fixed-subgroup equivalence is a homeomorphism for the Krull
topologies. A separable-closure equivalence then identifies the native
absolute Galois group of the finite fixed field with the original ambient
subgroup. The induced topological abelianization equivalence retains this
literal conjugation formula.
-/

@[expose] public section

universe v w

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory ProCGroups.Abelian

variable (K : Type v) (Ω : Type w) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The original closed-subgroup/Galois-group equivalence preserves the
actual Krull topologies when the fixed field is finite over the base. -/
def finiteAbstractSubgroupGaloisEquiv
    (H : FiniteAbstractField Gal(Ω/K)) :
    H.field.toSubgroup ≃ₜ* Gal(Ω/abstractFixedField K Ω H.field) := by
  let F := abstractFixedField K Ω H.field
  have hfinite : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional K Ω H.field H.finite
  have hgal : IsGalois F Ω := IsGalois.tower_top_of_isGalois K F Ω
  let e := abstractSubgroupEquivGaloisGroup K Ω H.field
  have hcontinuous : Continuous e.symm := by
    exact (RamificationTheory.Field.absoluteGaloisGroup.ofIntermediateFieldInExtension_continuous
      F).subtype_mk (fun σ => (e.symm σ).property)
  let h := Continuous.homeoOfEquivCompactToT2 (f := e.symm.toEquiv) hcontinuous
  exact
    { toMulEquiv := e
      continuous_toFun := h.symm.continuous
      continuous_invFun := h.continuous }

/-- This homeomorphism retains the original underlying automorphism. -/
theorem finiteAbstractSubgroupGaloisEquiv_apply
    (H : FiniteAbstractField Gal(Ω/K)) (σ : H.field.toSubgroup) (x : Ω) :
    finiteAbstractSubgroupGaloisEquiv K Ω H σ x = σ.val x := rfl

/-- The inverse is literal restriction of scalars to the original base. -/
theorem finiteAbstractSubgroupGaloisEquiv_symm_val
    (H : FiniteAbstractField Gal(Ω/K))
    (σ : Gal(Ω/abstractFixedField K Ω H.field)) :
    ((finiteAbstractSubgroupGaloisEquiv K Ω H).symm σ).val = σ.restrictScalars K := rfl

/-- Conjugation by an actual separable-closure equivalence identifies the
native absolute Galois group with the original finite-index subgroup. -/
def fixedFieldAbsoluteGaloisEquivOfClosure
    (H : FiniteAbstractField Gal(Ω/K))
    (e : SeparableClosure (abstractFixedField K Ω H.field) ≃ₐ[abstractFixedField K Ω H.field] Ω) :
    Gal(SeparableClosure (abstractFixedField K Ω H.field)/(abstractFixedField K Ω H.field)) ≃ₜ*
      H.field.toSubgroup :=
  ({ toMulEquiv := AlgEquiv.autCongr e
     continuous_toFun :=
       RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_continuous e
     continuous_invFun :=
       RamificationTheory.Field.absoluteGaloisGroup.algEquiv_autCongr_symm_continuous e } :
    Gal(SeparableClosure (abstractFixedField K Ω H.field)/(abstractFixedField K Ω H.field)) ≃ₜ*
      Gal(Ω/abstractFixedField K Ω H.field)).trans
    (finiteAbstractSubgroupGaloisEquiv K Ω H).symm

/-- The subgroup automorphism is the actual conjugate by the closure
equivalence, evaluated on the original ambient field. -/
theorem fixedFieldAbsoluteGaloisEquivOfClosure_apply
    (H : FiniteAbstractField Gal(Ω/K))
    (e : SeparableClosure (abstractFixedField K Ω H.field) ≃ₐ[abstractFixedField K Ω H.field] Ω)
    (σ : Gal(SeparableClosure (abstractFixedField K Ω H.field)/(abstractFixedField K Ω H.field)))
    (x : Ω) :
    (fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e σ).val x =
      e (σ (e.symm x)) := rfl

/-- The induced equivalence identifies the native absolute abelian group
with the topological abelianization of the actual ambient subgroup. -/
def fixedFieldAbsoluteAbelianEquivOfClosure
    (H : FiniteAbstractField Gal(Ω/K))
    (e : SeparableClosure (abstractFixedField K Ω H.field) ≃ₐ[abstractFixedField K Ω H.field] Ω) :
    localAbsoluteAbelianProfinite (abstractFixedField K Ω H.field) ≃ₜ*
      TopologicalAbelianization H.field.toSubgroup :=
  TopologicalAbelianization.congr (fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e)

/-- The abelian equivalence is induced by the original conjugation of
absolute automorphisms. -/
theorem fixedFieldAbsoluteAbelianEquivOfClosure_mk
    (H : FiniteAbstractField Gal(Ω/K))
    (e : SeparableClosure (abstractFixedField K Ω H.field) ≃ₐ[abstractFixedField K Ω H.field] Ω)
    (σ : Gal(SeparableClosure (abstractFixedField K Ω H.field)/(abstractFixedField K Ω H.field))) :
    fixedFieldAbsoluteAbelianEquivOfClosure K Ω H e (QuotientGroup.mk σ) =
      TopologicalAbelianization.mk H.field.toSubgroup
        (fixedFieldAbsoluteGaloisEquivOfClosure K Ω H e σ) := rfl

variable [IsSepClosed Ω]

/-- The original ambient separable closure is also a separable closure of
each finite fixed field. This supplies the closure equivalence used above. -/
def fixedFieldSeparableClosureEquiv
    (H : FiniteAbstractField Gal(Ω/K)) :
    SeparableClosure (abstractFixedField K Ω H.field) ≃ₐ[abstractFixedField K Ω H.field] Ω := by
  let F := abstractFixedField K Ω H.field
  have hsep : Algebra.IsSeparable F Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K F Ω
  have hclosure : IsSepClosure F Ω := ⟨inferInstance, hsep⟩
  exact IsSepClosure.equiv F (SeparableClosure F) Ω

/-- A chosen actual identification of the finite fixed field's absolute
Galois group with its original ambient subgroup. -/
def fixedFieldAbsoluteGaloisEquiv
    (H : FiniteAbstractField Gal(Ω/K)) :
    Gal(SeparableClosure (abstractFixedField K Ω H.field)/(abstractFixedField K Ω H.field)) ≃ₜ*
      H.field.toSubgroup :=
  fixedFieldAbsoluteGaloisEquivOfClosure K Ω H (fixedFieldSeparableClosureEquiv K Ω H)

/-- The corresponding chosen equivalence of actual topological
abelianizations. -/
def fixedFieldAbsoluteAbelianEquiv
    (H : FiniteAbstractField Gal(Ω/K)) :
    localAbsoluteAbelianProfinite (abstractFixedField K Ω H.field) ≃ₜ*
      TopologicalAbelianization H.field.toSubgroup :=
  fixedFieldAbsoluteAbelianEquivOfClosure K Ω H (fixedFieldSeparableClosureEquiv K Ω H)

end FunctionField
