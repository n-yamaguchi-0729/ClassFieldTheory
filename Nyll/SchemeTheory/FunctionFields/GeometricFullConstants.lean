/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.GeometricIntegrality
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSource
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Full constants of the original geometrically integral function field

A field whose tensor product with an algebraically closed field is a domain
has no new algebraic constants. Linear disjointness in a common field proves
this for actual elements and the original base inclusion. Applied to the
existing geometric-integrality theorem for the original function field, it
supplies the constant-field condition needed by normalized arithmetic degree.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace FieldTheory

/-- Geometric integrality of a field extension excludes every new algebraic
constant, with respect to the original algebra map. -/
theorem mem_base_of_isAlgebraic_of_tensorDomain
    (k K κ : Type*) [Field k] [Field K] [Field κ] [IsAlgClosed κ]
    [Algebra k K] [Algebra k κ] [IsDomain (K ⊗[k] κ)]
    (x : K) (hx : IsAlgebraic k x) : x ∈ (algebraMap k K).range := by
  obtain ⟨L, fieldL, algL, a, b, hab⟩ :=
    IntermediateField.LinearDisjoint.exists_field_of_isDomain k K κ
  let _ : Algebra κ L := b.toRingHom.toAlgebra
  have : IsScalarTower k κ L :=
    IsScalarTower.of_algebraMap_eq (fun c => (b.commutes c).symm)
  have hxκ : IsAlgebraic κ (a x) := (hx.algHom a).tower_top κ
  have hconstant : a x ∈ b.fieldRange := by
    exact minpoly.degree_eq_one_iff.mp
      (IsAlgClosed.degree_eq_one_of_irreducible κ (minpoly.irreducible hxκ.isIntegral))
  have hboth : a x ∈ a.fieldRange ⊓ b.fieldRange := ⟨⟨x, rfl⟩, hconstant⟩
  rw [hab.inf_eq_bot] at hboth
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hboth
  exact ⟨c, a.injective ((a.commutes c).trans hc)⟩

end FieldTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The original geometrically integral spectrum of a field has exactly
its specified base as algebraic constants. -/
theorem GeometricallyIntegral.field_fullConstants
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k K)))]
    (x : K) (hx : IsAlgebraic k x) : x ∈ (algebraMap k K).range := by
  let κ := AlgebraicClosure k
  let f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let g := Spec.map (CommRingCat.ofHom (algebraMap k κ))
  have : IsIntegral (pullback f g) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
  have : IsIntegral (Spec (.of (K ⊗[k] κ))) :=
    IsIntegral.of_isIso (pullbackSpecIso k K κ).hom
  have : IsDomain (K ⊗[k] κ) :=
    (affine_isIntegral_iff (.of (K ⊗[k] κ))).mp inferInstance
  exact FieldTheory.mem_base_of_isAlgebraic_of_tensorDomain k K κ x hx

/-- The same condition for the actual function field of the original
geometrically integral scheme, with the original morphism's scalar map. -/
theorem GeometricallyIntegral.functionField_fullConstants
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f] :
    let _ : Algebra k X.functionField := f.functionFieldAlgebra
    ∀ x : X.functionField, IsAlgebraic k x → x ∈ (algebraMap k X.functionField).range := by
  intro algF
  have : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k X.functionField))) :=
    GeometricallyIntegral.spec_functionField f
  exact GeometricallyIntegral.field_fullConstants k X.functionField

/-- A supplied generic field has the same full constants. Its actual
generic-source isomorphism and original structural-map square give geometric
integrality of its spectrum; no scalar-transport premise is added. -/
theorem GeometricallyIntegral.genericFieldSource_fullConstants
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [GeometricallyIntegral f]
    (p : Spec (.of F) ⟶ X) [IsDominant p] [IsPreimmersion p]
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k F)))
    (x : F) (hx : IsAlgebraic k x) : x ∈ (algebraMap k F).range := by
  let : Algebra k X.functionField := f.functionFieldAlgebra
  have hfield : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k X.functionField))) :=
    GeometricallyIntegral.spec_functionField f
  have hbase : X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) :=
    AlgebraicCurve.fromSpecStalk_genericPoint_comp_base f
  have hsource : (EtaleFundamentalGroups.genericFieldSourceIso p).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) =
        Spec.map (CommRingCat.ofHom (algebraMap k F)) := by
    exact (congrArg ((EtaleFundamentalGroups.genericFieldSourceIso p).hom ≫ ·)
      hbase.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f)
          (EtaleFundamentalGroups.genericFieldSourceIso_hom_fromSpecStalk p)).trans hp))
  have : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u}) := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_respectsIso _
  have hsourceIntegral : GeometricallyIntegral
      ((EtaleFundamentalGroups.genericFieldSourceIso p).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k X.functionField))) :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := (@GeometricallyIntegral : MorphismProperty Scheme.{u}))
      (EtaleFundamentalGroups.genericFieldSourceIso p).hom _).mpr hfield
  have : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k F))) := by
    rw [← hsource]
    exact hsourceIntegral
  exact GeometricallyIntegral.field_fullConstants k F x hx

end AlgebraicGeometry
