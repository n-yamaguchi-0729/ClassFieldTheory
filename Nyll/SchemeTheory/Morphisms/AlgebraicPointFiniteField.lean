/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-!
# An algebraic point is defined over a finite intermediate field

For a separated scheme locally of finite type, a specified point over an
algebraic extension factors through an actual finite intermediate field.
The factorization retains the original point and its structural morphism.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A specified algebraic point has an actual finite field of definition. -/
theorem exists_finite_intermediateField_point_factorization
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsSeparated f]
    (p : Spec (CommRingCat.of Ω) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ E : IntermediateField k Ω, Module.Finite k E ∧
      ∃ q : Spec (CommRingCat.of E) ⟶ X,
        q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
        Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ q = p := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective p
  change (Spec.map a ≫ X.fromSpecResidueField x) ≫ f = _ at hp
  let p := Spec.map a ≫ X.fromSpecResidueField x
  have : IsIntegralHom (p ≫ f) := by
    rw [show p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) from hp]
    exact IsIntegralHom.SpecMap_iff.mpr (Algebra.IsIntegral.isIntegral (R := k))
  have : IsIntegralHom p := IsIntegralHom.of_comp p f
  let t : ↥(Spec (CommRingCat.of Ω)) := IsLocalRing.closedPoint Ω
  have hx : IsClosed ({x} : Set X) := by
    have he : p '' ({t} : Set (Spec (CommRingCat.of Ω))) = {x} := by
      rw [Set.image_singleton]
      congr 1
      exact X.fromSpecResidueField_apply x _
    rw [← he]
    exact p.isClosedMap _ (IsLocalRing.isClosed_singleton_closedPoint Ω)
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) := by
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let b := Spec.preimage (X.fromSpecResidueField x ≫ f)
  let κ : Type u := X.residueField x
  let : Algebra k κ := b.hom.toAlgebra
  have : Module.Finite k κ := (IsFinite.SpecMap_iff b).mp (by
    simpa only [b, Spec.map_preimage] using hfin)
  have hba : b ≫ a = CommRingCat.ofHom (algebraMap k Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact (Category.assoc _ _ _).symm.trans hp
  let j : κ →ₐ[k] Ω :=
    { a.hom with commutes' := fun r => congrArg (fun h : CommRingCat.of k ⟶
        CommRingCat.of Ω => h.hom r) hba }
  let E := j.fieldRange
  let e := j.equivFieldRange
  have hE : Module.Finite k E := Module.Finite.of_surjective e.toLinearMap e.surjective
  refine ⟨E, hE, Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x,
    ?_, ?_⟩
  · rw [Category.assoc, ← Spec.map_preimage (X.fromSpecResidueField x ≫ f), ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact congrArg (fun z : E => (z : Ω)) (e.commutes r)
  · change Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x) = p
    rw [← Spec.map_comp_assoc]
    rfl

end AlgebraicGeometry
