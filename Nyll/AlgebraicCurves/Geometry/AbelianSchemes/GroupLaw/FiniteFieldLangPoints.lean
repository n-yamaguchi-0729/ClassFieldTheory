/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.FiniteFieldLang
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.LangPointFormula
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints

/-!
# Frobenius coboundaries on actual algebraic points

Lang surjectivity is expressed in the existing group of algebra-valued points,
with its existing action of automorphisms of the constant field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem mul_inv_change_base {R : Type} [CommRing R] {A T : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x y : SchemeHomOver t f) :
    (L.mul t x (L.inv t y)).val =
      (L.mul t' ⟨x.val, x.property.trans h⟩
        (L.inv t' ⟨y.val, y.property.trans h⟩)).val := by
  subst t'
  rfl

variable (k Ω : Type) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of k))]
    (L : RelativeGroupLaw k (X ↘ Spec (CommRingCat.of k))) (hc : L.IsCommutative)

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "g" => pullback.snd f b

private local instance constantSpecOver :
    (Spec (CommRingCat.of Ω)).Over (Spec (CommRingCat.of k)) := ⟨b⟩

/-- A geometric point of the base change as an actual algebra-valued original point. -/
def finiteFieldGeometricPoint (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g) :
    L.AlgPoints hc Ω :=
  AlgPoints.ofPoint ⟨(baseChangePointToBase b x).val, by
    simpa only [Category.id_comp] using (baseChangePointToBase b x).property⟩

omit [Fintype k] [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω] in
/-- Every actual algebra-valued point is represented by a geometric point of the base change. -/
theorem finiteFieldGeometricPoint_surjective :
    Function.Surjective (finiteFieldGeometricPoint k Ω X L hc) := by
  intro y
  let y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω)) ≫ b) f :=
    ⟨(AlgPoints.toPoint y).val, by
      simpa only [Category.id_comp] using (AlgPoints.toPoint y).property⟩
  refine ⟨baseChangePointOfBase b y', ?_⟩
  apply AlgPoints.toPoint_injective
  exact Subtype.ext (pullback.lift_fst _ _ _)

omit [IsAlgClosed Ω] in
/-- The geometric Frobenius agrees with the existing Galois action on algebraic points. -/
theorem finiteFieldGeometricPoint_frobenius
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g) :
    finiteFieldGeometricPoint k Ω X L hc
        (NeronModelInfra.schemeHomOverComp x (finiteFieldFrobeniusOver k Ω X)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k Ω •
        finiteFieldGeometricPoint k Ω X L hc x := by
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  change (x.val ≫ Scheme.constantBaseChangeFrobenius k Ω X) ≫ pullback.fst f b =
    Spec.map (CommRingCat.ofHom (FiniteField.frobeniusAlgHom k Ω).toRingHom) ≫
      (x.val ≫ pullback.fst f b)
  rw [Category.assoc, Scheme.constantBaseChangeFrobenius_fst, ← Category.assoc]
  have hn := Scheme.finiteFieldFrobenius_naturality (Spec (CommRingCat.of Ω)) k X
    (x.val ≫ pullback.fst f b)
  rw [Scheme.finiteFieldFrobenius_spec] at hn
  exact hn.symm

omit [Fintype k] [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω] in
/-- Evaluation of any Lang map agrees with subtraction in the original algebraic point group. -/
theorem finiteFieldGeometricPoint_langMap_apply (β : SchemeHomOver g g)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g) :
    finiteFieldGeometricPoint k Ω X L hc
        (NeronModelInfra.schemeHomOverComp x ((L.baseChange b).langMap (hc.baseChange b) β)) =
      finiteFieldGeometricPoint k Ω X L hc (NeronModelInfra.schemeHomOverComp x β) -
        finiteFieldGeometricPoint k Ω X L hc x := by
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  have h := congrArg (fun z => (baseChangePointToBase b z).val)
    ((L.baseChange b).comp_langMap (hc.baseChange b) β x)
  rw [baseChangePointToBase_mul, baseChangePointToBase_inv] at h
  simp only [finiteFieldGeometricPoint, sub_eq_add_neg, AlgPoints.toPoint_add,
    AlgPoints.toPoint_neg, AlgPoints.toPoint_ofPoint]
  exact h.trans (mul_inv_change_base L (Category.id_comp b) _ _)

omit [IsAlgClosed Ω] in
/-- The geometric Lang map is exactly the Frobenius coboundary in the actual point group. -/
theorem finiteFieldGeometricPoint_langMap
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) g) :
    finiteFieldGeometricPoint k Ω X L hc
        (NeronModelInfra.schemeHomOverComp x (finiteFieldLangMap k Ω X L hc)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k Ω •
        finiteFieldGeometricPoint k Ω X L hc x - finiteFieldGeometricPoint k Ω X L hc x := by
  exact (finiteFieldGeometricPoint_langMap_apply k Ω X L hc
    (finiteFieldFrobeniusOver k Ω X) x).trans
      (congrArg (· - finiteFieldGeometricPoint k Ω X L hc x)
        (finiteFieldGeometricPoint_frobenius k Ω X L hc x))

/-- Every actual algebraic point is a Frobenius coboundary, in every characteristic. -/
theorem surjective_frobenius_sub
    (hX : AbelianSchemePropertyBundle k (X ↘ Spec (CommRingCat.of k))) :
    Function.Surjective (fun x : L.AlgPoints hc Ω =>
      FiniteField.frobeniusAlgEquivOfAlgebraic k Ω • x - x) := by
  intro y
  obtain ⟨y', hy⟩ := finiteFieldGeometricPoint_surjective k Ω X L hc y
  obtain ⟨x, hx⟩ := surjective_finiteFieldLangMap_points k Ω X L hc hX y'
  refine ⟨finiteFieldGeometricPoint k Ω X L hc x, ?_⟩
  change FiniteField.frobeniusAlgEquivOfAlgebraic k Ω •
    finiteFieldGeometricPoint k Ω X L hc x - finiteFieldGeometricPoint k Ω X L hc x = y
  exact (finiteFieldGeometricPoint_langMap k Ω X L hc x).symm.trans
    ((congrArg (finiteFieldGeometricPoint k Ω X L hc) hx).trans hy)

end GoodReductionJacobian.RelativeGroupLaw
