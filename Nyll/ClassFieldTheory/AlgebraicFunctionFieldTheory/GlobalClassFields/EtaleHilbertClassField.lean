/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.EtaleClosedPoints
public import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegEqOneIsRational
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassField

/-!
# Actual finite étale curve covers and the Hilbert class field

For a finite abelian function-field extension, a finite étale map of its
actual smooth proper models gives the unramifiedness conditions in global
class field theory. Rational sections through the actual points over a
chosen rational base point give complete splitting. The resulting inclusion
is in the original separable closure, with its original field embedding.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped AlgebraicCurve.Place

namespace FunctionField

variable (k : Type u) (K : Type v) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- An actual finite abelian étale curve cover whose fiber over the chosen
rational point consists of rational sections lies in the corresponding
Hilbert class field. Ramification indices and inertia degrees are derived
from the curve map and its actual fiber points. -/
theorem finiteEtale_le_hilbertClassField_of_rational_fiber
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    ∀ (M : CurveModel k K) (N : CurveModel k E.val)
      (π : N.C ⟶ M.C) [IsFinite π] [Etale π]
      (_hπ : π ≫ M.toBase = N.toBase)
      (_hgeneric : N.C.fromSpecStalk (genericPoint N.C) ≫ π =
        Spec.map (CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
          ((algebraMap K E.val).comp M.ffEquiv.symm.toRingHom))) ≫
            M.C.fromSpecStalk (genericPoint M.C))
      (x : closedPoints M.C)
      (ε : Spec (.of k) ⟶ M.C) (_hε : ε ≫ M.toBase = 𝟙 _)
      (_hεx : ε (IsLocalRing.closedPoint k) = x.1)
      (_hsplit : ∀ y : closedPoints N.C, π y.1 = x.1 →
        ∃ s : Spec (.of k) ⟶ N.C,
          s ≫ π = ε ∧ s (IsLocalRing.closedPoint k) = y.1),
      E.val ≤ (hilbertClassField k K {M.placeOfPoint x}
        (Finset.singleton_nonempty _)).val := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ M N π hfinite hetale hπ hgeneric x ε hε hεx hsplit
  let φ : K →ₐ[k] E.val := IsScalarTower.toAlgHom k K E.val
  have hφ : φ.toRingHom.IsIntegral := fun a =>
    Algebra.IsIntegral.isIntegral (R := K) a
  have halong : algebraAlong φ = (inferInstance : Algebra K E.val) :=
    toAlgebra_algebraMap
  have hpoints (y : closedPoints N.C) :
      ∃ hx : IsClosed ({π y.1} : Set M.C),
        (N.placeOfPoint y).restrict K = M.placeOfPoint ⟨π y.1, hx⟩ ∧
          (N.placeOfPoint y).ramificationIndex K = 1 := by
    obtain ⟨hx, hrestrict, hramification⟩ :=
      M.closedPoint_restrictAlong_ramificationIndex_eq_one_of_finiteEtale
        N φ hφ π hgeneric y
    have hrestriction : (N.placeOfPoint y).restrictAlong φ hφ =
        (N.placeOfPoint y).restrict K := by
      apply Place.ext
      exact congrArg (fun a : Algebra K E.val =>
        let _ : Algebra K E.val := a
        (N.placeOfPoint y).toValuationSubring.comap (algebraMap K E.val)) halong
    have hindex : Place.ramificationIndexAlong φ (N.placeOfPoint y) =
        (N.placeOfPoint y).ramificationIndex K :=
      congrArg (fun a : Algebra K E.val =>
        let _ : Algebra K E.val := a
        (N.placeOfPoint y).ramificationIndex K) halong
    refine ⟨hx, ?_, ?_⟩
    · exact hrestriction.symm.trans hrestrict
    · exact hindex.symm.trans hramification
  have hunramified : ∀ w : Place k E.val, w.ramificationIndex K = 1 := by
    intro w
    let y : closedPoints N.C := N.placeEquiv.symm w
    have hy : N.placeOfPoint y = w := N.placeEquiv.apply_symm_apply w
    obtain ⟨_, _, he⟩ := hpoints y
    rw [hy] at he
    exact he
  apply (le_hilbertClassField_iff k K {M.placeOfPoint x}
    (Finset.singleton_nonempty _) E).mpr
  refine ⟨hunramified, ?_⟩
  intro w hw
  have hwx : w.restrict K = M.placeOfPoint x := Finset.mem_singleton.mp hw
  let y : closedPoints N.C := N.placeEquiv.symm w
  have hy : N.placeOfPoint y = w := N.placeEquiv.apply_symm_apply w
  obtain ⟨hx, hrestrict, _⟩ := hpoints y
  rw [hy] at hrestrict
  have hxy : (⟨π y.1, hx⟩ : closedPoints M.C) = x :=
    M.placeOfPoint_bijective.1 (hrestrict.symm.trans hwx)
  obtain ⟨s, hsπ, hsy⟩ := hsplit y (congrArg Subtype.val hxy)
  have hs : s ≫ N.toBase = 𝟙 _ := by
    rw [← hπ, ← Category.assoc, hsπ, hε]
  have hwrat : w.IsRational := by
    rw [← hy]
    exact N.isRational_placeOfPoint_of_section s hs y hsy.symm
  have hvrat : (w.restrict K).IsRational := by
    rw [hwx]
    exact M.isRational_placeOfPoint_of_section ε hε x hεx.symm
  exact ⟨hunramified w, Place.inertiaDeg_eq_one_of_isRational w hwrat hvrat⟩

end FunctionField
