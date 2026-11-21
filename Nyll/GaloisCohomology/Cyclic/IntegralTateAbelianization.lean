/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology

/-!
# Integral Tate degree minus two and the original abelianization

The native Tate-to-homology comparison and the standard bar-chain calculation
identify degree minus two, with the original trivial integer coefficients,
with the abelianization of the original group. The coefficient and group lifts
are removed by their actual equivalences. The class of the chain `[g]` maps to
the positive class of `g`; the formula for its negative records the sign
explicitly, without asserting any comparison with an arithmetic Artin map.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace IntegralGroupCohomology.Universe

variable (G : Type u) [Group G]

/-- The trivial integer module at the original coefficient universe. -/
abbrev integralTrivialInteger : Rep.{v} ℤ G := Rep.trivial ℤ G (ULift.{v} ℤ)

/-- The original coefficient one in the trivial integer module. -/
abbrev integralTrivialIntegerOne : integralTrivialInteger.{u, v} G := ULift.up (1 : ℤ)

/-- The original trivial module after the native cohomology lift. -/
abbrev nativeTrivialInt :
    Rep.{max u v} (ULift.{max u v} ℤ) (ULift.{v} G) :=
  (nativeFunctor G).obj (integralTrivialInteger.{u, v} G)

/-- Lifting the trivial action preserves the literal trivial action. -/
instance nativeTrivialInt_isTrivial : (nativeTrivialInt.{u, v} G).IsTrivial where
  out _ := LinearMap.ext fun _ => rfl

/-- Contraction of the original tensor coefficient and removal of the group lift. -/
def trivialIntTensorEquiv :
    Additive (Group.Abelianization (ULift.{v} G)) ⊗[ℤ] nativeTrivialInt.{u, v} G ≃+
      Additive (Group.Abelianization G) :=
  ((TensorProduct.congr
      (LinearEquiv.refl ℤ (Additive (Group.Abelianization (ULift.{v} G))))
      ((ULift.moduleEquiv : ULift.{u} (ULift.{v} ℤ) ≃ₗ[ℤ] ULift.{v} ℤ).trans
        (ULift.moduleEquiv : ULift.{v} ℤ ≃ₗ[ℤ] ℤ))).trans
        (TensorProduct.rid ℤ (Additive (Group.Abelianization (ULift.{v} G))))).toAddEquiv.trans
    (MulEquiv.ulift : ULift.{v} G ≃* G).abelianizationCongr.toAdditive

/-- The standard first-homology calculation uses the original abelianization. -/
def homologyOneAbelianizationEquiv :
    homology (integralTrivialInteger.{u, v} G) 1 ≃+ Additive (Group.Abelianization G) :=
  (groupHomology.H1AddEquivOfIsTrivial (nativeTrivialInt.{u, v} G)).trans
    (trivialIntTensorEquiv G)

/-- The first-homology class of the bar chain with coefficient one at `g`. -/
def homologyOneClass (g : G) : homology (integralTrivialInteger.{u, v} G) 1 :=
  groupHomology.H1π (nativeTrivialInt.{u, v} G)
    ((groupHomology.cycles₁IsoOfIsTrivial (nativeTrivialInt.{u, v} G)).inv
      (Finsupp.single (ULift.up g) (ULift.up (integralTrivialIntegerOne.{u, v} G))))

/-- The bar-chain convention sends `[g]` to the positive abelianization class. -/
theorem homologyOneAbelianizationEquiv_class (g : G) :
    homologyOneAbelianizationEquiv.{u, v} G (homologyOneClass G g) =
      Additive.ofMul (Group.Abelianization.of g) := by
  let M := nativeTrivialInt.{u, v} G
  let a : M := ULift.up (integralTrivialIntegerOne G)
  change trivialIntTensorEquiv G
      (groupHomology.H1AddEquivOfIsTrivial M
        (groupHomology.H1π M
          ((groupHomology.cycles₁IsoOfIsTrivial M).inv
            (Finsupp.single (ULift.up g) a)))) = _
  rw [groupHomology.H1AddEquivOfIsTrivial_single M (ULift.up g) a]
  change (MulEquiv.ulift : ULift.{v} G ≃* G).abelianizationCongr.toAdditive
    ((TensorProduct.rid ℤ (Additive (Group.Abelianization (ULift.{v} G))))
      (Additive.ofMul (Group.Abelianization.of (ULift.up g)) ⊗ₜ[ℤ] (1 : ℤ))) = _
  rw [TensorProduct.rid_tmul, one_smul]
  exact congrArg Additive.ofMul
    (Group.abelianizationCongr_of (MulEquiv.ulift : ULift.{v} G ≃* G) (ULift.up g))

variable [Fintype G]

/-- The actual native Tate-to-homology comparison at degree minus two, with
independent group and coefficient universes. -/
def tateNegTwoIsoHomology (A : Rep.{v} ℤ G) : tate A (-2) ≅ homology A 1 :=
  integerScalars.mapIso
    ((TateCohomology.isoGroupHomology (-2) 1 (by decide)).app
      ((nativeFunctor G).obj A))

/-- Degree minus two on the original trivial integer module computes
the original abelianization in any coefficient universe. -/
def tateNegTwoUnitAbelianizationEquiv :
    tate (integralTrivialInteger.{u, v} G) (-2) ≃+ Additive (Group.Abelianization G) :=
  (tateNegTwoIsoHomology G (integralTrivialInteger.{u, v} G)).toLinearEquiv.toAddEquiv.trans
    (homologyOneAbelianizationEquiv G)

/-- The original bar-chain class of `g` in the coefficient universe. -/
def tateNegTwoUnitClass (g : G) : tate (integralTrivialInteger.{u, v} G) (-2) :=
  (tateNegTwoIsoHomology G (integralTrivialInteger.{u, v} G)).inv (homologyOneClass G g)

/-- The native Tate comparison preserves the positive bar-chain convention. -/
theorem tateNegTwoUnitAbelianizationEquiv_class (g : G) :
    tateNegTwoUnitAbelianizationEquiv.{u, v} G (tateNegTwoUnitClass G g) =
      Additive.ofMul (Group.Abelianization.of g) := by
  let A := integralTrivialInteger.{u, v} G
  let e := tateNegTwoIsoHomology G A
  let z : homology A 1 := homologyOneClass G g
  have he : e.hom (e.inv z) = z := Iso.inv_hom_id_apply e z
  change homologyOneAbelianizationEquiv G (e.hom (e.inv z)) = _
  exact (congrArg (homologyOneAbelianizationEquiv G) he).trans
    (homologyOneAbelianizationEquiv_class G g)

end IntegralGroupCohomology.Universe
