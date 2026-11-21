/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateAbelianization
public import Nyll.GaloisCohomology.Cyclic.IntegralTateExactness
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles
public import Nyll.GaloisCohomology.Cyclic.TateNegativeCyclicBoundaries

/-! # Integral representatives for the two negative Tate boundaries -/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory MonoidalCategory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- The integral class of the single bar chain with the given original coefficient. -/
def tateNegTwoBarClass (A : Rep.{v} ℤ G) (g : G) (a : A) (ha : A.ρ g⁻¹ a = a) : tate A (-2) :=
  TateCohomology.negTwoSingleClass ((nativeFunctor G).obj A) (ULift.up g) (ULift.up a)
    (ULift.ext ha)

/-- The actual integral Tate class of a norm-zero vector of the original coefficient. -/
def tateNegOneNormClass (A : Rep.{v} ℤ G) (a : A) (ha : A.ρ.norm a = 0) : tate A (-1) :=
  TateCohomology.negOneNormClass ((nativeFunctor G).obj A) (ULift.up a)
    (ULift.down_injective ((nativeFunctor_norm_down A a).trans ha))

/-- The positive abelianization convention uses this same original bar representative. -/
theorem tateNegTwoUnitClass_eq_bar (g : G) :
    tateNegTwoUnitClass.{u, v} G g =
      tateNegTwoBarClass (integralTrivialInteger G) g (integralTrivialIntegerOne G) rfl := by
  let A := integralTrivialInteger.{u, v} G
  let M := nativeTrivialInt.{u, v} G
  let a : M := ULift.up (integralTrivialIntegerOne G)
  let E := tateNegTwoIsoHomology G A
  apply E.toLinearEquiv.injective
  let x : homology A 1 := homologyOneClass G g
  change E.hom (E.inv x) = E.hom (tateNegTwoBarClass A g (integralTrivialIntegerOne G) rfl)
  exact (Iso.inv_hom_id_apply E x).trans
    (TateCohomology.isoGroupHomology_hom_negTwoSingleClass M (ULift.up g) a rfl).symm

/-- Combining the original auxiliary lift with the common-universe comparison
preserves the single bar representative on the original group and carrier. -/
theorem tateIsoCommon_inv_barClass (A : Rep.{v} ℤ G) (g : G) (a : A) (ha : A.ρ g⁻¹ a = a) :
    let F := Rep.universeLiftFunctor ℤ G
    (tateIsoCommon (F.obj A) (-2)).inv (tateNegTwoBarClass A g a ha) =
      tateNegTwoBarClass (F.obj A) (ULift.up g) (ULift.up a) (ULift.ext ha) := by
  let F := Rep.universeLiftFunctor ℤ G
  let U := F.obj A
  let E := tateIsoCommon U (-2)
  apply E.toLinearEquiv.injective
  let x : IntegralGroupCohomology.tate U (-2) := tateNegTwoBarClass A g a ha
  let y := tateNegTwoBarClass U (ULift.up g) (ULift.up a) (ULift.ext ha)
  change E.hom (E.inv x) = E.hom y
  exact (Iso.inv_hom_id_apply E x).trans (TateCohomology.groupEquivIso_hom_negTwoSingleClass
    (MulEquiv.ulift : ULift.{max u v} (ULift.{v} G) ≃* ULift.{v} G) (nativeCarrierEquiv U)
    (nativeCarrierEquiv_comm U) (ULift.up (ULift.up g)) (ULift.up (ULift.up a))
    (ULift.ext (ULift.ext ha)) (ULift.ext ha)).symm

/-- A fixed vector in the single auxiliary carrier lift. -/
def universeLiftFixedVector (A : Rep.{v} ℤ G) (a : A.ρ.invariants) :
    ((Rep.universeLiftFunctor ℤ G).obj A).ρ.invariants :=
  ⟨ULift.up a.val, fun g => ULift.ext (a.property g.down)⟩

/-- Removing the same auxiliary lift sends a fixed Tate class to the
class of the original fixed vector. -/
theorem tateIsoCommon_fixedClass_lift (A : Rep.{v} ℤ G) (a : A.ρ.invariants) :
    let F := Rep.universeLiftFunctor ℤ G
    (tateIsoCommon (F.obj A) 0).hom (fixedClass (F.obj A) (universeLiftFixedVector A a)) =
      fixedClass A a := by
  let F := Rep.universeLiftFunctor ℤ G
  let U := F.obj A
  exact TateCohomology.groupEquivIso_hom_fixedClass
    (MulEquiv.ulift : ULift.{max u v} (ULift.{v} G) ≃* ULift.{v} G) (nativeCarrierEquiv U)
    (nativeCarrierEquiv_comm U) (nativeFixedEquiv U (universeLiftFixedVector A a))
    (nativeFixedEquiv A a) rfl

/-- A coefficient map keeps the same original bar entry and applies its coefficient map. -/
theorem tateMap_negTwoBarClass {A B : Rep.{v} ℤ G} (f : A ⟶ B) (g : G) (a : A)
    (ha : A.ρ g⁻¹ a = a) :
    (tateFunctor G (-2)).map f (tateNegTwoBarClass A g a ha) =
      tateNegTwoBarClass B g (f a) (by rw [← Rep.hom_comm_apply, ha]) :=
  TateCohomology.map_negTwoSingleClass ((nativeFunctor G).map f) (ULift.up g) (ULift.up a)
    (ULift.ext ha)

/-- The original integral boundary on a lifted bar class applies `g⁻¹ − 1`. -/
theorem tateδ_negTwoBarClass {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact) (g : G)
    (a : S.X₃) (ha : S.X₃.ρ g⁻¹ a = a) (y : S.X₂) (hy : S.g y = a)
    (x : S.X₁) (hx : S.f x = S.X₂.ρ g⁻¹ y - y) (hn : S.X₁.ρ.norm x = 0) :
    tateδ hS (-2) (tateNegTwoBarClass S.X₃ g a ha) = tateNegOneNormClass S.X₁ x hn :=
  TateCohomology.δ_negTwoSingleClass (native_shortExact hS) (ULift.up g)
    (ULift.up a) (ULift.ext ha) (ULift.up y) (ULift.ext hy) (ULift.up x) (ULift.ext hx)
    (ULift.down_injective ((nativeFunctor_norm_down S.X₁ x).trans hn))

/-- The original integral boundary from degree minus one takes the norm of the chosen lift. -/
theorem tateδ_negOneNormClass {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact)
    (a : S.X₃) (ha : S.X₃.ρ.norm a = 0) (y : S.X₂) (hy : S.g y = a)
    (x : S.X₁.ρ.invariants) (hx : S.f x.val = S.X₂.ρ.norm y) :
    tateδ hS (-1) (tateNegOneNormClass S.X₃ a ha) = fixedClass S.X₁ x :=
  TateCohomology.δ_negOneNormClass (native_shortExact hS) (ULift.up a)
    (ULift.down_injective ((nativeFunctor_norm_down S.X₃ a).trans ha))
    (ULift.up y) (ULift.ext hy) (nativeFixedEquiv S.X₁ x)
    (ULift.down_injective (hx.trans (nativeFunctor_norm_down S.X₂ y).symm))

end IntegralGroupCohomology.Universe
