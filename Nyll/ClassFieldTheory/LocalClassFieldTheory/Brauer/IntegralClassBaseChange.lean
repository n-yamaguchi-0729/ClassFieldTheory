/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.IntegralUnitClass

/-! # Base change of integral classes with a unit coefficient -/

@[expose] public section

noncomputable section

open CategoryTheory ContRepresentation ContinuousCohomology

namespace ClassFieldTheory.Brauer

universe u

variable {K L : Type u} [Field K] [Field L]

local notation "Gₖ" => Gal(SeparableClosure K/K)
local notation "Gₗ" => Gal(SeparableClosure L/L)
local notation "Zₖ" => trivialIntegralTopRep Gₖ
local notation "Zₗ" => trivialIntegralTopRep Gₗ

/-- Restricting an integral class with a base unit coefficient restricts the
integer class and applies the original field map to the unit. -/
theorem restrictOfEmbedding_unitsIntegralClass (f : K →+* L)
    (r : Gₗ →ₜ* Gₖ) (j : SeparableClosure K →+* SeparableClosure L)
    (hbase : ∀ x : K, j (algebraMap K (SeparableClosure K) x) =
      algebraMap L (SeparableClosure L) (f x))
    (hcomm : ∀ (g : Gₗ) (x : SeparableClosure K), j (r g x) = g (j x))
    (a : Kˣ) (x : continuousCohomology 2 Zₖ) :
    restrictOfEmbedding r j hcomm (unitsIntegralClass K a x) =
      unitsIntegralClass L (Units.map f.toMonoidHom a) (integralRestriction r x) := by
  let aL := Units.map f.toMonoidHom a
  let mK : Zₖ ⟶ unitsRep K := unitScalarCoefficientMap K a
  let mL : Zₗ ⟶ unitsRep L := unitScalarCoefficientMap L aL
  let i := integralRestrictionCoefficient r
  let t : TopRep.res r.toMonoidHom (unitsRep K) ⟶ unitsRep L :=
    galoisUnitsMap r j hcomm
  have hunit : Units.map j.toMonoidHom
      (Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a) =
      Units.map (algebraMap L (SeparableClosure L)).toMonoidHom aL := by
    apply Units.ext
    exact hbase (a : K)
  have hcoeff : (TopRep.resFunctor r.toMonoidHom).map mK ≫ t =
      (TopRep.resFunctor (ContinuousMonoidHom.id Gₗ).toMonoidHom).map i ≫ mL := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro v
    let vK : Zₖ := v
    let vL : Zₗ := v
    let n := (show ULift.{u} ℤ from vK).down
    let bK : unitsRep K :=
      Additive.ofMul (Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    let bL : unitsRep L :=
      Additive.ofMul (Units.map (algebraMap L (SeparableClosure L)).toMonoidHom aL)
    change t (mK vK) = mL vL
    have ht : t bK = bL :=
      (galoisUnitsMap_apply r j hcomm bK).trans (congrArg Additive.ofMul hunit)
    have hK : mK vK = n • bK := unitScalarCoefficientMap_apply K a vK
    have hL : mL vL = n • bL := unitScalarCoefficientMap_apply L aL vL
    have hsmul : t (n • bK) = n • t bK := t.hom.toContinuousLinearMap.map_smul n bK
    exact (congrArg (fun b : unitsRep K => t b) hK).trans
      (hsmul.trans ((congrArg (fun b : unitsRep L => n • b) ht).trans hL.symm))
  have hleft : map r (X := Zₖ) ((TopRep.resFunctor r.toMonoidHom).map mK ≫ t) 2 =
      map (ContinuousMonoidHom.id Gₖ) mK 2 ≫ map r t 2 :=
    map_comp (X := Zₖ) (Y := unitsRep K) (Z := unitsRep L)
      (ContinuousMonoidHom.id Gₖ) r mK t 2
  have hright :
      map r (X := Zₖ) ((TopRep.resFunctor (ContinuousMonoidHom.id Gₗ).toMonoidHom).map i ≫ mL) 2 =
        map r i 2 ≫ map (ContinuousMonoidHom.id Gₗ) mL 2 :=
    map_comp (X := Zₖ) (Y := Zₗ) (Z := unitsRep L) r (ContinuousMonoidHom.id Gₗ) i mL 2
  have hmap := congrArg
    (fun p : TopRep.res r.toMonoidHom Zₖ ⟶ unitsRep L => map r p 2) hcoeff
  have h := hleft.symm.trans (hmap.trans hright)
  change map r t 2 (map (ContinuousMonoidHom.id Gₖ) mK 2 x) =
    map (ContinuousMonoidHom.id Gₗ) mL 2 (map r i 2 x)
  exact ConcreteCategory.congr_hom h x

end ClassFieldTheory.Brauer
