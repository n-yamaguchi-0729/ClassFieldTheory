/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.SchemeTheory.BaseChange.Points
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Fibre
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Base Change
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section BaseChange

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

/-- The relative group law transported to the base-changed scheme. -/
def baseChange (G : RelativeGroupLaw R f) : RelativeGroupLaw R' (baseChangeStr ι f) where
  mul t' x y := baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase
    ι y))
  one t' := baseChangePointOfBase ι (G.one _)
  inv t' x := baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x))
  mul_assoc t' x y z := by
    simp only [baseChangePointToBase_ofBase, G.mul_assoc]
  one_mul t' x := by
    simp only [baseChangePointToBase_ofBase, G.one_mul, baseChangePointOfBase_toBase]
  mul_one t' x := by
    simp only [baseChangePointToBase_ofBase, G.mul_one, baseChangePointOfBase_toBase]
  inv_mul_cancel t' x := by
    simp only [baseChangePointToBase_ofBase, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe,
        Category.assoc,
        pullback.lift_fst, pullback.lift_fst]
      have h := congrArg Subtype.val
        (G.mul_natural (t ≫ ι) (t' ≫ ι) ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x)
          (baseChangePointToBase ι y))
      rw [schemeHomOverComp_coe] at h
      rw [h, ← baseChangePointToBase_schemeHomOverComp, ← baseChangePointToBase_schemeHomOverComp]
    · rw [schemeHomOverComp_coe, baseChangePointOfBase_coe, baseChangePointOfBase_coe,
        Category.assoc,
        pullback.lift_snd, pullback.lift_snd]
      exact hψ
@[simp]
theorem baseChange_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).mul t' x y =
      baseChangePointOfBase ι (G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y)) :=
  rfl
@[simp]
theorem baseChange_one (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of
  R')) :
    (G.baseChange ι).one t' = baseChangePointOfBase ι (G.one _) :=
  rfl
@[simp]
theorem baseChange_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (G.baseChange ι).inv t' x = baseChangePointOfBase ι (G.inv _ (baseChangePointToBase ι x)) :=
  rfl

theorem baseChangePointToBase_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).mul t' x y) =
      G.mul _ (baseChangePointToBase ι x) (baseChangePointToBase ι y) := by
  rw [baseChange_mul, baseChangePointToBase_ofBase]

theorem baseChangePointToBase_one (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) :
    baseChangePointToBase ι ((G.baseChange ι).one t') = G.one _ := by
  rw [baseChange_one, baseChangePointToBase_ofBase]

theorem baseChangePointToBase_inv (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointToBase ι ((G.baseChange ι).inv t' x) = G.inv _ (baseChangePointToBase ι x) := by
  rw [baseChange_inv, baseChangePointToBase_ofBase]

theorem IsCommutative.baseChange {G : RelativeGroupLaw R f} (hG : G.IsCommutative) :
    (G.baseChange ι).IsCommutative := fun t' x y => by
  rw [baseChange_mul, baseChange_mul, hG.mul_comm]

theorem fibre_eq_baseChange (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u}))
  :
    G.fibre s = G.baseChange (basePointInclusion s) :=
  rfl

end BaseChange

section GenericFibre

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

/-- The base change of the scheme to the fraction field. -/
abbrev genericFibreScheme (f : A ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  baseChangeScheme (specGenericFibreInclusion R K) f

/-- The structure morphism of the generic fibre. -/
abbrev genericFibreStr (f : A ⟶ Spec (CommRingCat.of R)) : genericFibreScheme K f ⟶ Spec
  (CommRingCat.of K) :=
  baseChangeStr (specGenericFibreInclusion R K) f

/-- The relative group law induced on the generic fibre. -/
abbrev genericFibre (G : RelativeGroupLaw R f) : RelativeGroupLaw K (genericFibreStr K f) :=
  G.baseChange (specGenericFibreInclusion R K)

theorem baseChangePointToBase_comp_genericFibreRestrict {B : Scheme.{u}}
    {g : B ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver g f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t' (genericFibreStr K
      g)) :
    baseChangePointToBase (specGenericFibreInclusion R K)
        (NeronModelInfra.schemeHomOverComp x (genericFibreRestrict R K f g φ)) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase (specGenericFibreInclusion R K) x) φ
        :=
  baseChangePointToBase_comp_fibreRestrictAlong (specGenericFibreInclusion R K) φ x

end GenericFibre

end RelativeGroupLaw
end GoodReductionJacobian

end
