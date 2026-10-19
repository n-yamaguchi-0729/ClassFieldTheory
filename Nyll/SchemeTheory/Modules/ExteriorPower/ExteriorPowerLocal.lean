/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.ExteriorPower.Det
import Nyll.SchemeTheory.Sheaves.RestrictOpen
import Nyll.SchemeTheory.Modules.Frames.LocallyFreeBasis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Nyll.SchemeTheory.Modules.LocalMorphisms

/-!
# Pullback to an open commutes with exterior powers

Restriction commutes with presheaf exterior powers, and sheafification transports
this comparison to pullback of module sheaves.
-/

section nonempty_pullback_exteriorPower_iso_exteriorPower_pullback

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback

universe u

open CategoryTheory

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Restriction along the open indexing functor commutes with presheaf exterior powers. -/
noncomputable def restrictPresheaf₀CompPresheafExteriorPowerIso (n : ℕ) (U : X.Opens) :
    presheafExteriorPower X n ⋙ restrictPresheaf₀ U ≅
      restrictPresheaf₀ U ⋙ presheafExteriorPower (U : Scheme.{u}) n :=
  NatIso.ofComponents
    (fun P => PresheafOfModules.isoMk (fun V => Iso.refl _) (fun V W f => by
      simp only [Iso.refl_hom]
      rfl))
    (fun φ => by
      ext V : 1
      simp only [Functor.comp_map, PresheafOfModules.comp_app]
      rfl)

/-- The restriction comparison transported to the ring-sheaf restriction functor. -/
noncomputable def restrictPresheafCompPresheafExteriorPowerIso (n : ℕ) (U : X.Opens) :
    presheafExteriorPower X n ⋙ restrictPresheaf U ≅
      restrictPresheaf U ⋙ presheafExteriorPower (U : Scheme.{u}) n :=
  Functor.isoWhiskerLeft _ (restrictPresheafIsoRestrictPresheaf₀ U) ≪≫
    restrictPresheaf₀CompPresheafExteriorPowerIso n U ≪≫
    Functor.isoWhiskerRight (restrictPresheafIsoRestrictPresheaf₀ U).symm _

section steps
variable (n : ℕ) (U : X.Opens) (M : X.Modules)

/-- The comparison between pullback of the sheafified power and sheafified restriction. -/
noncomputable def pullbackExteriorPowerIso_step1 :
    (Modules.pullback U.ι).obj ((exteriorPower X n).obj M) ≅
      (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((restrictPresheaf U).obj ((presheafExteriorPower X n).obj M.val)) :=
  (sheafificationCompPullbackIso U).app ((presheafExteriorPower X n).obj M.val)

/-- The sheafified comparison between exterior power before and after restriction. -/
noncomputable def pullbackExteriorPowerIso_step2 :
    (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((restrictPresheaf U).obj ((presheafExteriorPower X n).obj M.val)) ≅
      (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((presheafExteriorPower (U : Scheme.{u}) n).obj ((restrictPresheaf U).obj M.val)) :=
  (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).mapIso
    ((restrictPresheafCompPresheafExteriorPowerIso n U).app M.val)

/-- The sheafified restricted power identified with the exterior power of the restriction. -/
noncomputable def pullbackExteriorPowerIso_step25 :
    (PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj)).obj
        ((presheafExteriorPower (U : Scheme.{u}) n).obj ((restrictPresheaf U).obj M.val)) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((restrictOpen U).obj M) :=
  Iso.refl _

/-- The exterior-power comparison induced by the restriction-pullback isomorphism. -/
noncomputable def pullbackExteriorPowerIso_step3 :
    (exteriorPower (U : Scheme.{u}) n).obj ((restrictOpen U).obj M) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((Modules.pullback U.ι).obj M) :=
  (exteriorPower (U : Scheme.{u}) n).mapIso ((restrictOpenIsoPullback U).app M)

end steps

/-- The canonical isomorphism commuting pullback to the open with exterior power. -/
noncomputable def pullbackExteriorPowerIso (n : ℕ) (U : X.Opens) (M : X.Modules) :
    (Modules.pullback U.ι).obj ((exteriorPower X n).obj M) ≅
      (exteriorPower (U : Scheme.{u}) n).obj ((Modules.pullback U.ι).obj M) :=
  pullbackExteriorPowerIso_step1 n U M ≪≫ pullbackExteriorPowerIso_step2 n U M ≪≫
    pullbackExteriorPowerIso_step25 n U M ≪≫ pullbackExteriorPowerIso_step3 n U M

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
  {X : Scheme.{u}} (n : ℕ) (U : X.Opens) (M : X.Modules) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.exteriorPower X n).obj M) ≅
      (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).obj ((Scheme.Modules.pullback U.ι).obj M))
          :=
  ⟨Scheme.Modules.pullbackExteriorPowerIso n U M⟩
end Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply
    PresheafOfModules.pushforwardNatTrans_app_app_apply
    PresheafOfModules.pushforwardCongr_hom_app_app_apply

end nonempty_pullback_exteriorPower_iso_exteriorPower_pullback

section nonempty_exteriorPower_free_iso_unit

/-!
# Top exterior powers of finite free module sheaves

The standard basis determines a top exterior form and an isomorphism from the
top exterior power of a free module sheaf to the tensor unit. The tuple presheaf and
its free-sheaf comparison use the same construction as the local-basis theorem.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_exteriorPower_free_iso_unit

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace exteriorPower
open _root_.exteriorPower
open _root_.exteriorPower

variable (A : Type u) [CommRing A] (n : ℕ)

noncomputable scoped instance uniquePowersetCardFin : Unique (Set.powersetCard (Fin n) n) where
  default := Set.powersetCard.ofCard (n := n) (s := (Finset.univ : Finset (Fin n)))
    (by rw [Finset.card_univ, Fintype.card_fin])
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by
    rw [Fintype.card_fin]; exact Set.powersetCard.card_eq s))

/-- The top exterior form determined by the standard basis. -/
noncomputable def topForm : ⋀[A]^n (Fin n → A) :=
  ιMulti_family A n (Pi.basisFun A (Fin n)) default

/-- The exterior power basis of the standard basis in top degree. -/
noncomputable abbrev topBasis : Module.Basis (Set.powersetCard (Fin n) n) A (⋀[A]^n (Fin n → A)) :=
  (Pi.basisFun A (Fin n)).exteriorPower n

lemma topBasis_apply (s : Set.powersetCard (Fin n) n) : topBasis A n s = topForm A n := by
  rw [Subsingleton.elim s default, basis_apply]
  rfl

/-- Identify the top exterior power with the coefficient ring using its standard form. -/
noncomputable def topEquiv : ⋀[A]^n (Fin n → A) ≃ₗ[A] A :=
  (topBasis A n).repr ≪≫ₗ Finsupp.uniqueLinearEquiv A A default

@[scoped simp] lemma topEquiv_topForm : topEquiv A n (topForm A n) = 1 := by
  have h := (topBasis A n).repr_self default
  rw [topBasis_apply] at h
  rw [topEquiv, LinearEquiv.trans_apply, h, Finsupp.uniqueLinearEquiv_apply,
    Finsupp.single_eq_same]

lemma topEquiv_symm_apply (a : A) : (topEquiv A n).symm a = a • topForm A n := by
  apply (topEquiv A n).injective
  rw [LinearEquiv.apply_symm_apply, map_smul (topEquiv A n) a (topForm A n), topEquiv_topForm,
    smul_eq_mul, mul_one]

lemma eq_topEquiv_smul_topForm (x : ⋀[A]^n (Fin n → A)) : x = topEquiv A n x • topForm A n := by
  conv_lhs => rw [← (topEquiv A n).symm_apply_apply x]
  rw [topEquiv_symm_apply]

lemma exists_eq_smul_topForm (x : ⋀[A]^n (Fin n → A)) : ∃ a : A, x = a • topForm A n :=
  ⟨_, eq_topEquiv_smul_topForm A n x⟩

end exteriorPower

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

variable {C : Type*} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ)

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open scoped Scheme_Modules_nonempty_exteriorPower_free_iso_unit.exteriorPower in
lemma mapₗ_topForm {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ExteriorPower.mapₗ n (piPow R n) f (exteriorPower.topForm (R.obj X) n) =
      exteriorPower.topForm (R.obj Y) n := by
  have hmap := ExteriorPower.mapₗ_ιMulti n (piPow R n) f
    (fun i => (show (piPow R n).obj X from
      Pi.basisFun (R.obj X) (Fin n) ((Set.powersetCard.ofFinEmbEquiv.symm (default :
          Set.powersetCard (Fin n) n)) i)))
  exact hmap.trans (congrArg
    (fun v : Fin n → (piPow R n).obj Y =>
      exteriorPower.ιMulti (R.obj Y) n (M := (piPow R n).obj Y) v)
    (funext fun i => piPow_map_basisFun R n f _))

lemma topEquiv_mapₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : ⋀[R.obj X]^n (Fin n → R.obj X)) :
    exteriorPower.topEquiv (R.obj Y) n (ExteriorPower.mapₗ n (piPow R n) f x) =
      R.map f (exteriorPower.topEquiv (R.obj X) n x) := by
  obtain ⟨a, rfl⟩ := exteriorPower.exists_eq_smul_topForm (R.obj X) n x
  have hx : exteriorPower.topEquiv (R.obj X) n (a • exteriorPower.topForm (R.obj X) n) = a :=
    (congrArg (exteriorPower.topEquiv (R.obj X) n)
      (exteriorPower.topEquiv_symm_apply (R.obj X) n a).symm).trans
      ((exteriorPower.topEquiv (R.obj X) n).apply_symm_apply a)
  have hy : exteriorPower.topEquiv (R.obj Y) n
      (R.map f a • exteriorPower.topForm (R.obj Y) n) = R.map f a :=
    (congrArg (exteriorPower.topEquiv (R.obj Y) n)
      (exteriorPower.topEquiv_symm_apply (R.obj Y) n (R.map f a)).symm).trans
      ((exteriorPower.topEquiv (R.obj Y) n).apply_symm_apply (R.map f a))
  exact (congrArg (exteriorPower.topEquiv (R.obj Y) n)
    ((ExteriorPower.mapₗ_smul n (piPow R n) f a (exteriorPower.topForm (R.obj X) n)).trans
      (congrArg (fun z : ⋀[R.obj Y]^n (Fin n → R.obj Y) => R.map f a • z)
        (mapₗ_topForm R n f)))).trans (hy.trans (congrArg (fun a : R.obj X => R.map f a) hx).symm)

lemma unit_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : R.obj X) :
    ((unit (R ⋙ forget₂ CommRingCat RingCat)).map f
      (show (unit (R ⋙ forget₂ CommRingCat RingCat)).obj X from a) : R.obj Y) = R.map f a := rfl

/-- The presheaf map from the top exterior power to its coefficient ring. -/
noncomputable def piPowTopHomAb :
    ExteriorPower.presheafAb n (piPow R n) ⟶ (unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf where
  app X := AddCommGrpCat.ofHom (X := ⋀[R.obj X]^n (Fin n → R.obj X)) (Y := R.obj X)
    (exteriorPower.topEquiv (R.obj X) n).toLinearMap.toAddMonoidHom
  naturality {X Y} f := by
    ext x
    exact topEquiv_mapₗ R n f x

/-- The presheaf map sending a coefficient to a multiple of the standard top form. -/
noncomputable def piPowTopInvAb :
    (unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf ⟶ ExteriorPower.presheafAb n (piPow R n) where
  app X := AddCommGrpCat.ofHom (X := R.obj X) (Y := ⋀[R.obj X]^n (Fin n → R.obj X))
    (LinearMap.toSpanSingleton (R.obj X) (⋀[R.obj X]^n (Fin n → R.obj X))
      (exteriorPower.topForm (R.obj X) n)).toAddMonoidHom
  naturality {X Y} f :=
    AddCommGrpCat.ext fun (a : R.obj X) =>
      ((ExteriorPower.mapₗ_smul n (piPow R n) f a
        (exteriorPower.topForm (R.obj X) n)).trans
          (congrArg (fun z : ⋀[R.obj Y]^n (Fin n → R.obj Y) => R.map f a • z)
            (mapₗ_topForm R n f))).symm

/-- The top exterior power of the tuple presheaf is the unit module presheaf. -/
noncomputable def exteriorPowerPiPowIso :
    exteriorPower n (piPow R n) ≅ unit (R ⋙ forget₂ CommRingCat RingCat) where
  hom := homMk (piPowTopHomAb R n) (fun X r m =>
    map_smul (exteriorPower.topEquiv (R.obj X) n) (show R.obj X from r)
      (show ⋀[R.obj X]^n (Fin n → R.obj X) from m))
  inv := homMk (M₁ := unit _) (piPowTopInvAb R n) (fun X r a =>
    mul_smul (show R.obj X from r) (show R.obj X from a) (exteriorPower.topForm (R.obj X) n))
  hom_inv_id := by
    ext X : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (exteriorPower.eq_topEquiv_smul_topForm (R.obj X) n x).symm
  inv_hom_id := by
    ext X : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (a : R.obj X) => ?_)
    change exteriorPower.topEquiv (R.obj X) n (a • exteriorPower.topForm (R.obj X) n) = a
    rw [← exteriorPower.topEquiv_symm_apply, LinearEquiv.apply_symm_apply]

end PresheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open TopologicalSpace

variable (X : Scheme.{u}) (n : ℕ)

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_exists_basis.AlgebraicGeometry.Scheme.Modules

/-- Identify the sheafification of the unit presheaf with the unit sheaf. -/
noncomputable def sheafificationUnitIso :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (PresheafOfModules.unit _) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).counit).app
    (SheafOfModules.unit X.ringCatSheaf)

/-- The top exterior power of the finite free module sheaf is the unit sheaf. -/
noncomputable def exteriorPowerFreeIso :
    (exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (exteriorPower X n).mapIso (freeIsoPiPow X n) ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (PresheafOfModules.exteriorPowerPiPowIso X.sheaf.obj n) ≪≫
    sheafificationUnitIso X

theorem nonempty_exteriorPowerFreeIso :
    Nonempty ((exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf) :=
  ⟨exteriorPowerFreeIso X n⟩

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit (X :
  Scheme.{u}) (n : ℕ) :
    Nonempty ((Scheme.Modules.exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf) :=
  AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPowerFreeIso X n
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_exteriorPower_free_iso_unit
end ProofImplementation

end nonempty_exteriorPower_free_iso_unit

section isZero_exteriorPower_of_isLocallyFreeOfRank

/-!
# Vanishing of exterior powers above the rank

Exterior powers of a locally free module sheaf vanish in degrees greater than its rank.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply
    PresheafOfModules.pushforwardNatTrans_app_app_apply
    PresheafOfModules.pushforwardCongr_hom_app_app_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace exteriorPower
open _root_.exteriorPower
open _root_.exteriorPower

lemma isEmpty_powersetCard_fin_of_lt {n m : ℕ} (h : n < m) : IsEmpty (Set.powersetCard (Fin n) m) :=
  ⟨fun s => by
    have h1 := Set.powersetCard.card_eq s
    have h2 : (s : Finset (Fin n)).card ≤ n := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (s : Finset (Fin n))
    omega⟩

lemma subsingleton_pi_of_lt (A : Type u) [CommRing A] {n m : ℕ} (h : n < m) :
    Subsingleton (⋀[A]^m (Fin n → A)) := by
  have := isEmpty_powersetCard_fin_of_lt h
  exact ((Pi.basisFun A (Fin n)).exteriorPower m).repr.toEquiv.subsingleton

end exteriorPower

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

variable {C : Type*} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{u})

lemma isZero_of_subsingleton {S : Cᵒᵖ ⥤ RingCat.{u}} (P : PresheafOfModules.{u} S)
    (h : ∀ X : Cᵒᵖ, Subsingleton (P.obj X)) : IsZero P := by
  rw [IsZero.iff_id_eq_zero]
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (h X).elim _ _

lemma isZero_exteriorPower_piPow {n m : ℕ} (h : n < m) :
    IsZero ((exteriorPowerFunctor R m).obj ((open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
        Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules.piPow R n))) :=
  isZero_of_subsingleton _ (fun X => exteriorPower.subsingleton_pi_of_lt (R.obj X) h)

end PresheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open TopologicalSpace

variable (X : Scheme.{u})

lemma isZero_exteriorPower_free_of_lt {n m : ℕ} (h : n < m) :
    IsZero ((exteriorPower X m).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n)))) := by
  refine IsZero.of_iso ?_ ((exteriorPower X m).mapIso
    (open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
      open Scheme_Modules_IsLocallyFreeOfRank_exists_basis.AlgebraicGeometry.Scheme.Modules in
        freeIsoPiPow X n))
  change IsZero ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((PresheafOfModules.exteriorPowerFunctor X.sheaf.obj m).obj ((open
      _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
        Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules.piPow X.sheaf.obj
          n))))
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_isZero
    (PresheafOfModules.isZero_exteriorPower_piPow X.sheaf.obj h)

variable {X}

theorem isZero_exteriorPower_of_isLocallyFreeOfRank {n m : ℕ} {M : X.Modules}
    (hM : IsLocallyFreeOfRank n M) (h : n < m) : IsZero ((exteriorPower X m).obj M) := by
  refine isZero_of_forall_exists_isZero_pullback_obj _ (fun x => ?_)
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨e₁⟩ := nonempty_pullback_exteriorPower_iso_exteriorPower_pullback m U M
  exact ⟨U, hxU, (isZero_exteriorPower_free_of_lt (U : Scheme.{u}) h).of_iso
    (e₁ ≪≫ (exteriorPower (U : Scheme.{u}) m).mapIso e)⟩

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry in
open Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank.AlgebraicGeometry.Scheme in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isZero_exteriorPower_of_isLocallyFreeOfRank
    {X : Scheme.{u}} {n m : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) (h : n < m) :
    Limits.IsZero ((Scheme.Modules.exteriorPower X m).obj M) :=
  Modules.isZero_exteriorPower_of_isLocallyFreeOfRank hM h
end Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end isZero_exteriorPower_of_isLocallyFreeOfRank
