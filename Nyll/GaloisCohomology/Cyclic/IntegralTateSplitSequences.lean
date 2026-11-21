/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex), The Tau Ceti contributors

The comparison with split sequences follows Tau Ceti's
`RepresentationTheory/Homological/TateCohomology/Cup/Delta.lean`.
-/

module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced
public import Nyll.GaloisCohomology.GroupTheory.CoinducedShift
public import Nyll.GaloisCohomology.GroupTheory.InducedShift

/-!
# Comparison maps for split coefficient sequences

An underlying linear splitting gives maps to and from the actual
coinduction and induction shift sequences, preserving the required end.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G]

/-- Any linear map is equivariant after restriction to the trivial subgroup. -/
def restrictBotLinearHom {A B : Rep.{u} ℤ G} (f : A →ₗ[ℤ] B) :
    Rep.res (⊥ : Subgroup G).subtype A ⟶ Rep.res (⊥ : Subgroup G).subtype B :=
  Rep.ofHom ⟨f, fun g => by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    rw [map_one, map_one]
    rfl⟩

/-- The underlying retraction supplies a map to the coinduced shift sequence. -/
def compareToCoindShift {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting) :
    S ⟶ Rep.coindShiftSequence S.X₁ := by
  let F := forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ)
  let D := Rep.coindShiftSequence S.X₁
  let r := restrictBotLinearHom (A := S.X₂) (B := S.X₁) split.r.hom
  let m : S.X₂ ⟶ D.X₂ := Rep.resCoindToHom (⊥ : Subgroup G).subtype S.X₂
    (Rep.res (⊥ : Subgroup G).subtype S.X₁) r
  have hm : S.f ≫ m = D.f := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro a
    apply Subtype.ext
    funext g
    change r.hom (S.X₂.ρ g (S.f a)) = S.X₁.ρ g a
    rw [← Rep.hom_comm_apply]
    exact congrArg (fun f : (S.map F).X₁ ⟶ (S.map F).X₁ => f (S.X₁.ρ g a)) split.f_r
  have hzero : S.f ≫ m ≫ D.g = 0 := by
    exact (Category.assoc S.f m D.g).symm.trans
      ((congrArg (fun f : S.X₁ ⟶ D.X₂ => f ≫ D.g) hm).trans D.zero)
  let : Epi S.g := hS.epi_g
  exact {
    τ₁ := 𝟙 S.X₁
    τ₂ := m
    τ₃ := hS.exact.desc (m ≫ D.g) hzero
    comm₁₂ := (Category.id_comp D.f).trans hm.symm
    comm₂₃ := (hS.exact.g_desc _ _).symm }

/-- The underlying section supplies a map from the induced shift sequence. -/
def compareFromIndShift {S : ShortComplex (Rep.{u} ℤ G)} (hS : S.ShortExact)
    (split : (S.map (forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ))).Splitting) :
    Rep.indShiftSequence S.X₃ ⟶ S := by
  let F := forget₂ (Rep.{u} ℤ G) (ModuleCat.{u} ℤ)
  let D := Rep.indShiftSequence S.X₃
  let T := Rep.res (⊥ : Subgroup G).subtype S.X₃
  let s := restrictBotLinearHom (A := S.X₃) (B := S.X₂) split.s.hom
  let e := Rep.indResHomEquiv.{u} (⊥ : Subgroup G).subtype T S.X₂
  let m : D.X₂ ⟶ S.X₂ := e.symm s
  have hm : m ≫ S.g = D.g := by
    apply (Rep.indResHomEquiv.{u} (⊥ : Subgroup G).subtype T S.X₃).injective
    apply Rep.hom_ext
    apply DFunLike.ext
    intro a
    change S.g.hom (m.hom (Rep.indShiftSection S.X₃ a)) =
      (Rep.indShiftCounit S.X₃).hom (Rep.indShiftSection S.X₃ a)
    rw [Rep.indShiftCounit_section]
    have hval : m.hom (Rep.indShiftSection S.X₃ a) = s.hom a :=
      congrArg (fun f : T ⟶ Rep.res (⊥ : Subgroup G).subtype S.X₂ => f.hom a)
        (e.apply_symm_apply s)
    rw [hval]
    exact congrArg (fun f : (S.map F).X₃ ⟶ (S.map F).X₃ => f a) split.s_g
  have hzero : (D.f ≫ m) ≫ S.g = 0 := by
    exact (Category.assoc D.f m S.g).trans
      ((congrArg (fun f : D.X₂ ⟶ S.X₃ => D.f ≫ f) hm).trans D.zero)
  let : Mono S.f := hS.mono_f
  exact {
    τ₁ := hS.exact.lift (D.f ≫ m) hzero
    τ₂ := m
    τ₃ := 𝟙 S.X₃
    comm₁₂ := hS.exact.lift_f _ _
    comm₂₃ := hm.trans (Category.comp_id D.g).symm }

end IntegralGroupCohomology.Universe
