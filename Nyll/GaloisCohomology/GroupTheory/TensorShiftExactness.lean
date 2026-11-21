/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Nyll.GaloisCohomology.GroupTheory.CoinducedShift
public import Nyll.GaloisCohomology.GroupTheory.InducedShift
public import Nyll.GaloisCohomology.GroupTheory.RepresentationTensor

/-!
# Tensor exactness of the dimension-shifting sequences

The original coinduced unit and induced counit split on the underlying
modules. Their tensor sequences are therefore short exact with arbitrary
coefficients. Exactness is detected by forgetting the action.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory

namespace Rep

variable {R : Type r} {G : Type u} [CommRing R] [Group G]

/-- Tensoring the original underlying splitting gives a splitting of the
underlying modules of the diagonal tensor sequence. -/
def tensorLeft_forget_splitting {S : ShortComplex (Rep.{v} R G)}
    (A : Rep.{v} R G)
    (hS : (S.map (forget₂ (Rep.{v} R G) (ModuleCat.{v} R))).Splitting) :
    ((S.map (diagonalTensorLeft A)).map (forget₂ (Rep.{v} R G) (ModuleCat.{v} R))).Splitting := by
  let F := forget₂ (Rep.{v} R G) (ModuleCat.{v} R)
  let U := S.map F
  let T := (S.map (diagonalTensorLeft A)).map F
  let r : T.X₂ ⟶ T.X₁ := ModuleCat.ofHom (hS.r.hom.lTensor A)
  let s : T.X₃ ⟶ T.X₂ := ModuleCat.ofHom (hS.s.hom.lTensor A)
  refine ⟨r, s, ?_, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    change (hS.r.hom.lTensor A).comp (U.f.hom.lTensor A) = LinearMap.id
    rw [← LinearMap.lTensor_comp, ← ModuleCat.hom_comp, hS.f_r,
      ModuleCat.hom_id, LinearMap.lTensor_id]
  · apply ModuleCat.hom_ext
    change (U.g.hom.lTensor A).comp (hS.s.hom.lTensor A) = LinearMap.id
    rw [← LinearMap.lTensor_comp, ← ModuleCat.hom_comp, hS.s_g,
      ModuleCat.hom_id, LinearMap.lTensor_id]
  · apply ModuleCat.hom_ext
    change (U.f.hom.lTensor A).comp (hS.r.hom.lTensor A) +
      (hS.s.hom.lTensor A).comp (U.g.hom.lTensor A) = LinearMap.id
    rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_add,
      ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← ModuleCat.hom_add, hS.id,
      ModuleCat.hom_id, LinearMap.lTensor_id]

/-- The diagonal tensor preserves a short complex split on the underlying modules. -/
theorem tensorLeft_shortExact_of_forget_splitting {S : ShortComplex (Rep.{v} R G)}
    (A : Rep.{v} R G) (hS : (S.map (forget₂ (Rep.{v} R G) (ModuleCat.{v} R))).Splitting) :
    (S.map (diagonalTensorLeft A)).ShortExact := by
  let F := forget₂ (Rep.{v} R G) (ModuleCat.{v} R)
  let T := S.map (diagonalTensorLeft A)
  have hT : (T.map F).ShortExact := (tensorLeft_forget_splitting A hS).shortExact
  exact {
    exact := F.reflects_exact_of_faithful T hT.exact
    mono_f := F.mono_of_mono_map hT.mono_f
    epi_g := F.epi_of_epi_map hT.epi_g }

/-- Tensoring on the right also preserves the original underlying splitting. -/
def tensorRight_forget_splitting {S : ShortComplex (Rep.{v} R G)}
    (A : Rep.{v} R G)
    (hS : (S.map (forget₂ (Rep.{v} R G) (ModuleCat.{v} R))).Splitting) :
    ((S.map (diagonalTensorRight A)).map (forget₂ (Rep.{v} R G) (ModuleCat.{v} R))).Splitting := by
  let F := forget₂ (Rep.{v} R G) (ModuleCat.{v} R)
  let U := S.map F
  let T := (S.map (diagonalTensorRight A)).map F
  let r : T.X₂ ⟶ T.X₁ := ModuleCat.ofHom (hS.r.hom.rTensor A)
  let s : T.X₃ ⟶ T.X₂ := ModuleCat.ofHom (hS.s.hom.rTensor A)
  refine ⟨r, s, ?_, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    change (hS.r.hom.rTensor A).comp (U.f.hom.rTensor A) = LinearMap.id
    rw [← LinearMap.rTensor_comp, ← ModuleCat.hom_comp, hS.f_r,
      ModuleCat.hom_id, LinearMap.rTensor_id]
  · apply ModuleCat.hom_ext
    change (U.g.hom.rTensor A).comp (hS.s.hom.rTensor A) = LinearMap.id
    rw [← LinearMap.rTensor_comp, ← ModuleCat.hom_comp, hS.s_g,
      ModuleCat.hom_id, LinearMap.rTensor_id]
  · apply ModuleCat.hom_ext
    change (U.f.hom.rTensor A).comp (hS.r.hom.rTensor A) +
      (hS.s.hom.rTensor A).comp (U.g.hom.rTensor A) = LinearMap.id
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, ← LinearMap.rTensor_add,
      ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← ModuleCat.hom_add, hS.id,
      ModuleCat.hom_id, LinearMap.rTensor_id]

/-- Right tensoring preserves exactness when the underlying modules split. -/
theorem tensorRight_shortExact_of_forget_splitting {S : ShortComplex (Rep.{v} R G)}
    (A : Rep.{v} R G)
    (hS : (S.map (forget₂ (Rep.{v} R G) (ModuleCat.{v} R))).Splitting) :
    (S.map (diagonalTensorRight A)).ShortExact := by
  let F := forget₂ (Rep.{v} R G) (ModuleCat.{v} R)
  let T := S.map (diagonalTensorRight A)
  have hT : (T.map F).ShortExact := (tensorRight_forget_splitting A hS).shortExact
  exact {
    exact := F.reflects_exact_of_faithful T hT.exact
    mono_f := F.mono_of_mono_map hT.mono_f
    epi_g := F.epi_of_epi_map hT.epi_g }

/-- Evaluation at the identity splits the coinduction unit on the underlying modules. -/
def coindShiftSequence_forget_splitting (B : Rep.{u} R G) :
    ((coindShiftSequence B).map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting := by
  let F := forget₂ (Rep.{u} R G) (ModuleCat.{u} R)
  let S := coindShiftSequence B
  let r : (S.map F).X₂ ⟶ (S.map F).X₁ := ModuleCat.ofHom (coindShiftRetraction B)
  have hr : (S.map F).f ≫ r = 𝟙 (S.map F).X₁ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact coindShiftRetraction_unit B b
  have hS : (S.map F).ShortExact := (coindShiftSequence_shortExact B).map_of_exact F
  exact ShortComplex.Splitting.ofExactOfRetraction (S.map F) hS.exact r hr hS.epi_g

/-- The class of the identity gives a section of the induction counit on modules. -/
def indShiftSequence_forget_splitting (B : Rep.{max u r} R G) :
    ((indShiftSequence B).map (forget₂ (Rep.{max u r} R G) (ModuleCat.{max u r} R))).Splitting := by
  let F := forget₂ (Rep.{max u r} R G) (ModuleCat.{max u r} R)
  let S := indShiftSequence B
  let s : (S.map F).X₃ ⟶ (S.map F).X₂ := ModuleCat.ofHom (indShiftSection B)
  have hs : s ≫ (S.map F).g = 𝟙 (S.map F).X₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact indShiftCounit_section B b
  have hS : (S.map F).ShortExact := (indShiftSequence_shortExact B).map_of_exact F
  exact ShortComplex.Splitting.ofExactOfSection (S.map F) hS.exact s hs hS.mono_f

/-- Tensoring the original coinduction sequence on the left is exact. -/
theorem tensorLeft_coindShiftSequence_shortExact (A B : Rep.{u} R G) :
    ((coindShiftSequence B).map (diagonalTensorLeft A)).ShortExact :=
  tensorLeft_shortExact_of_forget_splitting A (coindShiftSequence_forget_splitting B)

/-- Tensoring the original induction sequence on the left is exact. -/
theorem tensorLeft_indShiftSequence_shortExact (A B : Rep.{max u r} R G) :
    ((indShiftSequence B).map (diagonalTensorLeft A)).ShortExact :=
  tensorLeft_shortExact_of_forget_splitting A (indShiftSequence_forget_splitting B)

end Rep
