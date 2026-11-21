/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCoinduction
public import Nyll.GaloisCohomology.Cyclic.IntegralTateExactness
public import Nyll.GaloisCohomology.GroupTheory.InducedShift
public import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Actual induced dimension shifting for integral Tate cohomology

Induction from a trivial subgroup is Tate acyclic by the actual finite-index
induction-coinduction comparison. Thus the connecting map of the specified
kernel sequence gives the complementary dimension-shifting isomorphism.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- Induction from a subsingleton subgroup has zero original integral Tate
cohomology in every integer degree, with independent coefficient universes. -/
theorem ind_tate_isZero {S : Subgroup G} [Subsingleton S] (A : Rep.{v} ℤ S) (n : ℤ) :
    Limits.IsZero (tate (Rep.ind S.subtype A) n) := by
  classical
  exact Limits.IsZero.of_iso (coind_tate_isZero A n)
    ((tateFunctor G n).mapIso (Rep.indCoindIso.{v} A))

/-- The connecting map for the actual kernel of the induction counit is an
equivalence; the induced middle term's vanishing is supplied by the theorem above. -/
def indShiftDownEquiv (A : Rep.{u} ℤ G) (n : ℤ) :
    tate A n ≃ₗ[ℤ] tate (Rep.indShiftDown A) (n + 1) :=
  tateδEquiv (Rep.indShiftSequence_shortExact A) n
    (ind_tate_isZero (Rep.res (⊥ : Subgroup G).subtype A) n)
    (ind_tate_isZero (Rep.res (⊥ : Subgroup G).subtype A) (n + 1))

/-- The forward map is exactly the original connecting homomorphism. -/
theorem indShiftDownEquiv_apply (A : Rep.{u} ℤ G) (n : ℤ) (x : tate A n) :
    indShiftDownEquiv A n x = tateδ (Rep.indShiftSequence_shortExact A) n x := rfl

/-- The induced shift also applies to independently sized original coefficients,
through the established lift and its existing Tate comparison. -/
def indShiftDownIso (A : Rep.{v} ℤ G) (n : ℤ) :
    tate A n ≅
      tate (Rep.indShiftDown ((Rep.universeLiftFunctor ℤ G).obj A)) (n + 1) :=
  (tateIsoCommon ((Rep.universeLiftFunctor ℤ G).obj A) n).symm ≪≫
    (indShiftDownEquiv ((Rep.universeLiftFunctor ℤ G).obj A) n).toModuleIso

/-- The independently sized version still evaluates by the original comparison
followed by the specified kernel sequence's connecting map. -/
theorem indShiftDownIso_hom_apply (A : Rep.{v} ℤ G) (n : ℤ) (x : tate A n) :
    (indShiftDownIso A n).hom x =
      tateδ (Rep.indShiftSequence_shortExact ((Rep.universeLiftFunctor ℤ G).obj A)) n
        ((tateIsoCommon ((Rep.universeLiftFunctor ℤ G).obj A) n).inv x) := rfl

end IntegralGroupCohomology.Universe
