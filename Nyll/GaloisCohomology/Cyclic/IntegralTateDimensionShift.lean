/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCoinduction
public import Nyll.GaloisCohomology.Cyclic.IntegralTateExactness
public import Nyll.GaloisCohomology.GroupTheory.CoinducedShift

/-!
# Actual coinduced dimension shifting for integral Tate cohomology

The explicit coinduction embedding, its cokernel sequence, and the proved
vanishing of its middle term make the original connecting map an equivalence
in every integer degree. Independently sized input groups and coefficients
use the established representation lift, followed by the established
comparison back to their original integral Tate object.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- The actual upward shifting equivalence in a working universe. The middle
term's vanishing is proved from coinduction and is not an input. -/
def coindShiftUpEquiv (A : Rep.{u} ℤ G) (n : ℤ) :
    tate (Rep.coindShiftUp A) n ≃ₗ[ℤ] tate A (n + 1) :=
  tateδEquiv (Rep.coindShiftSequence_shortExact A) n
    (coind_tate_isZero (Rep.res (⊥ : Subgroup G).subtype A) n)
    (coind_tate_isZero (Rep.res (⊥ : Subgroup G).subtype A) (n + 1))

/-- The forward shift is precisely the original connecting homomorphism. -/
theorem coindShiftUpEquiv_apply (A : Rep.{u} ℤ G) (n : ℤ)
    (x : tate (Rep.coindShiftUp A) n) :
    coindShiftUpEquiv A n x = tateδ (Rep.coindShiftSequence_shortExact A) n x := rfl

/-- Dimension shifting with independent input universes. The original
representation lift supplies a working universe, and its existing Tate
comparison recovers the original target object. -/
def coindShiftUpIso (A : Rep.{v} ℤ G) (n : ℤ) :
    tate (Rep.coindShiftUp ((Rep.universeLiftFunctor ℤ G).obj A)) n ≅
      tate A (n + 1) :=
  (coindShiftUpEquiv ((Rep.universeLiftFunctor ℤ G).obj A) n).toModuleIso ≪≫
    tateIsoCommon ((Rep.universeLiftFunctor ℤ G).obj A) (n + 1)

/-- The independently lifted shift still uses the specified connecting map
and the existing native-complex comparison, with no chosen isomorphism. -/
theorem coindShiftUpIso_hom_apply (A : Rep.{v} ℤ G) (n : ℤ)
    (x : tate (Rep.coindShiftUp ((Rep.universeLiftFunctor ℤ G).obj A)) n) :
    (coindShiftUpIso A n).hom x =
      (tateIsoCommon ((Rep.universeLiftFunctor ℤ G).obj A) (n + 1)).hom
        (tateδ (Rep.coindShiftSequence_shortExact
          ((Rep.universeLiftFunctor ℤ G).obj A)) n x) := rfl

end IntegralGroupCohomology.Universe
