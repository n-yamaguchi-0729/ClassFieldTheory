/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseShapiro
public import Nyll.GaloisCohomology.Cyclic.TateCoinducedVanishing

/-!
# Coinduced acyclicity in the existing integral Tate backend

The original equivariant functions are transported by the established
`nativeCoindIso`. Its lifted subgroup is still subsingleton, so the explicit
native coinduced vanishing theorem applies in every integer degree. The
conclusion uses the original integral Tate object, without an extra carrier
or a vanishing hypothesis.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]
  {S : Subgroup G} [Subsingleton S]

/-- Coinduction from a subsingleton subgroup has zero actual integral Tate
cohomology in every degree, with independent group and coefficient universes. -/
theorem coind_tate_isZero (A : Rep.{v} ℤ S) (n : ℤ) :
    Limits.IsZero (tate (Rep.coind S.subtype A) n) := by
  let : Subsingleton
      (coindLiftSubgroup S : Subgroup (ULift.{max u v} G)) :=
    (coindLiftSubgroupEquiv S).injective.subsingleton
  have hnative : Limits.IsZero
      (tateCohomology ((nativeFunctor G).obj (Rep.coind S.subtype A)) n) :=
    Limits.IsZero.of_iso
      (TateCohomology.isZero_coind_subsingleton (coindLiftRepresentation A) n)
      ((tateCohomologyFunctor n).mapIso (nativeCoindIso A))
  let T := tateCohomology ((nativeFunctor G).obj (Rep.coind S.subtype A)) n
  let F := IntegralGroupCohomology.integerScalars.{max u v}
  let : F.Additive := IntegralGroupCohomology.integerScalars_additive
  have hid : 𝟙 T = 0 := hnative.eq_of_src _ _
  change Limits.IsZero (F.obj T)
  rw [Limits.IsZero.iff_id_eq_zero, ← F.map_id, hid, F.map_zero]

end IntegralGroupCohomology.Universe
