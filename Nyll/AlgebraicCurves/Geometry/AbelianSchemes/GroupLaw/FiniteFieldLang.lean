/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.LangMap
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemeBaseChange
import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange

/-!
# Lang surjectivity for actual finite-field abelian schemes

The Frobenius is the morphism constructed from powers on rings of sections and
base change of the original finite-field scheme. Its proved cotangent vanishing
discharges Lang's geometric hypothesis. No Frobenius or differential assumption
is supplied by the caller.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    (L : RelativeGroupLaw k (X ↘ Spec (CommRingCat.of k))) (hc : L.IsCommutative)

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "g" => pullback.snd f b

/-- Actual arithmetic Frobenius as an endomorphism over the extended constants. -/
def finiteFieldFrobeniusOver : SchemeHomOver g g :=
  ⟨Scheme.constantBaseChangeFrobenius k Ω X,
    Scheme.constantBaseChangeFrobenius_snd k Ω X⟩

/-- The Lang map of the actual finite-field Frobenius after extending constants. -/
def finiteFieldLangMap : SchemeHomOver g g :=
  (L.baseChange b).langMap (hc.baseChange b) (finiteFieldFrobeniusOver k Ω X)

variable (hX : AbelianSchemePropertyBundle k (X ↘ Spec (CommRingCat.of k)))

include hX

/-- The actual finite-field Lang map is étale in every characteristic. -/
theorem etale_finiteFieldLangMap : Etale (finiteFieldLangMap k Ω X L hc).val :=
  (L.baseChange b).etale_langMap_of_map_maximalIdeal_le_sq (hc.baseChange b)
    (hX.baseChange_of_field b) (finiteFieldFrobeniusOver k Ω X)
    (Scheme.constantBaseChangeFrobenius_map_maximalIdeal_le_sq k Ω X)

/-- The actual finite-field Lang map is surjective in every characteristic. -/
theorem surjective_finiteFieldLangMap : Surjective (finiteFieldLangMap k Ω X L hc).val :=
  (L.baseChange b).surjective_langMap_of_map_maximalIdeal_le_sq (hc.baseChange b)
    (hX.baseChange_of_field b) (finiteFieldFrobeniusOver k Ω X)
    (Scheme.constantBaseChangeFrobenius_map_maximalIdeal_le_sq k Ω X)

/-- Every geometric point has a preimage under the actual finite-field Lang map. -/
theorem surjective_finiteFieldLangMap_points :
    Function.Surjective (fun x : SchemeHomOver (𝟙 (Spec (.of Ω))) g =>
      NeronModelInfra.schemeHomOverComp x (finiteFieldLangMap k Ω X L hc)) :=
  (L.baseChange b).surjective_langMap_points_of_map_maximalIdeal_le_sq (hc.baseChange b)
    (hX.baseChange_of_field b) (finiteFieldFrobeniusOver k Ω X)
    (Scheme.constantBaseChangeFrobenius_map_maximalIdeal_le_sq k Ω X)

end GoodReductionJacobian.RelativeGroupLaw
