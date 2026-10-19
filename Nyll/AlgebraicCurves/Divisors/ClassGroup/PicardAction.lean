/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree

/-!
# Semilinear action on the full Picard degree sequence

Actual semilinear automorphisms preserve principal divisors and degree.
Their action on the full divisor class group restricts to the existing Picard-zero action.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

namespace SemilinearAut

/-- The induced additive map on the actual full Picard group. -/
def picSMulHom (g : SemilinearAut K F) : Pic K F →+ Pic K F :=
  QuotientAddGroup.map _ _ (DistribSMul.toAddMonoidHom (Divisor K F) g)
    (fun _ h => smul_mem_principal g h)

/-- The canonical semilinear action on divisor classes. -/
instance picDistribMulAction : DistribMulAction (SemilinearAut K F) (Pic K F) where
  smul g x := picSMulHom g x
  one_smul x := by
    obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
    change H1Gm.mk ((1 : SemilinearAut K F) • D) = H1Gm.mk D
    rw [one_smul]
  mul_smul g h x := by
    obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
    change H1Gm.mk ((g * h) • D) = H1Gm.mk (g • (h • D))
    rw [mul_smul]
  smul_zero g := (picSMulHom g).map_zero
  smul_add g x y := (picSMulHom g).map_add x y

/-- The action on classes is induced by the actual action on divisors. -/
theorem pic_smul_mk (g : SemilinearAut K F) (D : Divisor K F) :
    g • H1Gm.mk D = H1Gm.mk (g • D) := rfl

end SemilinearAut

namespace H1Gm

/-- Inclusion of degree-zero classes respects the semilinear action. -/
theorem ofPic0_smul (g : SemilinearAut K F) (x : Pic0 K F) :
    ofPic0 K F (g • x) = g • ofPic0 K F x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rfl

/-- Semilinear action preserves the actual Picard degree. -/
theorem degree_smul [HasPrincipalDivisors K F] (g : SemilinearAut K F) (x : Pic K F) :
    degree K F (g • x) = degree K F x := by
  obtain ⟨D, rfl⟩ := mk_surjective x
  exact SemilinearAut.degree_smul g D

end H1Gm

end AlgebraicCurve
