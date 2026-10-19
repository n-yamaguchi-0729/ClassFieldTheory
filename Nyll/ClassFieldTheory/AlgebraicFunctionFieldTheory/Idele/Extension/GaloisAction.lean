/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.AlgEquiv
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# The extension Galois action on function-field ideles

Restricting scalars and then using the completed semilinear action gives the
canonical action of the extension automorphism group. The action uses the
existing places, completed field maps, and principal-idele quotient.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

namespace IdeleGroup

/-- Extension automorphisms act through the existing completed semilinear action. -/
instance galoisMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup k L) :=
  MulDistribMulAction.compHom (IdeleGroup k L)
    (SemilinearAut.ofAlgAut.comp (AlgEquiv.restrictScalarsHom k))

/-- The extension action is exactly the completed semilinear action. -/
theorem smul_algAut_eq_semilinear (σ : L ≃ₐ[K] L) (a : IdeleGroup k L) :
    σ • a = SemilinearAut.ofAlgAut (σ.restrictScalars k) • a :=
  rfl

/-- Each extension automorphism acts continuously on the restricted product. -/
theorem continuous_algAut_smul (σ : L ≃ₐ[K] L) :
    Continuous (fun a : IdeleGroup k L => σ • a) :=
  continuous_semilinearHom (SemilinearAut.ofAlgAut (σ.restrictScalars k))

end IdeleGroup

namespace IdeleClassGroup

variable [HasPrincipalDivisors k L]

/-- The extension action on classes is the action descended from actual ideles. -/
instance galoisMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup k L) :=
  MulDistribMulAction.compHom (IdeleClassGroup k L)
    (SemilinearAut.ofAlgAut.comp (AlgEquiv.restrictScalarsHom k))

/-- The extension action on classes is the established semilinear action. -/
theorem smul_algAut_eq_semilinear (σ : L ≃ₐ[K] L) (c : IdeleClassGroup k L) :
    σ • c = SemilinearAut.ofAlgAut (σ.restrictScalars k) • c :=
  rfl

/-- Passing from ideles to classes respects the extension action. -/
@[simp]
theorem algAut_smul_mk (σ : L ≃ₐ[K] L) (a : IdeleGroup k L) :
    σ • mk (k := k) (K := L) a = mk (k := k) (K := L) (σ • a) :=
  rfl

/-- Every extension automorphism acts continuously on the quotient topology. -/
theorem continuous_algAut_smul (σ : L ≃ₐ[K] L) :
    Continuous (fun c : IdeleClassGroup k L => σ • c) :=
  continuous_semilinearHom (SemilinearAut.ofAlgAut (σ.restrictScalars k))

end IdeleClassGroup

end FunctionField
