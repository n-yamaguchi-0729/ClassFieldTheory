/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.PeriodicGalois

/-!
# The actual periodic automorphism over the original fixed field

Restriction preserves the original fixed field pointwise. It therefore gives
an algebra automorphism, with the same order as the restricted ring automorphism.
-/

noncomputable section

namespace RingAut

variable {K F : Type*} [Field K] [Field F]

/-- The restricted automorphism fixes the original field identified with the fixed subfield. -/
def periodicAlgAut (σ : RingAut F) (n : ℕ) (e : K ≃+* periodicSubfield σ 1) :
    let _ := periodicExtensionAlgebra σ n e
    periodicSubfield σ n ≃ₐ[K] periodicSubfield σ n := by
  intro alg
  apply AlgEquiv.ofRingEquiv (f := periodicAut σ n)
  intro x
  apply Subtype.ext
  change σ (e x : F) = (e x : F)
  have hx : (σ ^ 1) (e x : F) = (e x : F) := (e x).property
  simpa only [pow_one] using hx

/-- The algebra automorphism is the actual restriction on the underlying field elements. -/
theorem periodicAlgAut_apply (σ : RingAut F) (n : ℕ)
    (e : K ≃+* periodicSubfield σ 1) (x : periodicSubfield σ n) :
    let _ := periodicExtensionAlgebra σ n e
    (periodicAlgAut σ n e x : F) = σ (x : F) := rfl

/-- Passing to algebra automorphisms does not change the exact order. -/
theorem orderOf_periodicAlgAut (σ : RingAut F) (n : ℕ) (e : K ≃+* periodicSubfield σ 1) :
    let _ := periodicExtensionAlgebra σ n e
    orderOf (periodicAlgAut σ n e) = orderOf (periodicAut σ n) := by
  intro alg
  let P := periodicSubfield σ n
  let ι : (P ≃ₐ[K] P) →* RingAut P :=
    { toFun := fun g => g.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun g h hgh =>
    AlgEquiv.ext (fun x => RingEquiv.congr_fun hgh x)
  exact (orderOf_injective ι hι (periodicAlgAut σ n e)).symm

end RingAut
