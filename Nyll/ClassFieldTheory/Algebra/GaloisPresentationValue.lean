/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits

/-!
# Values of Galois transport through fixed-field presentations

Transport from a relative fixed field to an isomorphic extension retains
the action of the original ambient automorphism on embedded elements.
-/

noncomputable section

namespace ClassFieldTheory

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [IsGalois K Ω]

/-- The transported quotient automorphism acts through the given ambient embedding. -/
theorem galoisPresentation_mk_apply_val
    (H T : ClosedSubgroup Gal(Ω/K)) (hTH : T.toSubgroup ≤ H.toSubgroup)
    (hn : (extensionSubgroup H T hTH).Normal)
    (eE : L ≃ₐ[K] abstractFixedField K Ω T) :
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω T) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hTH)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H) (abstractFixedField K Ω T) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    ∀ (hF : Module.finrank K (abstractFixedField K Ω H) = 1)
      (σ : H.toSubgroup) (x : L),
      (eE (((galoisRestrictScalarsEquivOfFinrankOne
        (K := K) (F := abstractFixedField K Ω H) (E := abstractFixedField K Ω T) hF).trans
        (AlgEquiv.autCongr eE).symm)
          (abstractExtensionQuotientEquivGaloisGroup K Ω H T hTH hn
            (QuotientGroup.mk' (extensionSubgroup H T hTH) σ)) x) : Ω) =
        σ.val (eE x : Ω) := by
  intro aHT hKHT hF σ x
  let τ : Gal((abstractFixedField K Ω T)/(abstractFixedField K Ω H)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H T hTH hn
      (QuotientGroup.mk' (extensionSubgroup H T hTH) σ)
  have he := congrArg (fun y : abstractFixedField K Ω T => (y : Ω))
    (eE.apply_symm_apply (τ (eE x)))
  exact he.trans (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    K Ω H T hTH hn σ (eE x)).symm

end ClassFieldTheory
