/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Representation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediateAction
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits

/-!
# The actual relative action on fixed idele-class coefficients

The carrier comparison with fixed-field idele classes intertwines the
abstract quotient action and the actual relative Galois action.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology
open IdeleClassGroup.FiniteExtensionLimit

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- Fixed coefficients in an abstract extension are actual upper-field idele classes. -/
def extensionClassEquiv (H J : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup) (hnormal : (extensionSubgroup H J hJH).Normal)
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) J (le_baseField J))) :
    let _ : FiniteDimensional K (abstractFixedField K Ω J) :=
      abstractFixedField_finiteDimensional K Ω J hfinite
    (extensionFixedRepresentation (ideleClassRepresentation k K Ω) H J hJH hnormal).V ≃+
      Additive (IdeleClassGroup k (abstractFixedField K Ω J)) := by
  intro hEfinite
  exact (extensionFixedRepresentationEquiv (ideleClassRepresentation k K Ω) H J hJH hnormal).trans
    (abstractFixedClassEquiv k K Ω J hfinite).symm

/-- The inverse carrier comparison is the actual inclusion of upper-field idele classes. -/
theorem extensionClassEquiv_symm_coe (H J : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup) (hnormal : (extensionSubgroup H J hJH).Normal)
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) J (le_baseField J))) :
    let _ : FiniteDimensional K (abstractFixedField K Ω J) :=
      abstractFixedField_finiteDimensional K Ω J hfinite
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω J)),
      ((extensionClassEquiv k K Ω H J hJH hnormal hfinite).symm c).1 =
        Additive.ofMul (ofIntermediate (k := k) (abstractFixedField K Ω J) c.toMul) := by
  intro hEfinite c
  exact abstractFixedClassEquiv_coe k K Ω J hfinite c

/-- The abstract quotient acts through the actual relative Galois group on idele classes. -/
theorem extensionClassEquiv_symm_action (H J : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup) (hnormal : (extensionSubgroup H J hJH).Normal)
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) J (le_baseField J))) :
    let _ : FiniteDimensional K (abstractFixedField K Ω J) :=
      abstractFixedField_finiteDimensional K Ω J hfinite
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
    let _ : IsScalarTower k (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : Algebra k (abstractRelativeFixedField K Ω hJH) :=
      inferInstanceAs (Algebra k (abstractFixedField K Ω J))
    let _ : IsScalarTower k (abstractFixedField K Ω H) (abstractRelativeFixedField K Ω hJH) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ := hnormal
    ∀ (q : H.toSubgroup ⧸ extensionSubgroup H J hJH)
      (c : Additive (IdeleClassGroup k (abstractFixedField K Ω J))),
      (extensionFixedRepresentation (ideleClassRepresentation k K Ω) H J hJH hnormal).ρ q
          ((extensionClassEquiv k K Ω H J hJH hnormal hfinite).symm c) =
        (extensionClassEquiv k K Ω H J hJH hnormal hfinite).symm
          (Additive.ofMul (AlgebraicCurve.SemilinearAut.ofAlgAut
            (show abstractFixedField K Ω J ≃ₐ[k] abstractFixedField K Ω J from
              (abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hnormal q).restrictScalars k) •
              c.toMul)) := by
  intro hEfinite aFE hkFE akE hkFErel hnorm q c
  refine Quotient.inductionOn' q ?_
  intro σ
  apply Subtype.ext
  change (ideleClassRepresentation k K Ω).ρ σ.1
      ((extensionClassEquiv k K Ω H J hJH hnormal hfinite).symm c).1 = _
  rw [extensionClassEquiv_symm_coe, extensionClassEquiv_symm_coe]
  apply congrArg Additive.ofMul
  exact (ofIntermediate_algAut_smul (abstractFixedField K Ω J) σ.1
    ((abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hnormal
      (QuotientGroup.mk' (extensionSubgroup H J hJH) σ)).restrictScalars k)
    (fun x => abstractExtensionQuotientEquivGaloisGroup_mk_apply_val K Ω H J hJH hnormal σ x)
    c.toMul).symm

/-- Each abstract norm summand is the corresponding actual Galois conjugate in the limit. -/
theorem abstractFixedClassEquiv_relativeCosetAction (H J : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup) (hnormal : (extensionSubgroup H J hJH).Normal)
    (hfinite : Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(Ω/K)) J (le_baseField J))) :
    let _ : FiniteDimensional K (abstractFixedField K Ω J) :=
      abstractFixedField_finiteDimensional K Ω J hfinite
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
    let _ : IsScalarTower k (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ := hnormal
    let r : (H.toSubgroup ⧸ extensionSubgroup H J hJH) ≃*
        Gal((abstractFixedField K Ω J)/(abstractFixedField K Ω H)) :=
      abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hnormal
    ∀ (q : H.toSubgroup ⧸ extensionSubgroup H J hJH)
      (c : Additive (IdeleClassGroup k (abstractFixedField K Ω J))),
      relativeCosetAction (ideleClassRepresentation k K Ω) H J hJH
          (abstractFixedClassEquiv k K Ω J hfinite c) q =
        Additive.ofMul (ofIntermediate (k := k) (abstractFixedField K Ω J)
          (AlgebraicCurve.SemilinearAut.ofAlgAut ((r q).restrictScalars k) • c.toMul)) := by
  intro hEfinite aFE hkFE hnorm r q c
  let akE : Algebra k (abstractRelativeFixedField K Ω hJH) :=
    inferInstanceAs (Algebra k (abstractFixedField K Ω J))
  have hkFErel : IsScalarTower k (abstractFixedField K Ω H) (abstractRelativeFixedField K Ω hJH) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have h := congrArg Subtype.val
    (extensionClassEquiv_symm_action k K Ω H J hJH hnormal hfinite q c)
  rw [extensionFixedRepresentation_action_coe, extensionClassEquiv_symm_coe] at h
  exact h

end FunctionField
