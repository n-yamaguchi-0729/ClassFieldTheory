/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.ExtensionRepresentation

/-!
# Relative idele classes as the actual fixed representation

The proved carrier and action comparisons give an isomorphism of integral
representations. It transports Tate cohomology, including both low degrees
required by the abstract class-field axiom.
-/

noncomputable section

namespace FunctionField

open CategoryTheory ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- The actual fixed representation is the relative Galois representation on idele classes. -/
def extensionClassRepresentationIso (H J : ClosedSubgroup Gal(Ω/K))
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
    extensionFixedRepresentation (ideleClassRepresentation k K Ω) H J hJH hnormal ≅
      Rep.res r.toMonoidHom (Rep.ofMulDistribMulAction
        Gal((abstractFixedField K Ω J)/(abstractFixedField K Ω H))
        (IdeleClassGroup k (abstractFixedField K Ω J))) := by
  intro hEfinite aFE hkFE hnorm r
  let akE : Algebra k (abstractRelativeFixedField K Ω hJH) :=
    inferInstanceAs (Algebra k (abstractFixedField K Ω J))
  have hkFErel : IsScalarTower k (abstractFixedField K Ω H) (abstractRelativeFixedField K Ω hJH) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let e := extensionClassEquiv k K Ω H J hJH hnormal hfinite
  refine Rep.mkIso (Representation.Equiv.mk e.toIntLinearEquiv ?_)
  intro q
  apply LinearMap.ext
  intro x
  change e ((extensionFixedRepresentation (ideleClassRepresentation k K Ω) H J hJH hnormal).ρ q x) =
    Additive.ofMul (AlgebraicCurve.SemilinearAut.ofAlgAut ((r q).restrictScalars k) • (e x).toMul)
  apply e.symm.injective
  rw [AddEquiv.symm_apply_apply]
  have h := extensionClassEquiv_symm_action k K Ω H J hJH hnormal hfinite q (e x)
  have he : (extensionClassEquiv k K Ω H J hJH hnormal hfinite).symm (e x) = x :=
    e.symm_apply_apply x
  rw [he] at h
  exact h

end FunctionField
