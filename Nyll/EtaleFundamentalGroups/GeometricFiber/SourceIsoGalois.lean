/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIso
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticSurjective
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationConjugacy

/-!
# The coefficient label of a source-induced arithmetic action

The original point formulas identify the source action with the extended
absolute Galois action. All comparisons retain their specified field maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable (k L Ω : Type u) [Field k] [Field L] [Field Ω]
    [Algebra k L] [IsSepClosure k L] [Algebra L Ω] [Algebra k Ω]
    [IsScalarTower k L Ω] [IsSepClosed Ω]

/-- The actual point action determines the coefficient Galois element. -/
theorem fundamentalGroupHom_sourceAction_eq_extendedGalois
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (xi : Spec (.of Ω) ⟶ X)
    (e : Spec (.of Ω) ≅ Spec (.of Ω)) (ρ : Ω →+* Ω)
    (he : e.hom = Spec.map (CommRingCat.ofHom ρ))
    (σ : Gal(L/k))
    (hρ : ρ.comp (algebraMap L Ω) = (algebraMap L Ω).comp σ.toRingHom)
    (hsource : e.hom ≫ xi = xi) (hbase : xi ≫ f = ξ k Ω) :
    (eqToIso (congrArg fiber hbase)).conjAut
        (fundamentalGroupHom f xi
          (Aut.of (fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource)))) =
      absoluteGaloisToExtendedFiberAut k L Ω σ := by
  let g : Aut (fiber xi) := Aut.of (fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource))
  have hg (A : FiniteEtale X) (v : (fiber xi).obj A) :
      (fiberObjEquivHom xi A (g.asIso.hom.app A v)).left =
        Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom xi A v).left := by
    rw [fiberSourceIso_aut_point xi e hsource, he]
  have hp := fundamentalGroupHom_point_of_point_action f xi g ρ hg
  apply Aut.ext
  apply Iso.ext
  ext A v
  apply (fiberObjEquivHom (ξ k Ω) A).injective
  ext1
  exact (point_action_of_eqToIso hbase (fundamentalGroupHom f xi g) ρ hp A v).trans
    (absoluteGaloisToExtendedFiberAut_point k L Ω σ ρ hρ A v).symm

/-- A single inner correction, determined by the original base-point comparison,
identifies every source-induced arithmetic label with its coefficient action. -/
theorem arithmeticFundamentalGroupHom_sourceAction
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (xi : Spec (.of Ω) ⟶ X)
    (hbase : xi ≫ f = ξ k Ω) :
    ∃ α : Gal(L/k), ∀ (e : Spec (.of Ω) ≅ Spec (.of Ω)) (ρ : Ω →+* Ω)
      (_he : e.hom = Spec.map (CommRingCat.ofHom ρ)) (σ : Gal(L/k))
      (_hρ : ρ.comp (algebraMap L Ω) = (algebraMap L Ω).comp σ.toRingHom)
      (hsource : e.hom ≫ xi = xi),
      arithmeticFundamentalGroupHom k L f xi
          (Aut.of (fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource))) =
        α * σ * α⁻¹ := by
  let : IsSepClosed L := IsSepClosure.sep_closed k
  let ε := suppliedGaloisEquivFundamentalGroup k L
  let E := fieldFiberExtensionIso k L Ω
  let q := eqToIso (congrArg fiber hbase)
  let tc := q ≪≫ E.symm
  let t : fiber (xi ≫ f) ≅ fib k L :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k L)).some
  let δ : Aut (fib k L) := Aut.of (tc.symm ≪≫ t)
  refine ⟨ε.symm δ, ?_⟩
  intro e ρ he σ hρ hsource
  let g : Aut (fiber xi) := Aut.of (fiberSourceIso xi e ≪≫ eqToIso (congrArg fiber hsource))
  have hfield := fundamentalGroupHom_sourceAction_eq_extendedGalois
    k L Ω f xi e ρ he σ hρ hsource hbase
  have hc : tc.conjAut (fundamentalGroupHom f xi g) = ε σ := by
    change (q ≪≫ E.symm).conjAut (fundamentalGroupHom f xi g) = ε σ
    rw [Iso.trans_conjAut, hfield]
    change E.symm.conjAut (E.conjAut (ε σ)) = ε σ
    apply Aut.ext
    simp only [Iso.conjAut_apply, Iso.symm_symm_eq, Iso.trans_assoc,
      Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]
  have hchoice := continuousConjAut_eq_conj tc t (fundamentalGroupHom f xi g)
  change t.conjAut (fundamentalGroupHom f xi g) =
    δ * tc.conjAut (fundamentalGroupHom f xi g) * δ⁻¹ at hchoice
  rw [hc] at hchoice
  change ε.symm (t.conjAut (fundamentalGroupHom f xi g)) = ε.symm δ * σ * (ε.symm δ)⁻¹
  rw [hchoice, map_mul, map_mul, map_inv, ε.symm_apply_apply]

end AlgebraicGeometry.FiniteEtale
