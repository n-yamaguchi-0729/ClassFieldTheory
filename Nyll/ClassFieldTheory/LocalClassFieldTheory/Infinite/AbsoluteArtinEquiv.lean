/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation

/-!
# Absolute local Artin maps under local field equivalences

Conjugation acts on the same finite abelian restrictions that define the
absolute local Artin map.
-/

@[expose] public section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFieldTower.Martinet.Shafarevich LocalFieldTheory ProCGroups.Abelian
open RamificationTheory.Field.absoluteGaloisGroup

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  (a : K ≃+* L) (c : SeparableClosure K ≃+* SeparableClosure L)
  (hc : ∀ x : K, c (algebraMap K (SeparableClosure K) x) =
    algebraMap L (SeparableClosure L) (a x))

/-- Compatible local field equivalences transport each absolute Artin value by conjugation. -/
theorem separableAbsoluteLocalArtinMap_equiv (hv : SemilinearValuationCompatible K L a)
    (x : Kˣ) :
    TopologicalAbelianization.congr (ClassFieldTheory.semilinearGaloisContinuousEquiv a c hc)
        (separableAbsoluteLocalArtinMap K x) =
      separableAbsoluteLocalArtinMap L (Units.map a.toMonoidHom x) := by
  apply ProCGroups.ProC.OpenNormalSubgroup.eq_of_forall_quotientProj_eq
    (G := localAbsoluteAbelianProfinite L)
  intro N
  let : N.toSubgroup.Normal := N.isNormal'
  apply (absoluteFiniteQuotientEquiv L N).injective
  let E := absoluteFiniteQuotientField L N
  let M := semilinearRingEquivPreimageIntermediateField a c hc E
  let b : M ≃+* E :=
    { toFun := fun z => ⟨c z.1, z.2⟩
      invFun := fun z => ⟨c.symm z.1,
        semilinearRingEquivPreimageIntermediateField_symm_mem a c hc E z.2⟩
      left_inv := fun z => Subtype.ext (c.symm_apply_apply z.1)
      right_inv := fun z => Subtype.ext (c.apply_symm_apply z.1)
      map_mul' := fun z w => Subtype.ext (map_mul c z.1 w.1)
      map_add' := fun z w => Subtype.ext (map_add c z.1 w.1) }
  have hb (z : K) : b (algebraMap K M z) = algebraMap L E (a z) :=
    Subtype.ext (hc z)
  let : FiniteDimensional K M := finiteDimensional_semilinearRingEquivPreimageIntermediateField
    a c hc E
  let : IsAbelianGalois K M := ClassFieldTheory.isAbelianGalois_of_equiv_equiv
    a.symm b.symm (RingHom.ext fun z =>
      (ClassFieldTheory.semilinear_symm_algebraMap a b hb z).symm)
  have hr (y : localAbsoluteAbelianProfinite L) :
      absoluteAbelianRestriction L E y = absoluteFiniteQuotientEquiv L N (QuotientGroup.mk y) := by
    refine QuotientGroup.induction_on y fun sigma => ?_
    rw [absoluteAbelianRestriction_mk, absoluteFiniteQuotientEquiv_mk_mk]
  let e := ClassFieldTheory.semilinearGaloisContinuousEquiv a c hc
  let y : localAbsoluteAbelianProfinite L :=
    TopologicalAbelianization.congr e (separableAbsoluteLocalArtinMap K x)
  let y' : localAbsoluteAbelianProfinite L :=
    separableAbsoluteLocalArtinMap L (Units.map a.toMonoidHom x)
  change absoluteFiniteQuotientEquiv L N (QuotientGroup.mk y) =
    absoluteFiniteQuotientEquiv L N (QuotientGroup.mk y')
  obtain ⟨σ, hσ⟩ := TopologicalAbelianization.surjective_mk
    Gal(SeparableClosure K / K) (separableAbsoluteLocalArtinMap K x)
  have hx : AlgEquiv.restrictNormalHom M σ = abelianLocalArtinMap K M x :=
    (absoluteAbelianRestriction_mk K M σ).symm.trans
      ((congrArg (absoluteAbelianRestriction K M) hσ).trans
        (separableAbsoluteLocalArtinMap_restriction K M x))
  have hy : y = (QuotientGroup.mk (e σ) : localAbsoluteAbelianProfinite L) :=
    (congrArg (TopologicalAbelianization.congr e) hσ).symm.trans
      (TopologicalAbelianization.congr_apply_mk e σ)
  have hnat := abelianLocalArtinMonoidHom_semilinear_conjugation_apply K L M E a b hb hv x
  simp only [← LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom] at hnat
  change semilinearGaloisGroupCongr K L M E a b hb (abelianLocalArtinMap K M x) =
    abelianLocalArtinMap L E (Units.map a.toMonoidHom x) at hnat
  have hrestrict : AlgEquiv.restrictNormalHom E (e σ) =
      semilinearGaloisGroupCongr K L M E a b hb (AlgEquiv.restrictNormalHom M σ) := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨w, rfl⟩ := b.surjective z
    rw [semilinearGaloisGroupCongr_apply_equiv]
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    have hw : (b ((AlgEquiv.restrictNormalHom M σ) w) : SeparableClosure L) =
        c (σ (w : SeparableClosure K)) := by
      change c (↑((AlgEquiv.restrictNormalHom M σ) w) : SeparableClosure K) = _
      rw [AlgEquiv.restrictNormalHom_apply]
    rw [hw]
    change c (σ (c.symm (c w.1))) = c (σ w.1)
    rw [c.symm_apply_apply]
  calc
    _ = absoluteAbelianRestriction L E y := (hr y).symm
    _ = AlgEquiv.restrictNormalHom E (e σ) :=
      (congrArg (absoluteAbelianRestriction L E) hy).trans
        (absoluteAbelianRestriction_mk L E (e σ))
    _ = semilinearGaloisGroupCongr K L M E a b hb (AlgEquiv.restrictNormalHom M σ) := hrestrict
    _ = abelianLocalArtinMap L E (Units.map a.toMonoidHom x) :=
      (congrArg (semilinearGaloisGroupCongr K L M E a b hb) hx).trans hnat
    _ = absoluteAbelianRestriction L E y' :=
      (separableAbsoluteLocalArtinMap_restriction L E _).symm
    _ = _ := hr y'

end LocalClassFieldTheory
