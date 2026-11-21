/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFrobenius
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilGroup
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup

/-!
# Arithmetic degree of the absolute local Artin map

Finite unramified restrictions compute the profinite degree on the existing
absolute Artin map. The integer coordinate uses the normalized valuation
which sends an inverse DVR uniformizer to one.
-/

@[expose] public section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation ClassFieldTower.Martinet.Shafarevich LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ProCGroups.Abelian

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem mem_intrinsicAbstractBase (g : Gal(SeparableClosure K/K)) :
    g ∈ (intrinsicAbstractBase K).toSubgroup := by
  change g ∈ (RamificationTheory.closedFixingSubgroup K (SeparableClosure K) ⊥).toSubgroup
  rw [closedFixingSubgroup_bot_eq_baseField]
  exact Subgroup.mem_top g

/-- The standard unramified subextension is fixed by the kernel of the
literal residue degree reduced modulo its degree. -/
theorem localFiniteUnramifiedField_mem_fixingSubgroup_iff
    (d : ℕ) (hd : 0 < d) (g : Gal(SeparableClosure K/K)) :
    g ∈ (localFiniteUnramifiedField K d hd).fixingSubgroup ↔
      zHatReductionMul d hd (localResidueDegree K g) = 1 := by
  let D := localResidueDatum K
  let B := (intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField D
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  change g ∈ (abstractFixedField K (SeparableClosure K) U.field).fixingSubgroup ↔ _
  rw [InfiniteGalois.fixingSubgroup_fixedField U.field]
  change g ∈ D.unramifiedExtensionOfDegree B d hd ↔ _
  rw [DegreeData.mem_unramifiedExtensionOfDegree_iff]
  have hdegree (x : B.toSubgroup) :
      D.normalizedDegree B x = localResidueDegree K x.1 := by
    apply Multiplicative.ext
    have h := D.residueDegree_nsmul_normalizedDegree B x
    have hB : (B.residueDegree : ℕ) = 1 := intrinsicFiniteAbstractBase_residueDegree_eq_one K
    rw [hB, one_nsmul] at h
    exact h
  constructor
  · rintro ⟨x, hx, rfl⟩
    change zHatReductionMul d hd (D.normalizedDegree B x) = 1 at hx
    rwa [hdegree x] at hx
  · intro hg
    let x : B.toSubgroup := ⟨g, mem_intrinsicAbstractBase K g⟩
    refine ⟨x, ?_, rfl⟩
    change zHatReductionMul d hd (D.normalizedDegree B x) = 1
    rw [hdegree x]
    exact hg

/-- A degree-one element restricts to the standard Frobenius in every
canonical finite unramified layer of the same separable closure. -/
theorem restrictNormalHom_localFiniteUnramifiedField_of_degree_one
    (d : ℕ) (hd : 0 < d) (g : Gal(SeparableClosure K/K))
    (hg : localResidueDegree K g = Multiplicative.ofAdd (1 : ZHat)) :
    AlgEquiv.restrictNormalHom (localFiniteUnramifiedField K d hd) g =
      arithmeticFrobeniusOfUnramifiedValuation K (localFiniteUnramifiedField K d hd) := by
  let E := localFiniteUnramifiedField K d hd
  let gB : (intrinsicAbstractBase K).toSubgroup := ⟨g, mem_intrinsicAbstractBase K g⟩
  have hF := finiteGaloisRestriction_eq_arithmeticFrobenius_of_degree_one K E E.val gB hg
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have h := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply K E E.val gB x
  rw [hF] at h
  change ((AlgEquiv.restrictNormalHom E g) x : SeparableClosure K) =
    E.val (arithmeticFrobeniusOfUnramifiedValuation K E x)
  rw [AlgEquiv.restrictNormalHom_apply]
  exact h.symm

/-- The arithmetic residue degree of the existing absolute Artin symbol is
the embedded integer valuation. This checks the sign at every finite layer. -/
theorem localAbsoluteAbelianResidueDegree_separableAbsoluteLocalArtinMap (a : Kˣ) :
    localAbsoluteAbelianResidueDegree K (separableAbsoluteLocalArtinMap K a) =
      localWeilIntegerInclusion (valuationUnitsMulHom K a) := by
  let G := Gal(SeparableClosure K / K)
  obtain ⟨g, hg⟩ := TopologicalAbelianization.surjective_mk G (separableAbsoluteLocalArtinMap K a)
  obtain ⟨phi, hphi⟩ := localResidueDegree_surjective K (Multiplicative.ofAdd (1 : ZHat))
  let v : ℤ := valuationMap K (Additive.ofMul a)
  rw [← hg]
  apply Multiplicative.ext
  apply ZHat.ext
  intro d hd
  let E := localFiniteUnramifiedField K d hd
  let r : G →* Gal(E / K) := AlgEquiv.restrictNormalHom E
  let q : G →* Multiplicative (ZMod d) :=
    ((zHatReductionMul d hd).comp (localResidueDegree K)).toMonoidHom
  have hg' : (QuotientGroup.mk g : localAbsoluteAbelianProfinite K) =
      separableAbsoluteLocalArtinMap K a := hg
  have hfinite : r g = abelianLocalArtinMap K E a :=
    (absoluteAbelianRestriction_mk K E g).symm.trans
      ((congrArg (absoluteAbelianRestriction K E) hg').trans
        (separableAbsoluteLocalArtinMap_restriction K E a))
  have hr : r g = r (phi ^ v) := calc
    r g = abelianLocalArtinMap K E a := hfinite
    _ = arithmeticFrobeniusOfUnramifiedValuation K E ^ v := by
      change (abelianLocalArtinMap K E).toMonoidHom a = _
      rw [abelianLocalArtinMap_toMonoidHom]
      exact Universe.abelianLocalArtinMonoidHom_eq_frobenius_zpow K E a
    _ = r phi ^ v := congrArg (fun x : Gal(E/K) => x ^ v)
      (restrictNormalHom_localFiniteUnramifiedField_of_degree_one K d hd phi hphi).symm
    _ = r (phi ^ v) := (map_zpow r phi v).symm
  have hfix : g * (phi ^ v)⁻¹ ∈ E.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    change r (g * (phi ^ v)⁻¹) = 1
    rw [map_mul, map_inv, hr, mul_inv_cancel]
  have hq : q g = q (phi ^ v) := by
    have h := (localFiniteUnramifiedField_mem_fixingSubgroup_iff K d hd _).mp hfix
    change q (g * (phi ^ v)⁻¹) = 1 at h
    rw [map_mul, map_inv] at h
    exact mul_inv_eq_one.mp h
  have hqphi : (q phi).toAdd = 1 := by
    change zHatReduction d hd (localResidueDegree K phi).toAdd = 1
    rw [hphi]
    exact zHatReduction_one d hd
  change (q g).toAdd = zHatReduction d hd (v : ZHat)
  rw [hq, map_zpow, zHatReduction_intCast]
  change v • (q phi).toAdd = (v : ZMod d)
  rw [hqphi, zsmul_eq_mul, mul_one]

end LocalClassFieldTheory
