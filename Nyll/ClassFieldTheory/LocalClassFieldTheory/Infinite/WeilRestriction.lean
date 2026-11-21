/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.FixedFieldAbsoluteGalois
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldLocalData
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilReciprocity
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Nyll.GaloisCohomology.Topology.FiniteExtensionGalois
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation

/-!
# Inclusion of Weil groups over finite local fixed fields

The existing residue-degree comparison normalizes the degree on the actual
open Galois subgroup. Hence the lift to Weil groups uses multiplication by
the residue degree on the discrete coordinate.
-/

@[expose] public section

open scoped Pointwise Topology ValuativeRel

namespace LocalClassFieldTheory

open ClassFormation LocalFieldTheory ProCGroups.Abelian
open LocalFieldTheory.IsNonarchimedeanLocalField

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (H : FiniteAbstractField (Gal(SeparableClosure K/K)))

local notation "F" => finiteFixedField K H

attribute [local instance] finiteFixedFieldFiniteDimensional finiteFixedFieldNormedField
  finiteFixedFieldValuativeRel finiteFixedFieldLocalField

attribute [local instance] finiteFixedFieldSeparableClosureAlgebra

noncomputable local instance weilFixedFieldAmbientAlgebra : Algebra F (SeparableClosure K) :=
  inferInstanceAs
    (Algebra ↥(abstractFixedField K (SeparableClosure K) H.field) (SeparableClosure K))

local instance weilFixedFieldAmbientTower : IsScalarTower K F (SeparableClosure K) :=
  IsScalarTower.of_algebraMap_eq' rfl

variable (e : SeparableClosure (finiteFixedField K H) ≃ₐ[finiteFixedField K H] SeparableClosure K)

local notation "G" => Gal(SeparableClosure K / K)
local notation "G_F" => Gal(SeparableClosure F / F)

/-- The inclusion on absolute groups induced by the chosen comparison of closures. -/
noncomputable def localFixedFieldAbsoluteInclusion
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) : G_F →ₜ* G where
  toMonoidHom := (AlgEquiv.restrictScalarsHom K).comp (AlgEquiv.autCongr e).toMonoidHom
  continuous_toFun := by
    let : Algebra.IsSeparable F (SeparableClosure K) :=
      Algebra.isSeparable_tower_top_of_isSeparable K F (SeparableClosure K)
    exact (GaloisCohomology.continuous_galoisRestrictScalars K F (SeparableClosure K)).comp
      (AlgebraicNumberTheory.continuous_algEquiv_autCongr e)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem localFixedFieldAbsoluteInclusion_eq_subtype
    (g : G_F) :
    localFixedFieldAbsoluteInclusion K H e g =
      ((abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H.field).symm
        (AlgEquiv.autCongr e g)).1 := by
  let s := abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H.field
  apply AlgEquiv.ext
  intro x
  have h := congrArg (fun f : Gal(SeparableClosure K / F) => f x)
    (s.apply_symm_apply (AlgEquiv.autCongr e g))
  exact h.symm

/-- Passing from the upper to the lower absolute group multiplies residue
degree by the actual residue index of the finite fixed field. -/
theorem localFixedFieldAbsoluteInclusion_residueDegree (g : G_F) :
    (localResidueDegree K (localFixedFieldAbsoluteInclusion K H e g)).toAdd =
      (H.residueDegree (localResidueDatum K) : ℕ) • (localResidueDegree F g).toAdd := by
  let D := localResidueDatum K
  let s := (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H.field).symm
    (AlgEquiv.autCongr e g)
  have h := D.residueDegree_nsmul_normalizedDegree (H.toFiniteResidueAbstractField D) s
  have hnorm := localResidueDegree_eq_normalizedDegree_abstractFixedFieldEquiv K H e g
  change localResidueDegree F g = D.normalizedDegree (H.toFiniteResidueAbstractField D) s at hnorm
  rw [← hnorm] at h
  rw [localFixedFieldAbsoluteInclusion_eq_subtype K H e]
  exact h.symm

private theorem localWeilIntegerInclusion_nsmul
    (d : ℕ) (n : Multiplicative ℤ) :
    (localWeilIntegerInclusion ((nsmulAddMonoidHom d : ℤ →+ ℤ).toMultiplicative n)).toAdd =
      d • (localWeilIntegerInclusion n).toAdd := by
  change ((d • n.toAdd : ℤ) : ZHat) = d • (n.toAdd : ZHat)
  exact map_nsmul (Int.castRingHom ZHat).toAddMonoidHom d n.toAdd

/-- The two coordinates of the Weil inclusion satisfy the lower residue equation. -/
theorem localWeilFixedFieldDegreeCompatibility
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) (x : localWeilGroup F) :
    localResidueDegree K
      (localFixedFieldAbsoluteInclusion K H e (localWeilToAbsolute F x)) =
    localWeilIntegerInclusion
      (Multiplicative.ofAdd
        ((H.residueDegree (localResidueDatum K) : ℕ) • (localWeilDegree F x).toAdd)) := by
  let d : ℕ := H.residueDegree (localResidueDatum K)
  apply Multiplicative.ext
  have h₁ := localFixedFieldAbsoluteInclusion_residueDegree K H e (localWeilToAbsolute F x)
  have h₂ := congrArg (fun z : ZHatMul => d • z.toAdd)
    (localResidueDegree_localWeilToAbsolute F x)
  have h₃ := localWeilIntegerInclusion_nsmul d (localWeilDegree F x)
  exact h₁.trans (h₂.trans h₃.symm)

/-- Weil inclusion with its actual Galois and discrete-degree coordinates. -/
noncomputable def localWeilFixedFieldInclusion
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) :
    localWeilGroup F →ₜ* localWeilGroup K := by
  let g : localWeilGroup F →ₜ* G :=
    (localFixedFieldAbsoluteInclusion K H e).comp (localWeilToAbsolute F)
  let d : ℕ := H.residueDegree (localResidueDatum K)
  let degreeMap := (nsmulAddMonoidHom d : ℤ →+ ℤ).toMultiplicative
  let h : localWeilGroup F →ₜ* Multiplicative ℤ :=
    (⟨degreeMap, continuous_of_discreteTopology⟩ : Multiplicative ℤ →ₜ* Multiplicative ℤ).comp
      (localWeilDegree F)
  let f := g.prod h
  have hf (x : localWeilGroup F) : f x ∈ localWeilGroup K := by
    change localResidueDegree K (g x) = localWeilIntegerInclusion (h x)
    exact localWeilFixedFieldDegreeCompatibility K H e x
  exact ⟨f.toMonoidHom.codRestrict (localWeilGroup K) hf, f.continuous.subtype_mk hf⟩

/-- The lower integral degree is the upper degree multiplied by the residue index. -/
theorem localWeilFixedFieldInclusion_degree (x : localWeilGroup F) :
    (localWeilDegree K (localWeilFixedFieldInclusion K H e x)).toAdd =
      (H.residueDegree (localResidueDatum K) : ℕ) • (localWeilDegree F x).toAdd :=
  rfl

/-- Weil inclusion uses the same Galois action as absolute restriction of scalars. -/
theorem localWeilFixedFieldInclusion_absolute (x : localWeilGroup F) :
    localWeilToAbsolute K (localWeilFixedFieldInclusion K H e x) =
      localFixedFieldAbsoluteInclusion K H e (localWeilToAbsolute F x) :=
  rfl

theorem localWeilFixedFieldInclusion_injective :
    Function.Injective (localWeilFixedFieldInclusion K H e) := by
  intro x y hxy
  apply localWeilToAbsolute_injective F
  apply (AlgEquiv.autCongr e).injective
  apply AlgEquiv.restrictScalars_injective K
  exact congrArg (localWeilToAbsolute K) hxy


/-- The Weil inclusion has image the inverse image of the actual fixing
subgroup under the inclusion into the absolute Galois group. -/
theorem localWeilFixedFieldInclusion_range :
    (localWeilFixedFieldInclusion K H e).toMonoidHom.range =
      H.field.toSubgroup.comap (localWeilToAbsolute K).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change localWeilToAbsolute K (localWeilFixedFieldInclusion K H e y) ∈ H.field.toSubgroup
    rw [localWeilFixedFieldInclusion_absolute, localFixedFieldAbsoluteInclusion_eq_subtype]
    exact Subtype.property _
  · intro hx
    let g := localWeilToAbsolute K x
    let n := (localWeilDegree K x).toAdd
    let s := abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H.field
    have hgMem : g ∈ H.field.toSubgroup := hx
    let gH : H.field.toSubgroup := ⟨g, hgMem⟩
    let gF : G_F := (AlgEquiv.autCongr e).symm (s gH)
    have hg : localFixedFieldAbsoluteInclusion K H e gF = g := by
      calc
        _ = (s.symm ((AlgEquiv.autCongr e) gF)).1 :=
          localFixedFieldAbsoluteInclusion_eq_subtype K H e gF
        _ = (s.symm (s gH)).1 := congrArg (fun v => (s.symm v).1)
          ((AlgEquiv.autCongr e).apply_symm_apply (s gH))
        _ = g := congrArg Subtype.val (s.symm_apply_apply gH)
    let d : ℕ := H.residueDegree (localResidueDatum K)
    have hd : 0 < d := (H.residueDegree (localResidueDatum K)).property
    have hscale : (n : ZHat) = d • (localResidueDegree F gF).toAdd := by
      have h := localFixedFieldAbsoluteInclusion_residueDegree K H e gF
      rw [hg, localResidueDegree_localWeilToAbsolute K x] at h
      exact h
    have hmod : (n : ZMod d) = 0 := by
      rw [← zHatReduction_intCast d hd, hscale, map_nsmul, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul]
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd n d).mp hmod
    have hmDegree : localResidueDegree F gF = Multiplicative.ofAdd (m : ZHat) := by
      apply Multiplicative.ext
      apply zHatMulNat_injective hd
      change d • (localResidueDegree F gF).toAdd = d • (m : ZHat)
      rw [← hscale, hm, Int.cast_mul, nsmul_eq_mul, Int.cast_natCast]
    let y : localWeilGroup F := ⟨(gF, Multiplicative.ofAdd m), hmDegree⟩
    refine ⟨y, Subtype.ext (Prod.ext hg ?_)⟩
    apply Multiplicative.ext
    change d • m = n
    exact (nsmul_eq_mul d m).trans hm.symm

/-- The image of the Weil inclusion is open for the discrete-degree topology. -/
theorem localWeilFixedFieldInclusion_isOpen_range :
    IsOpen (Set.range (localWeilFixedFieldInclusion K H e)) := by
  change IsOpen ((localWeilFixedFieldInclusion K H e).toMonoidHom.range : Set (localWeilGroup K))
  rw [localWeilFixedFieldInclusion_range]
  have hH : IsOpen (H.field.toSubgroup : Set G) :=
    abstractFiniteClosedSubgroup_isOpen K (SeparableClosure K) H.field H.finite
  exact hH.preimage (localWeilToAbsolute K).continuous

/-- For a Galois finite fixed field, this is the kernel of the literal
restriction from the lower Weil group to the relative Galois group. -/
theorem localWeilFixedFieldInclusion_range_eq_ker
    [IsGalois K F] :
    (localWeilFixedFieldInclusion K H e).toMonoidHom.range =
      ((AlgEquiv.restrictNormalHom F).comp (localWeilToAbsolute K).toMonoidHom).ker := by
  let E := abstractFixedField K (SeparableClosure K) H.field
  have hfix : (AlgEquiv.restrictNormalHom E).ker = H.field.toSubgroup :=
    (IntermediateField.restrictNormalHom_ker E).trans
      (InfiniteGalois.fixingSubgroup_fixedField H.field)
  rw [localWeilFixedFieldInclusion_range, ← MonoidHom.comap_ker]
  exact congrArg (Subgroup.comap (localWeilToAbsolute K).toMonoidHom) hfix.symm


/-- The inclusion identifies the upper Weil group with its actual open image. -/
noncomputable def localWeilFixedFieldInclusionEquivRange :
    localWeilGroup F ≃ₜ* (localWeilFixedFieldInclusion K H e).toMonoidHom.range := by
  let f := localWeilFixedFieldInclusion K H e
  let R := f.toMonoidHom.range
  let er : localWeilGroup F ≃* R :=
    MonoidHom.ofInjective (f := f.toMonoidHom) (localWeilFixedFieldInclusion_injective K H e)
  let ea := FunctionField.fixedFieldAbsoluteGaloisEquivOfClosure K (SeparableClosure K) H e
  have heainv : Continuous ea.symm := ea.symm.continuous
  have hm (x : R) : localWeilToAbsolute K x.1 ∈ H.field.toSubgroup := by
    have hx : x.1 ∈ (localWeilFixedFieldInclusion K H e).toMonoidHom.range := x.property
    rw [localWeilFixedFieldInclusion_range K H e] at hx
    exact hx
  let q : R → H.field.toSubgroup := fun x => ⟨localWeilToAbsolute K x.1, hm x⟩
  have hq : Continuous q :=
    ((localWeilToAbsolute K).continuous.comp continuous_subtype_val).subtype_mk _
  have hg : Continuous (fun x : R => localWeilToAbsolute F (er.symm x)) := by
    apply (heainv.comp hq).congr
    intro x
    apply ea.injective
    calc
      _ = q x := ea.apply_symm_apply (q x)
      _ = ea (localWeilToAbsolute F (er.symm x)) := ?_
    apply Subtype.ext
    have hx := congrArg (fun y : R => localWeilToAbsolute K y.1) (er.apply_symm_apply x)
    change localFixedFieldAbsoluteInclusion K H e (localWeilToAbsolute F (er.symm x)) =
      localWeilToAbsolute K x.1 at hx
    exact hx.symm.trans
      (localFixedFieldAbsoluteInclusion_eq_subtype K H e (localWeilToAbsolute F (er.symm x)))
  let d : ℤ := H.residueDegree (localResidueDatum K)
  have hd : d ≠ 0 := Int.natCast_ne_zero.mpr (H.residueDegree (localResidueDatum K)).ne_zero
  have hn : Continuous (fun x : R => localWeilDegree F (er.symm x)) := by
    have hdiv : Continuous (fun n : Multiplicative ℤ => Multiplicative.ofAdd (n.toAdd / d)) :=
      continuous_of_discreteTopology
    apply (hdiv.comp ((localWeilDegree K).continuous.comp continuous_subtype_val)).congr
    intro x
    apply Multiplicative.ext
    have hx := congrArg (fun y : R => (localWeilDegree K y.1).toAdd) (er.apply_symm_apply x)
    change (localWeilDegree K (f (er.symm x))).toAdd = (localWeilDegree K x.1).toAdd at hx
    change (localWeilDegree K x.1).toAdd / d = (localWeilDegree F (er.symm x)).toAdd
    let n : ℤ := (localWeilDegree F (er.symm x)).toAdd
    have hmul : (localWeilDegree K (f (er.symm x))).toAdd = d * n :=
      (localWeilFixedFieldInclusion_degree K H e (er.symm x)).trans
        (nsmul_eq_mul _ n)
    exact (congrArg (fun a : ℤ => a / d) (hx.symm.trans hmul)).trans
      (Int.mul_ediv_cancel_left n hd)
  exact
    { toMulEquiv := er
      continuous_toFun := f.continuous.subtype_mk _
      continuous_invFun := (hg.prodMk hn).subtype_mk _ }

/-- Weil inclusion is an open embedding for the two Weil topologies. -/
theorem localWeilFixedFieldInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding (localWeilFixedFieldInclusion K H e) := by
  let er := localWeilFixedFieldInclusionEquivRange K H e
  have hOpen : IsOpen (((localWeilFixedFieldInclusion K H e).toMonoidHom.range :
      Subgroup (localWeilGroup K)) : Set (localWeilGroup K)) :=
    localWeilFixedFieldInclusion_isOpen_range K H e
  exact hOpen.isOpenEmbedding_subtypeVal.comp er.toHomeomorph.isOpenEmbedding

/-- The dense Weil group represents every coset of the open fixing subgroup. -/
theorem localWeilToAbsolute_fixingCoset_surjective (g : G) :
    ∃ w : localWeilGroup K,
      (QuotientGroup.mk (localWeilToAbsolute K w) : G ⧸ H.field.toSubgroup) =
        QuotientGroup.mk g := by
  let B := H.field.toSubgroup
  have hB : IsOpen (B : Set G) :=
    abstractFiniteClosedSubgroup_isOpen K (SeparableClosure K) H.field H.finite
  let V : Set G := g • (B : Set G)
  have hV : IsOpen V := hB.smul g
  have hg : g ∈ V := mem_leftCoset g B.one_mem
  obtain ⟨w, hy⟩ := (localWeilToAbsolute_denseRange K).exists_mem_open hV ⟨g, hg⟩
  refine ⟨w, QuotientGroup.eq.2 ?_⟩
  simpa only [mul_inv_rev, inv_inv] using B.inv_mem ((mem_leftCoset_iff g).1 hy)

/-- The open Weil image has index equal to the actual finite field degree. -/
theorem localWeilFixedFieldInclusion_index :
    (localWeilFixedFieldInclusion K H e).toMonoidHom.range.index = Module.finrank K F := by
  let h := (localWeilToAbsolute K).toMonoidHom
  let B := H.field.toSubgroup
  let A := B.comap h
  have hrel (x y : localWeilGroup K) :
      QuotientGroup.leftRel A x y ↔ QuotientGroup.leftRel B (h x) (h y) := by
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_comap, map_mul, map_inv, A]
  let f : localWeilGroup K ⧸ A → G ⧸ B :=
    Quotient.map' h fun x y => (hrel x y).mp
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      revert hab
      refine Quotient.inductionOn₂' a b ?_
      intro x y hxy
      apply Quotient.sound'
      apply (hrel x y).mpr
      exact Quotient.exact' hxy
    · refine Quotient.ind' fun x => ?_
      obtain ⟨w, hw⟩ := localWeilToAbsolute_fixingCoset_surjective K H x
      exact ⟨QuotientGroup.mk w, hw⟩
  calc
    (localWeilFixedFieldInclusion K H e).toMonoidHom.range.index = A.index := by
      rw [localWeilFixedFieldInclusion_range]
    _ = B.index := Nat.card_congr (Equiv.ofBijective f hf)
    _ = Module.finrank K F := by
      let E := abstractFixedField K (SeparableClosure K) H.field
      have hfix : E.fixingSubgroup = B := InfiniteGalois.fixingSubgroup_fixedField H.field
      exact (congrArg Subgroup.index hfix).symm.trans
        (IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K) E).symm


/-- Under the ordinary Weil reciprocity equivalences, finite inclusion and
the actual field norm give the same discrete degree. -/
theorem localWeilFixedFieldInclusion_reciprocity_norm_degree (x : Fˣ) :
    localWeilAbelianizationDegree K
      (TopologicalAbelianization.map (localWeilFixedFieldInclusion K H e)
        (localWeilReciprocity F x)) =
      localWeilAbelianizationDegree K (localWeilReciprocity K (normUnits K F x)) := by
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F) :=
    finiteExtensionSpectralValuation_hasExtension K F
  let hIntegralClosure : IsIntegralClosure 𝒪[F] 𝒪[K] F :=
    localCompleteDVF_integerRing_isIntegralClosure K F
  let a : TopologicalAbelianization (localWeilGroup F) := localWeilReciprocity F x
  have hs : ∃ w : localWeilGroup F, TopologicalAbelianization.mk (localWeilGroup F) w = a :=
    TopologicalAbelianization.surjective_mk (localWeilGroup F) a
  obtain ⟨w, hw⟩ := hs
  let f := localWeilFixedFieldInclusion K H e
  let d : ℕ := H.residueDegree (localResidueDatum K)
  have hx : (localWeilDegree F w).toAdd = valuationMap F (Additive.ofMul x) :=
    (congrArg (fun b : TopologicalAbelianization (localWeilGroup F) =>
      (localWeilAbelianizationDegree F b).toAdd) hw).trans
      (congrArg Multiplicative.toAdd (localWeilAbelianizationDegree_localWeilReciprocity F x))
  let residueRank : ℕ := @Module.finrank 𝓀[K] 𝓀[F] _ _
    (IsLocalRing.ResidueField.instModule (R := 𝒪[K]) (S := 𝒪[F]))
  have hd : d = residueRank := localResidueDatum_residueDegree_eq_residueFinrank K H
  have hv : valuationMap K (Additive.ofMul (normUnits K F x)) =
      (residueRank : ℤ) * valuationMap F (Additive.ofMul x) := by
    simpa only [valuationMap_apply] using
      (@v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K F _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure x)
  apply Multiplicative.ext
  calc
    _ = (localWeilAbelianizationDegree K (TopologicalAbelianization.map f
          (TopologicalAbelianization.mk (localWeilGroup F) w))).toAdd :=
      congrArg (fun b : TopologicalAbelianization (localWeilGroup F) =>
        (localWeilAbelianizationDegree K (TopologicalAbelianization.map f b)).toAdd) hw.symm
    _ = (localWeilDegree K (f w)).toAdd :=
      congrArg (fun b : TopologicalAbelianization (localWeilGroup K) =>
        (localWeilAbelianizationDegree K b).toAdd) (TopologicalAbelianization.map_apply_mk f w)
    _ = d • (localWeilDegree F w).toAdd := localWeilFixedFieldInclusion_degree K H e w
    _ = (residueRank : ℤ) * valuationMap F (Additive.ofMul x) := by
      rw [hx, hd, nsmul_eq_mul]
    _ = valuationMap K (Additive.ofMul (normUnits K F x)) := hv.symm
    _ = _ := congrArg Multiplicative.toAdd
      (localWeilAbelianizationDegree_localWeilReciprocity K (normUnits K F x)).symm

end LocalClassFieldTheory
