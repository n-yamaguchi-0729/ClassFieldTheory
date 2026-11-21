/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.CyclicGeneratorLift
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.FiniteUnramifiedField
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.NormRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction

/-! # Unramification of a cyclic local extension after diagonal base change -/

@[expose] public section

open scoped ValuativeRel

namespace LocalClassFieldTheory

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField RamificationTheory

noncomputable section

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]

/-- The unramified factor has the degree of the given finite local extension. -/
abbrev cyclicLocalUnramifiedFactor : IntermediateField K (SeparableClosure K) :=
  localFiniteUnramifiedField K (Module.finrank K L) Module.finrank_pos

/-- The actual compositum of the finite extension and its unramified factor. -/
abbrev cyclicLocalUnramifiedCompositum : IntermediateField K (SeparableClosure K) :=
  L ⊔ cyclicLocalUnramifiedFactor K L

local notation "d" => Module.finrank K L
local notation "U" => cyclicLocalUnramifiedFactor K L
local notation "C" => cyclicLocalUnramifiedCompositum K L

local instance cyclicCompositumFinite : FiniteDimensional K C :=
  IntermediateField.finiteDimensional_sup L U

variable [IsGalois K L]

local instance cyclicCompositumGalois : IsGalois K C :=
  { to_isSeparable := inferInstance, to_normal := inferInstance }

/-- Restriction from the actual compositum to its unramified factor. -/
noncomputable def cyclicLocalUnramifiedRestriction : Gal(C/K) →* Gal(U/K) :=
  intermediateFieldRestrictNormalHom U C le_sup_right

/-- Restriction from the actual compositum to the given finite extension. -/
noncomputable def cyclicLocalOriginalRestriction : Gal(C/K) →* Gal(L/K) :=
  intermediateFieldRestrictNormalHom L C le_sup_left

/-- The diagonal subgroup projects isomorphically onto the unramified factor
and surjectively onto the original cyclic extension. -/
theorem exists_cyclicLocalUnramifiedDiagonal [IsCyclic Gal(L/K)] :
    ∃ H : Subgroup Gal(C/K),
      H.map (cyclicLocalOriginalRestriction K L) = ⊤ ∧
      Function.Bijective ((cyclicLocalUnramifiedRestriction K L).comp H.subtype) ∧
      Module.finrank (IntermediateField.fixedField H) C = d := by
  let : Algebra U C := ((U).inclusion (show U ≤ C from le_sup_right)).toRingHom.toAlgebra
  let : IsScalarTower K U C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra L C := (L.inclusion (show L ≤ C from le_sup_left)).toRingHom.toAlgebra
  let : IsScalarTower K L C := IsScalarTower.of_algebraMap_eq' rfl
  let a := cyclicLocalUnramifiedRestriction K L
  let b := cyclicLocalOriginalRestriction K L
  have ha : Function.Surjective a := AlgEquiv.restrictNormalHom_surjective (E := C)
  have hb : Function.Surjective b := AlgEquiv.restrictNormalHom_surjective (E := C)
  have hab : Function.Injective (a.prod b) :=
    intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq K U L C
      le_sup_right le_sup_left (sup_comm U L)
  let φ := arithmeticFrobeniusOfUnramifiedValuation K U
  have hφ : Subgroup.zpowers φ = ⊤ :=
    arithmeticFrobeniusOfUnramifiedValuation_zpowers_eq_top K U
  have hφorder : orderOf φ = d :=
    localFiniteUnramifiedField_arithmeticFrobenius_order K d Module.finrank_pos
  obtain ⟨τ, hτ⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic Gal(L/K))
  obtain ⟨σ, hσa, hσb⟩ := ClassFieldTheory.exists_diagonal_cyclicGenerator a ha b hb φ hφ τ hτ
  have hbOrder : orderOf (b σ) = d :=
    (orderOf_eq_card_of_zpowers_eq_top hσb).trans (IsGalois.card_aut_eq_finrank K L)
  have hσorder : orderOf σ = d := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      apply hab
      apply Prod.ext
      · change a (σ ^ d) = a 1
        rw [map_pow, map_one, hσa, ← hφorder, pow_orderOf_eq_one]
      · change b (σ ^ d) = b 1
        rw [map_pow, map_one, ← hbOrder, pow_orderOf_eq_one]
    · rw [← hφorder, ← hσa]
      exact orderOf_map_dvd a σ
  let H := Subgroup.zpowers σ
  refine ⟨H, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact (MonoidHom.map_zpowers b σ).trans hσb
  · apply (injective_iff_map_eq_one _).mpr
    intro g hg
    obtain ⟨n, hn⟩ := g.property
    apply Subtype.ext
    change (g : Gal(C/K)) = 1
    rw [← hn, ← orderOf_dvd_iff_zpow_eq_one, hσorder, ← hφorder]
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    have h := congrArg a hn
    rw [map_zpow, hσa] at h
    exact h.trans hg
  · intro y
    have hy : y ∈ Subgroup.zpowers φ := hφ.symm ▸ Subgroup.mem_top y
    obtain ⟨n, hn⟩ := hy
    refine ⟨⟨σ ^ n, ⟨n, rfl⟩⟩, ?_⟩
    change a (σ ^ n) = y
    rw [map_zpow, hσa]
    exact hn
  · change Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) C = d
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hσorder]

local instance cyclicCompositumNormedField : NontriviallyNormedField C :=
  finiteExtensionSpectralNormedField K C

local instance cyclicCompositumValuativeRel : ValuativeRel C :=
  finiteExtensionSpectralValuativeRel K C

local instance cyclicCompositumLocalField : IsNonarchimedeanLocalField C :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K C

/-- The diagonal fixed field as an intermediate field of the original separable closure. -/
abbrev cyclicLocalDiagonalField (H : Subgroup Gal(C/K)) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.lift (IntermediateField.fixedField H)

omit [IsGalois K L] in
/-- The lifted diagonal field lies in the actual compositum. -/
theorem cyclicLocalDiagonalField_le (H : Subgroup Gal(C/K)) :
    cyclicLocalDiagonalField K L H ≤ C :=
  IntermediateField.lift_le (F := C) (IntermediateField.fixedField H)

variable (H : Subgroup (Gal(↥(cyclicLocalUnramifiedCompositum K L)/K)))

include H

/-- Coefficient inclusion from the lifted diagonal field into the actual compositum. -/
@[instance_reducible]
noncomputable def cyclicLocalDiagonalAlgebra : Algebra (cyclicLocalDiagonalField K L H) C :=
  (IntermediateField.inclusion (cyclicLocalDiagonalField_le K L H)).toRingHom.toAlgebra

attribute [local instance] cyclicLocalDiagonalAlgebra

local instance cyclicDiagonalScalarTower : IsScalarTower K (cyclicLocalDiagonalField K L H) C :=
  IsScalarTower.of_algebraMap_eq' (R := K) (S := (cyclicLocalDiagonalField K L H)) (A := C) rfl

local instance cyclicDiagonalBaseFinite : FiniteDimensional K (cyclicLocalDiagonalField K L H) := by
  let e : (IntermediateField.fixedField H) ≃ₐ[K] cyclicLocalDiagonalField K L H :=
    IntermediateField.liftAlgEquiv (E := C) (IntermediateField.fixedField H)
  exact e.toLinearEquiv.finiteDimensional

local instance cyclicDiagonalBaseNormedField :
    NontriviallyNormedField (cyclicLocalDiagonalField K L H) :=
  finiteExtensionSpectralNormedField K (cyclicLocalDiagonalField K L H)

local instance cyclicDiagonalBaseValuativeRel : ValuativeRel (cyclicLocalDiagonalField K L H) :=
  finiteExtensionSpectralValuativeRel K (cyclicLocalDiagonalField K L H)

local instance cyclicDiagonalBaseLocalField :
    IsNonarchimedeanLocalField (cyclicLocalDiagonalField K L H) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K (cyclicLocalDiagonalField K L H)

local instance cyclicDiagonalRelativeFinite :
    FiniteDimensional (cyclicLocalDiagonalField K L H) C :=
  FiniteDimensional.right K (cyclicLocalDiagonalField K L H) C

omit [IsGalois K L] in
/-- The field isomorphism for the lift retains the original elements in the compositum. -/
theorem cyclicLocalDiagonalLift_commutes (x : (IntermediateField.fixedField H)) :
    algebraMap (cyclicLocalDiagonalField K L H) C
      (IntermediateField.liftAlgEquiv (E := C) (IntermediateField.fixedField H) x) =
      algebraMap (IntermediateField.fixedField H) C x := rfl

local instance cyclicDiagonalRelativeGalois : IsGalois (cyclicLocalDiagonalField K L H) C :=
  IsGalois.tower_top_of_isGalois K (cyclicLocalDiagonalField K L H) C

omit [IsGalois K L] in
/-- An automorphism in the diagonal subgroup fixes the lifted diagonal field. -/
theorem cyclicLocalDiagonalSubgroup_fixes (σ : Gal(C/K)) (hσ : σ ∈ H)
    (x : cyclicLocalDiagonalField K L H) :
    σ (algebraMap (cyclicLocalDiagonalField K L H) C x) =
      algebraMap (cyclicLocalDiagonalField K L H) C x := by
  let e : (IntermediateField.fixedField H) ≃ₐ[K] cyclicLocalDiagonalField K L H :=
    IntermediateField.liftAlgEquiv (E := C) (IntermediateField.fixedField H)
  obtain ⟨y, rfl⟩ := e.surjective x
  rw [cyclicLocalDiagonalLift_commutes K L H]
  have h : σ ∈ (IntermediateField.fixedField H).fixingSubgroup :=
    (IntermediateField.fixingSubgroup_fixedField H).symm ▸ hσ
  exact (IntermediateField.mem_fixingSubgroup_iff (IntermediateField.fixedField H) σ).mp h
    (y : C) y.property

omit [IsGalois K L] in
/-- A compositum automorphism fixing the lifted field restricts into the diagonal subgroup. -/
theorem cyclicLocalDiagonalSubgroup_mem (σ : Gal(C/(cyclicLocalDiagonalField K L H))) :
    σ.restrictScalars K ∈ H := by
  have h : σ.restrictScalars K ∈ (IntermediateField.fixedField H).fixingSubgroup := by
    apply (IntermediateField.mem_fixingSubgroup_iff (IntermediateField.fixedField H)
      (σ.restrictScalars K)).mpr
    intro x hx
    let y : (IntermediateField.fixedField H) := ⟨x, hx⟩
    let e : (IntermediateField.fixedField H) ≃ₐ[K] cyclicLocalDiagonalField K L H :=
      IntermediateField.liftAlgEquiv (E := C) (IntermediateField.fixedField H)
    have hy := σ.commutes (e y)
    rw [cyclicLocalDiagonalLift_commutes K L H] at hy
    exact hy
  exact (congrArg (fun S : Subgroup Gal(C/K) => σ.restrictScalars K ∈ S)
    (IntermediateField.fixingSubgroup_fixedField H)).mp h

/-- The subgroup of the compositum and the Galois group over the lifted
fixed field act identically. -/
noncomputable def cyclicLocalDiagonalSubgroupEquiv :
    H ≃* Gal(C/(cyclicLocalDiagonalField K L H)) where
  toFun σ :=
    { toRingEquiv := σ.val.toRingEquiv
      commutes' := cyclicLocalDiagonalSubgroup_fixes K L H σ.val σ.property }
  invFun σ := ⟨σ.restrictScalars K, cyclicLocalDiagonalSubgroup_mem K L H σ⟩
  left_inv _ := Subtype.ext (AlgEquiv.ext fun _ => rfl)
  right_inv _ := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

omit [IsGalois K L] in
theorem cyclicLocalDiagonalSubgroupEquiv_restrictScalars (σ : H) :
    (cyclicLocalDiagonalSubgroupEquiv K L H σ).restrictScalars K = σ.val :=
  congrArg Subtype.val ((cyclicLocalDiagonalSubgroupEquiv K L H).symm_apply_apply σ)

/-- Lifting the fixed subfield retains the relative extension degree. -/
theorem cyclicLocalDiagonalField_relative_finrank :
    Module.finrank (cyclicLocalDiagonalField K L H) C =
      Module.finrank (IntermediateField.fixedField H) C := by
  rw [← IsGalois.card_aut_eq_finrank (cyclicLocalDiagonalField K L H) C,
    IntermediateField.finrank_fixedField_eq_card H]
  exact (Nat.card_congr (cyclicLocalDiagonalSubgroupEquiv K L H).toEquiv).symm

/-- Literal restriction gives the relative Galois isomorphism with the original extension. -/
noncomputable def cyclicLocalDiagonalGaloisEquiv
    (hH : H.map (cyclicLocalOriginalRestriction K L) = (⊤ : Subgroup Gal(L/K)))
    (hdegree : Module.finrank (IntermediateField.fixedField H) C = d) :
    Gal(C/(cyclicLocalDiagonalField K L H)) ≃* Gal(L/K) := by
  let f : Gal(C/(cyclicLocalDiagonalField K L H)) →* Gal(L/K) :=
    (cyclicLocalOriginalRestriction K L).comp (AlgEquiv.restrictScalarsHom K)
  have hsurj : Function.Surjective f := by
    intro σ
    have hσ : σ ∈ H.map (cyclicLocalOriginalRestriction K L) := hH.symm ▸ Subgroup.mem_top σ
    obtain ⟨τ, hτ, hrestrict⟩ := hσ
    refine ⟨cyclicLocalDiagonalSubgroupEquiv K L H ⟨τ, hτ⟩, ?_⟩
    change cyclicLocalOriginalRestriction K L
      ((cyclicLocalDiagonalSubgroupEquiv K L H ⟨τ, hτ⟩).restrictScalars K) = σ
    rw [cyclicLocalDiagonalSubgroupEquiv_restrictScalars]
    exact hrestrict
  have hcard : Nat.card Gal(C/(cyclicLocalDiagonalField K L H)) = Nat.card Gal(L/K) := by
    rw [IsGalois.card_aut_eq_finrank (cyclicLocalDiagonalField K L H) C,
      IsGalois.card_aut_eq_finrank K L,
      cyclicLocalDiagonalField_relative_finrank K L H, hdegree]
  exact MulEquiv.ofBijective f (hsurj.bijective_of_nat_card_le hcard.le)

theorem cyclicLocalDiagonalGaloisEquiv_apply
    (hH : H.map (cyclicLocalOriginalRestriction K L) = (⊤ : Subgroup Gal(L/K)))
    (hdegree : Module.finrank (IntermediateField.fixedField H) C = d)
    (σ : Gal(C/(cyclicLocalDiagonalField K L H))) :
    cyclicLocalDiagonalGaloisEquiv K L H hH hdegree σ =
      cyclicLocalOriginalRestriction K L (σ.restrictScalars K) := rfl

local instance cyclicDiagonalValuationExtension :
    Valuation.HasExtension (ValuativeRel.valuation (cyclicLocalDiagonalField K L H))
      (ValuativeRel.valuation C) :=
  finiteExtensionSpectralValuation_hasExtension_of_tower K (cyclicLocalDiagonalField K L H) C

local instance cyclicDiagonalBaseValuationExtension :
    Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation (cyclicLocalDiagonalField K L H)) :=
  finiteExtensionSpectralValuation_hasExtension K (cyclicLocalDiagonalField K L H)

local instance cyclicDiagonalIntegerRingFinite :
    Module.Finite 𝒪[cyclicLocalDiagonalField K L H] 𝒪[C] := by
  let : Algebra.IsSeparable (cyclicLocalDiagonalField K L H) C :=
    (cyclicDiagonalRelativeGalois K L H).to_isSeparable
  exact localCompleteDVF_integerRing_moduleFinite (cyclicLocalDiagonalField K L H) C

private theorem cyclicLocalUnramifiedDiagonal_ramificationIdx_eq_one
    (hH : Function.Injective ((cyclicLocalUnramifiedRestriction K L).comp H.subtype)) :
    (𝓂[C] : Ideal 𝒪[C]).ramificationIdx 𝒪[cyclicLocalDiagonalField K L H] = 1 := by
  let : Algebra U C := ((U).inclusion (show U ≤ C from le_sup_right)).toRingHom.toAlgebra
  let : IsScalarTower K U C := IsScalarTower.of_algebraMap_eq' rfl
  let : Valuation.HasExtension (ValuativeRel.valuation U) (ValuativeRel.valuation C) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower K U C
  let : Algebra.IsSeparable (cyclicLocalDiagonalField K L H) C :=
    (cyclicDiagonalRelativeGalois K L H).to_isSeparable
  let : IsIntegralClosure 𝒪[C] 𝒪[cyclicLocalDiagonalField K L H] C :=
    localCompleteDVF_integerRing_isIntegralClosure (cyclicLocalDiagonalField K L H) C
  let r := galoisGroupResidueAlgEquivHomOfIsIntegralClosure (cyclicLocalDiagonalField K L H) C
  have hker : r.ker = (⊥ : Subgroup Gal(C/(cyclicLocalDiagonalField K L H))) := by
    refine le_antisymm ?_ bot_le
    intro σ hσ
    let σK : Gal(C/K) := σ.restrictScalars K
    have hm : σK ∈ H := cyclicLocalDiagonalSubgroup_mem K L H σ
    have hres : r σ = 1 := MonoidHom.mem_ker.mp hσ
    have hU : σK.restrictNormal U = 1 := by
      let ρ := galoisGroupResidueAlgEquivHomOfIsIntegralClosure K U
      have hi : Function.Injective ρ :=
        galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K U
      have hρ : ρ (σK.restrictNormal U) = 1 := by
        refine DFunLike.ext _ _ (fun (x : 𝓀[U]) => ?_)
        let f := residueFieldMapOfValuationExtension U C
        apply f.injective
        have h := galoisGroupResidue_restrictNormal_commutes K
          (cyclicLocalDiagonalField K L H) U C σ x
        change f (ρ (σK.restrictNormal U) x) = r σ (f x) at h
        exact h.trans (congrArg (fun τ => τ (f x)) hres)
      exact hi (hρ.trans (map_one ρ).symm)
    have hσK : σK = 1 := by
      have h : (⟨σK, hm⟩ : H) = 1 := hH (by
        change σK.restrictNormal U = cyclicLocalUnramifiedRestriction K L 1
        rw [map_one]
        exact hU)
      exact congrArg Subtype.val h
    have h1 : σ = 1 := AlgEquiv.restrictScalars_injective K hσK
    exact Subgroup.mem_bot.mpr h1
  have hcard : Nat.card r.ker =
      (𝓂[C] : Ideal 𝒪[C]).ramificationIdx 𝒪[cyclicLocalDiagonalField K L H] :=
    galoisGroupResidueAlgEquivHomOfIsIntegralClosure_ker_card_eq_ramificationIdx
      (cyclicLocalDiagonalField K L H) C
  have hone : Nat.card r.ker = 1 :=
    (congrArg (fun S : Subgroup Gal(C/(cyclicLocalDiagonalField K L H)) => Nat.card S)
      hker).trans Subgroup.card_bot
  exact hcard.symm.trans hone

/-- The compositum over the diagonal fixed field is unramified for the
canonical valuations on both actual fields. -/
theorem cyclicLocalUnramifiedDiagonal_isUnramified
    (hH : Function.Injective ((cyclicLocalUnramifiedRestriction K L).comp H.subtype)) :
    IsUnramifiedValuedExtension (cyclicLocalDiagonalField K L H) C := by
  exact ⟨cyclicLocalUnramifiedDiagonal_ramificationIdx_eq_one K L H hH⟩

variable [IsCyclic Gal(L/K)]

local instance cyclicOriginalAbelian : IsAbelianGalois K L :=
  IsAbelianGalois.of_isCyclic K L

/-- The restriction isomorphism makes the relative extension abelian Galois. -/
theorem cyclicLocalDiagonalRelative_isAbelianGalois
    (e : Gal(C/(cyclicLocalDiagonalField K L H)) ≃* Gal(L/K)) :
    IsAbelianGalois (cyclicLocalDiagonalField K L H) C :=
  { toIsGalois := inferInstance, toIsMulCommutative := e.symm.surjective.isMulCommutative }

/-- Norm reciprocity across the actual lifted diagonal field is computed by literal restriction. -/
theorem cyclicLocalDiagonalArtin_norm
    (hH : H.map (cyclicLocalOriginalRestriction K L) = (⊤ : Subgroup Gal(L/K)))
    (hdegree : Module.finrank (IntermediateField.fixedField H) C = d)
    (b : (cyclicLocalDiagonalField K L H)ˣ) :
    let e := cyclicLocalDiagonalGaloisEquiv K L H hH hdegree
    let : IsAbelianGalois (cyclicLocalDiagonalField K L H) C :=
      cyclicLocalDiagonalRelative_isAbelianGalois K L H e
    abelianLocalArtinMap K L (normUnits K (cyclicLocalDiagonalField K L H) b) =
      e (abelianLocalArtinMap (cyclicLocalDiagonalField K L H) C b) := by
  intro e hAbelian
  let : Algebra L C := (L.inclusion (show L ≤ C from le_sup_left)).toRingHom.toAlgebra
  let : IsScalarTower K L C := IsScalarTower.of_algebraMap_eq' rfl
  have h := LocalClassFieldTheory.abelianLocalArtinMonoidHom_norm_restriction K
    (cyclicLocalDiagonalField K L H) L C
  simp only [← LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom] at h
  exact (DFunLike.congr_fun h b).symm

/-- Every original finite Artin symbol is realized by an actual norm from the
lifted diagonal field, with the specified relative Artin value. -/
theorem exists_cyclicLocalDiagonalArtinNorm
    (hH : H.map (cyclicLocalOriginalRestriction K L) = (⊤ : Subgroup Gal(L/K)))
    (hdegree : Module.finrank (IntermediateField.fixedField H) C = d) (σ : Gal(L/K)) :
    let e := cyclicLocalDiagonalGaloisEquiv K L H hH hdegree
    let : IsAbelianGalois (cyclicLocalDiagonalField K L H) C :=
      cyclicLocalDiagonalRelative_isAbelianGalois K L H e
    ∃ b : (cyclicLocalDiagonalField K L H)ˣ,
      abelianLocalArtinMap K L (normUnits K (cyclicLocalDiagonalField K L H) b) = σ ∧
      abelianLocalArtinMap (cyclicLocalDiagonalField K L H) C b = e.symm σ := by
  intro e hAbelian
  obtain ⟨b, hb⟩ := abelianLocalArtinMap_surjective
    (cyclicLocalDiagonalField K L H) C (e.symm σ)
  refine ⟨b, ?_, hb⟩
  have h := cyclicLocalDiagonalArtin_norm K L H hH hdegree b
  change abelianLocalArtinMap K L (normUnits K (cyclicLocalDiagonalField K L H) b) =
      e (abelianLocalArtinMap (cyclicLocalDiagonalField K L H) C b) at h
  exact h.trans ((congrArg e hb).trans (e.apply_symm_apply σ))

end

end LocalClassFieldTheory
