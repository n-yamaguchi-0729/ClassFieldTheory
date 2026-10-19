/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
The generic valuation-subring and exponential-order comparisons are also adapted from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_Repartitions.lean
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_adicValuation_isTrivialOn.lean
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mem_iff_ord_nonneg.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff.lean

Source-file correspondence is unconfirmed for:
Place_adicValuation_isRankOneDiscrete
Place_exists_ord_eq_one
Place_min_ord_le_ord_add
Place_ord_add_eq_of_lt
Place_ord_algebraMap
Place_ord_nonneg_of_mem
Place_ord_natCast
Place_ord_smul_of_ne_zero
Place_mem_of_ord_nonneg
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Ring.Subring.Pointwise
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Bezout

/-!
# Places and their normalized valuations

A place, its residue field and normalized order, the action of field automorphisms, and
the place associated with a height-one prime. Divisor and Picard constructions build on this API.
-/

section

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A proper principal valuation subring of `F` containing the image of the base field `K`. -/
structure Place where
  /-- The valuation subring defining the place. -/
  toValuationSubring : ValuationSubring F
  /-- Every scalar from the base field belongs to the valuation subring. -/
  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring
  /-- The valuation subring is a proper subring of the ambient field. -/
  ne_top' : toValuationSubring ≠ ⊤
  /-- The valuation subring is a principal ideal ring. -/
  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring

theorem _root_.ValuationSubring.not_isField_of_ne_top {A : ValuationSubring F} (hA : A ≠ ⊤) :
    ¬IsField A := by
  intro hf
  apply hA
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  by_cases hx : x ∈ A
  · exact hx
  · exfalso
    have hx0 : x ≠ 0 := fun h => hx (h ▸ A.zero_mem)
    have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have hxi0 : (⟨x⁻¹, hxi⟩ : A) ≠ 0 := by
      simp only [ne_eq, Subtype.ext_iff]
      exact inv_ne_zero hx0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel hxi0
    have hb' : x⁻¹ * (b : F) = 1 := by
      exact congrArg (Subtype.val) hb
    have hbx : (b : F) = x := ((inv_mul_eq_one₀ hx0).mp hb').symm
    exact hx (hbx ▸ b.2)

namespace Place

variable {K F}

theorem toValuationSubring_injective :
    Function.Injective (toValuationSubring (K := K) (F := F)) := by
  rintro ⟨a, _, _, _⟩ ⟨b, _, _, _⟩ (rfl : a = b)
  rfl
@[ext]
theorem ext {v w : Place K F} (h : v.toValuationSubring = w.toValuationSubring) : v = w :=
  toValuationSubring_injective h

variable (v : Place K F)

instance : IsPrincipalIdealRing v.toValuationSubring := v.isPrincipalIdealRing'

instance : IsDiscreteValuationRing v.toValuationSubring where
  not_a_field' := by
    rw [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact ValuationSubring.not_isField_of_ne_top F v.ne_top'

instance : Algebra K v.toValuationSubring :=
  ((algebraMap K F).codRestrict v.toValuationSubring.toSubring v.algebraMap_mem').toAlgebra
@[simp]
theorem coe_algebraMap (a : K) :
    (algebraMap K v.toValuationSubring a : F) = algebraMap K F a := rfl

instance : IsScalarTower K v.toValuationSubring F :=
  IsScalarTower.of_algebraMap_eq fun a => (v.coe_algebraMap a).symm

/-- The residue field of the valuation subring at the place. -/
abbrev ResidueField : Type _ := IsLocalRing.ResidueField v.toValuationSubring

/-- The degree of the residue field over the base field. -/
def deg : ℕ := Module.finrank K v.ResidueField

/-- The residue field at a place is a finite module over the base field. -/
class FiniteResidue : Prop where
  /-- Finiteness of the residue field as a module over the base field. -/
  finite : Module.Finite K v.ResidueField

/-- The maximal ideal of the discrete valuation ring, viewed as a height-one prime. -/
def heightOneSpectrum : HeightOneSpectrum v.toValuationSubring :=
  IsDiscreteValuationRing.maximalIdeal _
@[simp]
theorem heightOneSpectrum_asIdeal :
    v.heightOneSpectrum.asIdeal = IsLocalRing.maximalIdeal v.toValuationSubring := rfl

/-- The multiplicative discrete valuation associated with the place. -/
def adicValuation : Valuation F ℤᵐ⁰ := v.heightOneSpectrum.valuation F

theorem adicValuation_ne_zero {f : F} (hf : f ≠ 0) : v.adicValuation f ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr hf

theorem adicValuation_valuationSubring :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

theorem mem_iff_adicValuation_le_one {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring]
  exact Valuation.mem_valuationSubring_iff _ _

theorem adicValuation_coe (a : v.toValuationSubring) :
    v.adicValuation (a : F) = v.heightOneSpectrum.intValuation a := by
  exact v.heightOneSpectrum.valuation_of_algebraMap (K := F) a

theorem adicValuation_coe_eq_one_iff (a : v.toValuationSubring) :
    v.adicValuation (a : F) = 1 ↔ IsUnit a := by
  rw [v.adicValuation_coe, HeightOneSpectrum.intValuation_eq_one_iff, heightOneSpectrum_asIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem adicValuation_coe_irreducible {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.adicValuation (π : F) = exp (-1 : ℤ) := by
  rw [v.adicValuation_coe]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero
    (by rw [heightOneSpectrum_asIdeal, hπ.maximalIdeal_eq])

/-- The additive valuation order of an element, with order zero assigned to zero. -/
def ord (f : F) : ℤ := -(WithZero.log (v.adicValuation f))
@[simp]
theorem ord_zero : v.ord (0 : F) = 0 := by simp only [ord, map_zero, WithZero.log_zero, neg_zero]
@[simp]
theorem ord_one : v.ord (1 : F) = 0 := by simp only [ord, map_one, WithZero.log_one, neg_zero]

theorem adicValuation_eq_exp_neg_ord {f : F} (hf : f ≠ 0) :
    v.adicValuation f = exp (-v.ord f) := by
  unfold ord
  rw [neg_neg, exp_log (v.adicValuation_ne_zero hf)]

theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f * g) = v.ord f + v.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul (v.adicValuation_ne_zero hf) (v.adicValuation_ne_zero hg)]
  ring

theorem ord_inv (f : F) : v.ord f⁻¹ = -v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp only [inv_zero, ord_zero, neg_zero]
  · simp only [ord, map_inv₀, WithZero.log_inv, neg_neg]

theorem ord_coe_unit (u : v.toValuationSubringˣ) :
    v.ord ((u : v.toValuationSubring) : F) = 0 := by
  rw [ord, (v.adicValuation_coe_eq_one_iff _).mpr u.isUnit, WithZero.log_one, neg_zero]

theorem ord_coe_irreducible {π : v.toValuationSubring} (hπ : Irreducible π) :
    v.ord (π : F) = 1 := by
  rw [ord, v.adicValuation_coe_irreducible hπ, WithZero.log_exp, neg_neg]

theorem ord_zpow (f : F) (n : ℤ) : v.ord (f ^ n) = n * v.ord f := by
  simp only [ord, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem ord_unit_smul_zpow (u : v.toValuationSubringˣ) {π : v.toValuationSubring}
    (hπ : Irreducible π) (n : ℤ) :
    v.ord (((u : v.toValuationSubring) : F) * ((π : F) ^ n)) = n := by
  have hπF : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hu : ((u : v.toValuationSubring) : F) ≠ 0 :=
    fun h => u.ne_zero (Subtype.ext h)
  rw [v.ord_mul hu (zpow_ne_zero n hπF), v.ord_coe_unit u, zero_add,
    v.ord_zpow _ _, v.ord_coe_irreducible hπ, mul_one]

theorem exists_unit_mul_zpow {f : F} (hf : f ≠ 0) {π : v.toValuationSubring}
    (hπ : Irreducible π) :
    ∃ u : v.toValuationSubringˣ,
      f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (v.ord f)) := by
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := F) hπ hf
  rw [Units.smul_def, Algebra.smul_def] at hu
  have hcoe : algebraMap v.toValuationSubring F (u : v.toValuationSubring)
      = ((u : v.toValuationSubring) : F) := rfl
  have hcoe' : algebraMap v.toValuationSubring F π = (π : F) := rfl
  rw [hcoe, hcoe'] at hu
  have hn : v.ord f = n := by rw [hu]; exact v.ord_unit_smul_zpow u hπ n
  exact ⟨u, by rw [hn, hu]⟩

end Place

namespace Place

open scoped Pointwise

variable {K F}
variable (σ : F ≃ₐ[K] F)

/-- Restrict a field automorphism to the corresponding transported valuation subring. -/
def smulRingEquiv (A : ValuationSubring F) : A ≃+* (σ • A : ValuationSubring F) where
  toFun x := ⟨σ x, by
    simpa only [AlgEquiv.smul_def] using
      ValuationSubring.smul_mem_pointwise_smul σ (x : F) A x.2⟩
  invFun y := ⟨σ.symm y, by
    have := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := σ)
      (S := A) (x := (y : F))).mp y.2
    simpa only [AlgEquiv.smul_def, AlgEquiv.aut_inv] using this⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv y := Subtype.ext (σ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul σ (x : F) (y : F))
  map_add' x y := Subtype.ext (map_add σ (x : F) (y : F))
@[simp]
theorem coe_smulRingEquiv_apply (A : ValuationSubring F) (x : A) :
    ((smulRingEquiv σ A x : (σ • A : ValuationSubring F)) : F) = σ x := rfl

theorem _root_.ValuationSubring.pointwise_smul_top :
    σ • (⊤ : ValuationSubring F) = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => ValuationSubring.mem_top _⟩

instance : SMul (F ≃ₐ[K] F) (Place K F) where
  smul σ v :=
    { toValuationSubring := σ • v.toValuationSubring
      algebraMap_mem' := fun a => by
        have h := ValuationSubring.smul_mem_pointwise_smul σ (algebraMap K F a)
          v.toValuationSubring (v.algebraMap_mem' a)
        rwa [AlgEquiv.smul_def, σ.commutes] at h
      ne_top' := fun h => v.ne_top' <| by
        have := congrArg (σ⁻¹ • ·) h
        simpa only [inv_smul_smul, ValuationSubring.pointwise_smul_top] using this
      isPrincipalIdealRing' :=
        IsPrincipalIdealRing.of_surjective
          (smulRingEquiv σ v.toValuationSubring : _ ≃+* _)
          (smulRingEquiv σ v.toValuationSubring).surjective }

variable (v : Place K F)

@[simp]
theorem smul_toValuationSubring : (σ • v).toValuationSubring = σ • v.toValuationSubring := rfl

instance : MulAction (F ≃ₐ[K] F) (Place K F) where
  one_smul v := by
    ext1
    rw [smul_toValuationSubring, one_smul]
  mul_smul σ τ v := by
    ext1
    simp only [smul_toValuationSubring]
    rw [mul_smul]

theorem ord_smul (f : F) : (σ • v).ord (σ f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, ord_zero, ord_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  set n := v.ord f with hn
  set e := smulRingEquiv σ v.toValuationSubring with he
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (σ • v).toValuationSubring) : F)
      = σ ((u : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((e π : (σ • v).toValuationSubring) : F) = σ (π : F) := rfl
  have key : σ f = ((hu'.unit : (σ • v).toValuationSubring) : F)
      * (((e π : (σ • v).toValuationSubring) : F) ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [key, (σ • v).ord_unit_smul_zpow hu'.unit hπ' n]

/-- The residue-field algebra equivalence induced by a field automorphism of a place. -/
def smulResidueAlgEquiv : v.ResidueField ≃ₐ[K] (σ • v).ResidueField :=
  AlgEquiv.ofRingEquiv (f := IsLocalRing.ResidueField.mapEquiv
      (smulRingEquiv σ v.toValuationSubring)) <| fun a => by
    have h3 : (smulRingEquiv σ v.toValuationSubring) (algebraMap K v.toValuationSubring a)
        = algebraMap K (σ • v).toValuationSubring a := by
      ext
      rw [coe_smulRingEquiv_apply, coe_algebraMap, σ.commutes]
      rfl
    change IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg _ h3
@[simp]
theorem deg_smul : (σ • v).deg = v.deg :=
  ((smulResidueAlgEquiv σ v).toLinearEquiv.finrank_eq).symm

end Place

namespace Place

variable {K F}
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

open IsDedekindDomain.HeightOneSpectrum in
theorem isPrincipalIdealRing_valuationSubring (w : HeightOneSpectrum R) :
    IsPrincipalIdealRing ((w.valuation F).valuationSubring) := by
  rw [show (w.valuation F).valuationSubring = valuationSubringAtPrime F w from
    (valuationSubringAtPrime_eq_valuationSubring (K := F) w).symm]
  infer_instance

open IsDedekindDomain.HeightOneSpectrum in
/-- Construct a place from the prime-adic valuation of a height-one prime. -/
def ofHeightOneSpectrum [Algebra K R] [IsScalarTower K R F] (w : HeightOneSpectrum R) :
    Place K F where
  toValuationSubring := (w.valuation F).valuationSubring
  algebraMap_mem' := fun a => by
    rw [Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply K R F]
    exact w.valuation_le_one (algebraMap K R a)
  ne_top' := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := isPrincipalIdealRing_valuationSubring w
@[simp]
theorem ofHeightOneSpectrum_toValuationSubring [Algebra K R] [IsScalarTower K R F]
    (w : HeightOneSpectrum R) :
    (ofHeightOneSpectrum (K := K) w).toValuationSubring = (w.valuation F).valuationSubring :=
  rfl

end Place

end AlgebraicCurve

end

end

namespace AlgebraicCurve.Place

open IsDedekindDomain WithZero IsLocalRing

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem adicValuation_isRankOneDiscrete : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

theorem adicValuation_isTrivialOn : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one.mp (v.algebraMap_mem' a)

theorem exists_ord_eq_one : ∃ t : F, v.ord t = 1 :=
  let ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  ⟨π, v.ord_coe_irreducible hπ⟩

theorem min_ord_le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  have hmax : v.adicValuation (f + g) ≤ max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add _ _ _
  unfold Place.ord
  rcases le_max_iff.mp hmax with hle | hle
  · have := (WithZero.log_le_log hfg' hf').mpr hle
    omega
  · have := (WithZero.log_le_log hfg' hg').mpr hle
    omega

theorem ord_add_eq_of_lt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hval : v.adicValuation g < v.adicValuation f := by
    have hf' := v.adicValuation_ne_zero hf
    have hg' := v.adicValuation_ne_zero hg
    rw [← WithZero.log_lt_log hg' hf']
    unfold Place.ord at h
    omega
  unfold Place.ord
  rw [Valuation.map_add_eq_of_lt_left _ hval]

theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) :=
      (isUnit_iff_ne_zero.mpr hc).map _
    have hval : v.adicValuation (algebraMap K F c) = 1 := by
      rw [← v.coe_algebraMap]
      exact (v.adicValuation_coe_eq_one_iff _).mpr hu
    simp only [ord, hval, log_one, neg_zero]

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [v.ord_zero]
  · have hle : v.adicValuation f ≤ 1 := (v.mem_iff_adicValuation_le_one).mp hf
    rw [v.adicValuation_eq_exp_neg_ord hf0, ← exp_zero, exp_le_exp] at hle
    omega

theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  rw [v.mem_iff_adicValuation_le_one, v.adicValuation_eq_exp_neg_ord hf,
    ← exp_zero, exp_le_exp]
  omega

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring :=
  (v.mem_iff_ord_nonneg hf).mpr h


/-- Nonnegative order implies integrality, including the zero element. -/
theorem mem_toValuationSubring_of_ord_nonneg {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact v.mem_of_ord_nonneg hf h


theorem mk_mem_maximalIdeal_iff_eq_zero_or_ord_pos {f : F} (hf : f ∈ v.toValuationSubring) :
    (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring
      ↔ f = 0 ∨ 0 < v.ord f := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hu
    rcases eq_or_ne f 0 with rfl | hf0
    · exact Or.inl rfl
    · refine Or.inr ?_
      rcases lt_or_eq_of_le (v.ord_nonneg_of_mem hf) with h | h
      · exact h
      · exfalso
        apply hu
        rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
        change v.adicValuation f = 1
        rw [v.adicValuation_eq_exp_neg_ord hf0, ← h, neg_zero, WithZero.exp_zero]
  · intro h hu
    have hne : f ≠ 0 := fun h0 => hu.ne_zero (Subtype.ext h0)
    have h0 : v.ord f = 0 := by
      obtain ⟨u, hu'⟩ := hu
      have hcoe : f = ((u : v.toValuationSubring) : F) := by rw [hu']
      rw [hcoe]
      exact v.ord_coe_unit u
    rcases h with rfl | hpos
    · exact hne rfl
    · omega

theorem ord_natCast (n : ℕ) : v.ord (n : F) = 0 := by
  rw [show (n : F) = algebraMap K F n from (map_natCast (algebraMap K F) n).symm]
  exact v.ord_algebraMap n

theorem ord_smul_of_ne_zero {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [smul_zero]
  · have halg : algebraMap K F c ≠ 0 :=
      fun h => hc ((algebraMap K F).injective (by rw [h, map_zero]))
    rw [Algebra.smul_def, v.ord_mul halg hx0, v.ord_algebraMap, zero_add]

end AlgebraicCurve.Place
