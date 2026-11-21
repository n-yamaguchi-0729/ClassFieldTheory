/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionTransport
public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FiniteGlobalInvariantLift
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassSecondInequality
public import Nyll.GaloisCohomology.Cyclic.IntegralH2EquivariantEquivalence

/-! # The normalized fundamental class on the original integral idèle-class cohomology -/

@[expose] public section

open ClassFieldTheory CategoryTheory NumberField
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

universe u v

section SmallFieldInstances

variable (T : Type u) [Field T] [Small.{0} T]

/-- The semiring obtained by shrinking agrees with the semiring of the shrunk field. -/
theorem shrinkSemiring_eq_fieldSemiring :
    (Shrink.instSemiring (α := T) : Semiring (Shrink T : Type)) =
      ((inferInstance : Field (Shrink T : Type))).toSemifield.toCommSemiring.toSemiring :=
  rfl

/-- The commutative semiring obtained by shrinking agrees with the field projection. -/
theorem shrinkCommSemiring_eq_fieldCommSemiring :
    (Shrink.instCommSemiring (α := T) : CommSemiring (Shrink T : Type)) =
      ((inferInstance : Field (Shrink T : Type))).toSemifield.toCommSemiring :=
  rfl

attribute [local instance] HasseArf.shrinkAlgebra in
/-- The canonical small field extension is Galois whenever the original extension is Galois. -/
theorem shrinkNumberField_isGalois (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Small.{0} K] [Small.{0} L] [IsGalois K L] :
    IsGalois (Shrink K : Type) (Shrink L : Type) :=
  IsGalois.of_equiv_equiv (f := (Shrink.ringEquiv K).symm) (g := (Shrink.ringEquiv L).symm)
    (HasseArf.shrinkAlgebra_commutes K L)

end SmallFieldInstances

variable (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local notation "H" =>
  IntegralGroupCohomology.Universe.cohomology (standardIdeleClassRep K L) 2
/-- The lifted standard idèle class representation over the native cohomology ring. -/
abbrev globalFundamentalNativeRep :
    Rep.{v} (ULift.{v} ℤ) (ULift.{v} Gal(L/K)) :=
  (IntegralGroupCohomology.Universe.nativeFunctor.{v, v} (Gal(L/K))).obj
    (standardIdeleClassRep K L)

local notation "NativeRep" => globalFundamentalNativeRep K L

attribute [local instance] ClassFieldTheory.numberField_small ClassFieldTheory.numberField_shrink
attribute [local instance] HasseArf.shrinkAlgebra HasseArf.shrink_finiteDimensional
attribute [local instance] shrinkNumberField_isGalois

local notation "K₀" => (Shrink K : Type)
local notation "L₀" => (Shrink L : Type)

local notation "j" =>
  AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K₀ L₀

/-- The compatible small realization is a genuine finite Galois stage
in the separable closure of the small base. -/
def globalFundamentalSmallStage : FiniteGaloisIntermediateField K₀ (SeparableClosure K₀) :=
  (j).finiteGaloisFieldRange

local notation "E" => globalFundamentalSmallStage K L
local instance globalFundamentalSmallStage_numberField : NumberField E :=
  NumberField.of_module_finite K₀ E

/-- Conjugation of actual automorphisms through the compatible small realization. -/
def globalFundamentalSmallGaloisEquiv : Gal(L/K) ≃* Gal(E/K₀) :=
  (HasseArf.shrinkGalMulEquiv K L).symm.trans (AlgEquiv.autCongr (j).equivFieldRange)

/-! ## Transport to the simultaneous small representatives -/

/-- The native Galois action is reindexed by the actual small field conjugation. -/
def globalFundamentalShrinkH2GroupEquiv : ULift.{v} Gal(L/K) ≃* Gal(L₀/K₀) :=
  MulEquiv.ulift.trans (HasseArf.shrinkGalMulEquiv K L).symm

/-- The native coefficients are sent through the isomorphism of the actual idèle classes. -/
def globalFundamentalShrinkH2CoefficientEquiv : NativeRep ≃+ standardIdeleClassRep K₀ L₀ :=
  AddEquiv.ulift.trans (NumberField.IdeleClassGroup.congr
    (Shrink.ringEquiv L).symm.toRatAlgEquiv).toAdditive

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The simultaneous small representatives preserve the action on every idèle class. -/
theorem globalFundamentalShrinkH2_equivariant (σ : ULift.{v} Gal(L/K)) (a : NativeRep) :
    globalFundamentalShrinkH2CoefficientEquiv K L ((NativeRep).ρ σ a) =
      (standardIdeleClassRep K₀ L₀).ρ (globalFundamentalShrinkH2GroupEquiv K L σ)
        (globalFundamentalShrinkH2CoefficientEquiv K L a) := by
  let S := HasseArf.shrinkGalMulEquiv K L
  let g := S.symm σ.down
  let e := (Shrink.ringEquiv L).symm.toRatAlgEquiv
  let c := NumberField.IdeleClassGroup.congr e
  have he : (σ.down.restrictScalars ℚ).trans e = e.trans (g.restrictScalars ℚ) := by
    apply AlgEquiv.ext
    intro x
    have hh := galEquiv_of_equiv_equiv_apply_equiv (Shrink.ringEquiv K).symm
      (Shrink.ringEquiv L).symm (HasseArf.shrinkAlgebra_commutes K L) g x
    change e (S g x) = g (e x) at hh
    rw [show S g = σ.down from S.apply_symm_apply σ.down] at hh
    exact hh
  let a₀ : Additive (NumberField.IdeleClassGroup (𝓞 L) L) := a.down
  let t := Additive.toMul a₀
  apply Additive.toMul.injective
  change c (NumberField.IdeleClassGroup.congr (σ.down.restrictScalars ℚ) t) =
    NumberField.IdeleClassGroup.congr (g.restrictScalars ℚ) (c t)
  simp only [c, NumberField.IdeleClassGroup.congr_trans, he]

/-- Transport to the simultaneous small representatives on the actual cocycles. -/
def globalFundamentalShrinkH2Equiv :
    groupCohomology NativeRep 2 ≃+ groupCohomology (standardIdeleClassRep K₀ L₀) 2 :=
  groupCohomology.equivariantH2AddEquiv (globalFundamentalShrinkH2GroupEquiv K L)
    (globalFundamentalShrinkH2CoefficientEquiv K L) (globalFundamentalShrinkH2_equivariant K L)

/-- The comparison with the chosen embedded stage is the simultaneous small transport
followed by the change to the actual image of the embedding. -/
def globalFundamentalSmallH2Equiv : H ≃+ groupCohomology (standardIdeleClassRep K₀ E) 2 :=
  (globalFundamentalShrinkH2Equiv K L).trans (standardIdeleClassH2Congr K₀ (j).equivFieldRange)

/-- Realizing the top field in the small closure preserves the extension degree. -/
theorem globalFundamentalSmallStage_finrank :
    Module.finrank K₀ E = Module.finrank K L := by
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (globalFundamentalSmallGaloisEquiv K L).symm.toEquiv

/-- The arithmetic normalization on the original group is identified by
the actual compatible field, idèle-class, and Galois transports. -/
def IsGlobalFundamentalClass (x : H) : Prop :=
  IsNormalizedGlobalFundamentalClass K₀ E (globalFundamentalSmallH2Equiv K L x)

/-- The canonical arithmetic fundamental class for an arbitrary finite Galois
extension of number fields, on the actual standard idèle-class cohomology. -/
def globalFundamentalClass : H :=
  (globalFundamentalSmallH2Equiv K L).symm (canonicalGlobalFundamentalClass K₀ E)

/-- The original normalized class becomes the normalized class of the compatible small pair. -/
theorem globalFundamentalShrinkH2Equiv_globalFundamentalClass :
    globalFundamentalShrinkH2Equiv K L (globalFundamentalClass K L) =
      finiteGlobalFundamentalClass K₀ L₀ := by
  let e : L₀ ≃ₐ[K₀] E := (j).equivFieldRange
  apply (standardIdeleClassH2Congr K₀ e).injective
  change globalFundamentalSmallH2Equiv K L (globalFundamentalClass K L) =
    standardIdeleClassH2Congr K₀ e (finiteGlobalFundamentalClass K₀ L₀)
  rw [globalFundamentalClass, AddEquiv.apply_symm_apply, finiteGlobalFundamentalClass_congr,
    finiteGlobalFundamentalClass_eq_canonical]

/-- The original fundamental class satisfies the arithmetic normalization. -/
theorem globalFundamentalClass_spec :
    IsGlobalFundamentalClass K L (globalFundamentalClass K L) := by
  change IsNormalizedGlobalFundamentalClass K₀ E
    (globalFundamentalSmallH2Equiv K L ((globalFundamentalSmallH2Equiv K L).symm _))
  rw [AddEquiv.apply_symm_apply]
  exact canonicalGlobalFundamentalClass_spec K₀ E

/-- The arithmetic normalization singles out a unique class on the original field. -/
theorem existsUnique_globalFundamentalClass : ∃! x : H, IsGlobalFundamentalClass K L x := by
  refine ⟨globalFundamentalClass K L, globalFundamentalClass_spec K L, ?_⟩
  intro x hx
  apply (globalFundamentalSmallH2Equiv K L).injective
  exact IsNormalizedGlobalFundamentalClass.eq K₀ E hx (globalFundamentalClass_spec K L)

/-- The original class has the full extension degree as its order. -/
theorem addOrderOf_globalFundamentalClass :
    addOrderOf (globalFundamentalClass K L) = Module.finrank K L := by
  exact ((globalFundamentalSmallH2Equiv K L).symm.addOrderOf_eq _).trans
    ((addOrderOf_canonicalGlobalFundamentalClass K₀ E).trans
      (globalFundamentalSmallStage_finrank K L))

/-- The actual standard degree-two idèle-class cohomology has cardinality
the extension degree, by the second inequality and the full-order class. -/
theorem originalStandardIdeleClassH2_finite_card :
    Finite H ∧ Nat.card H = Module.finrank K L := by
  obtain ⟨hfinite, hdvd⟩ := standardIdeleClassH2_finite_card_dvd K₀ E
  let _ := hfinite
  let e := globalFundamentalSmallH2Equiv K L
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, Nat.dvd_antisymm ?_ ?_⟩
  · rw [Nat.card_congr e.toEquiv, ← globalFundamentalSmallStage_finrank K L]
    exact hdvd
  · rw [← addOrderOf_globalFundamentalClass K L]
    exact addOrderOf_dvd_natCard (globalFundamentalClass K L)

end GlobalClassFieldTheory.Cohomology
