/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.StandardHerbrand
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.StandardIdeleClassRepresentation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.ContinuousUnramified
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Nyll.GaloisCohomology.ProP.FiniteCyclicH2TateH0

/-!
# The cyclic global fundamental class on standard idèle classes

A generator identifies degree-two cohomology of the standard idèle class
group with the Tate norm quotient. Arithmetic norm-residue then gives the
normalization by the reciprocal of the extension degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Cohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand GlobalClassFieldTheory.Reciprocity
open scoped IsMulCommutative NumberField

namespace GlobalClassFieldTheory.Cohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulDistribMulAction Gal(L/K) (NumberField.IdeleClassGroup (𝓞 L) L) :=
  NumberField.IdeleClassGroup.relativeGaloisAction K L

variable (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g)

/-- The degree-two arithmetic norm-quotient comparison for the standard
idèle class group, using the periodic resolution for the given generator. -/
def cyclicGlobalIdeleClassH2EquivNormQuotient :
    groupCohomology (standardIdeleClassRep K L) 2 ≃+
      Additive (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (_root_.ideleClassNorm K L).range) := by
  let t := finiteCyclicGroupH2IsoTateHZero (standardIdeleClassRep K L) g hg
  let h := tateH0IsoHerbrandH0 (G := Gal(L/K)) (A := NumberField.IdeleClassGroup (𝓞 L) L)
  let n := NumberField.IdeleClassGroup.herbrandH0EquivClassNormQuotient K L
  exact ((t ≪≫ h).toLinearEquiv.toAddEquiv).trans n.toAdditive

/-- Arithmetic norm-residue identifies the cyclic degree-two cohomology
of the standard idèle class group with the Galois group. -/
def cyclicGlobalIdeleClassH2EquivArtin :
    groupCohomology (standardIdeleClassRep K L) 2 ≃+ Additive Gal(L/K) := by
  let : IsCyclic Gal(L/K) := finiteCyclicH2IsCyclicOfGenerator g hg
  let : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  exact (cyclicGlobalIdeleClassH2EquivNormQuotient K L g hg).trans
    (arithmeticGlobalNormResidueContinuousMulEquiv K L).toMulEquiv.toAdditive

/-- The rational-circle invariant on actual degree-two cohomology of
the standard idèle class group of a cyclic extension. -/
def cyclicGlobalIdeleClassInvariant :
    groupCohomology (standardIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ) :=
  (finiteCyclicArithmeticCharacter g hg).comp
    (cyclicGlobalIdeleClassH2EquivArtin K L g hg).toAddMonoidHom

/-- The cyclic global invariant is injective. -/
theorem cyclicGlobalIdeleClassInvariant_injective :
    Function.Injective (cyclicGlobalIdeleClassInvariant K L g hg) :=
  (finiteCyclicArithmeticCharacter_injective g hg).comp
    (cyclicGlobalIdeleClassH2EquivArtin K L g hg).injective

/-- Every rational-circle element killed by the extension degree is an invariant. -/
theorem mem_range_cyclicGlobalIdeleClassInvariant_iff (z : AddCircle (1 : ℚ)) :
    z ∈ (cyclicGlobalIdeleClassInvariant K L g hg).range ↔ Module.finrank K L • z = 0 := by
  rw [← IsGalois.card_aut_eq_finrank K L,
    ← mem_range_finiteCyclicArithmeticCharacter_iff g hg z]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨cyclicGlobalIdeleClassH2EquivArtin K L g hg x, rfl⟩
  · rintro ⟨x, rfl⟩
    let e := cyclicGlobalIdeleClassH2EquivArtin K L g hg
    exact ⟨e.symm x, congrArg (finiteCyclicArithmeticCharacter g hg) (e.apply_symm_apply x)⟩

/-- The cyclic global fundamental class is the class of the chosen
generator under the arithmetic norm-residue comparison. -/
def cyclicGlobalIdeleClassFundamentalClass :
    groupCohomology (standardIdeleClassRep K L) 2 :=
  (cyclicGlobalIdeleClassH2EquivArtin K L g hg).symm (Additive.ofMul g)

/-- The cyclic global fundamental class has invariant `1 / [L : K]`. -/
@[simp]
theorem cyclicGlobalIdeleClassInvariant_fundamentalClass :
    cyclicGlobalIdeleClassInvariant K L g hg (cyclicGlobalIdeleClassFundamentalClass K L g hg) =
      (((1 : ℚ) / Module.finrank K L : ℚ) : AddCircle (1 : ℚ)) := by
  simp only [cyclicGlobalIdeleClassInvariant, cyclicGlobalIdeleClassFundamentalClass,
    AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  change zmodToRationalCircle (Nat.card Gal(L/K)) Nat.card_pos
    (finiteCyclicGeneratorCoordinate g hg g) = _
  rw [finiteCyclicGeneratorCoordinate_generator]
  simpa only [Int.cast_one, IsGalois.card_aut_eq_finrank] using
    zmodToRationalCircle_intCast (Nat.card Gal(L/K)) Nat.card_pos 1

/-- The reciprocal invariant uniquely determines the cyclic global fundamental class. -/
theorem cyclicGlobalIdeleClassInvariant_eq_reciprocal_iff
    (x : groupCohomology (standardIdeleClassRep K L) 2) :
    cyclicGlobalIdeleClassInvariant K L g hg x =
      (((1 : ℚ) / Module.finrank K L : ℚ) : AddCircle (1 : ℚ)) ↔
        x = cyclicGlobalIdeleClassFundamentalClass K L g hg := by
  rw [← cyclicGlobalIdeleClassInvariant_fundamentalClass K L g hg]
  exact (cyclicGlobalIdeleClassInvariant_injective K L g hg).eq_iff

/-- The order of the cyclic global fundamental class is the extension degree. -/
theorem addOrderOf_cyclicGlobalIdeleClassFundamentalClass :
    addOrderOf (cyclicGlobalIdeleClassFundamentalClass K L g hg) = Module.finrank K L := by
  change addOrderOf ((cyclicGlobalIdeleClassH2EquivArtin K L g hg).symm (Additive.ofMul g)) = _
  rw [AddEquiv.addOrderOf_eq]
  change orderOf g = Module.finrank K L
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, IsGalois.card_aut_eq_finrank]

end GlobalClassFieldTheory.Cohomology
