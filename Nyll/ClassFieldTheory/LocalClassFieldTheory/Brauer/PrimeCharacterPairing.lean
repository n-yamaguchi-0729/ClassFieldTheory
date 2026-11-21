/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.KummerReciprocity
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.PrimeCharacterStage
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.PrimeUnitCharacter
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePairing
public import Nyll.GaloisCohomology.Topology.ContinuousH1CocycleSurjectivity
public import Nyll.GaloisCohomology.Topology.ContinuousRestrictionEquiv
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassTopology

/-! # The original local Kummer cup detects every prime-order character -/

@[expose] public section

noncomputable section

open CategoryTheory ClassFieldTower.Cohomology ContinuousCohomology TopRep
open LocalClassFieldTheory LocalFieldTheory
open scoped ContRepresentation ValuativeRel

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

local notation "G" => Gal(SeparableClosure K/K)
local notation "Z[" n "]" => trivialIntegralZModPLifted n G
local notation "Mu[" n "]" => separableMuTopRep K n
local notation "D[" n "]" => discreteLinearDual (Z[n]) (Mu[n])

/-- The actual dual of the trivial cyclic coefficient identifies with the
original roots of unity by evaluation at the scalar one. -/
def primeCharacterDualIso (p : ℕ) : D[p] ≅ Mu[p] := by
  let A := Z[p]
  let M := Mu[p]
  let one : A := ULift.up (1 : ZMod p)
  let f : D[p] →ₗ[ℤ] M := discreteLinearDualIntEvaluation A M one
  let φ : (D[p]).ρ →ⁱL M.ρ := {
    toLinearMap := f
    cont := continuous_of_discreteTopology
    isIntertwining' := fun σ => by
      apply ContinuousLinearMap.ext
      intro x
      change discreteLinearDualMap A M ((D[p]).ρ σ x) one =
        M.ρ σ (discreteLinearDualMap A M x one)
      rw [discreteLinearDual_action]
      rfl }
  refine discreteCoefficientIsoOfBijective (ConcreteCategory.ofHom (C := TopRep ℤ G) φ) ?_
  change Function.Bijective f
  constructor
  · intro x y hxy
    apply LinearMap.ext
    intro a
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (show ULift.{u} (ZMod p) from a).down
    have ha : a = m • one := ULift.ext (by
      change _ = m • (1 : ZMod p)
      rw [← hm, zsmul_eq_mul, mul_one])
    change discreteLinearDualMap A M x a = discreteLinearDualMap A M y a
    rw [ha, map_zsmul, map_zsmul]
    exact congrArg (fun z : M => m • z) hxy
  · intro x
    refine ⟨(kummerScalarPairing K p).flip x, ?_⟩
    change kummerScalarPairing K p one x = x
    have hone : one = (ULift.up ((1 : ℤ) : ZMod p) : A) := ULift.ext Int.cast_one.symm
    exact (congrArg (fun a : A => kummerScalarPairing K p a x) hone).trans
      ((kummerScalarPairing_intCast K p 1 x).trans (one_zsmul x))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem primeCharacterDualIso_hom_apply (p : ℕ) (x : D[p]) :
    (primeCharacterDualIso K p).hom x =
      discreteLinearDualMap (Z[p]) (Mu[p]) x (ULift.up (1 : ZMod p)) := rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The scalar cup uses exactly the ordinary dual evaluation at an arbitrary
cyclic coefficient. -/
theorem kummerScalarPairing_primeCharacterDual (p : ℕ) (a : Z[p]) (x : D[p]) :
    kummerScalarPairing K p a ((primeCharacterDualIso K p).hom x) =
      discreteLinearDualIntEvaluation (Z[p]) (Mu[p]) a x := by
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (show ULift.{u} (ZMod p) from a).down
  have ha : a = ULift.up (m : ZMod p) := ULift.ext hm.symm
  let one : Z[p] := ULift.up (1 : ZMod p)
  have hm' : (ULift.up (m : ZMod p) : Z[p]) = m • one := by
    apply ULift.ext
    change (m : ZMod p) = m • (1 : ZMod p)
    rw [zsmul_eq_mul, mul_one]
  let eval := discreteLinearDualMap (Z[p]) (Mu[p]) x
  let y := (primeCharacterDualIso K p).hom x
  change kummerScalarPairing K p a y = discreteLinearDualIntEvaluation (Z[p]) (Mu[p]) a x
  calc
    _ = kummerScalarPairing K p (ULift.up (m : ZMod p)) y := congrArg (fun t : Z[p] =>
      kummerScalarPairing K p t y) ha
    _ = m • y := kummerScalarPairing_intCast K p m y
    _ = eval (m • one) := (map_zsmul eval m one).symm
    _ = eval a := congrArg eval (hm'.symm.trans ha.symm)
    _ = _ := rfl

/-- The cup of a prime-order character and a class of the natural Kummer coefficient. -/
def primeCharacterKummerPairing (p : ℕ+) (hpK : ((p : ℕ) : K) ≠ 0)
    (x : continuousCohomology 1 (Z[p])) (y : continuousCohomology 1 (Mu[p])) : ZMod (p : ℕ) :=
  localKummerTrace K p hpK
    (cupOneOne (kummerScalarPairing K p) (kummerScalarPairing_continuous K p)
      (kummerScalarPairing_equivariant K p) x y)

/-- A nonzero character is detected by the Kummer class of an original unit,
with trace one in the same coefficient and with no assumption of roots in the base. -/
theorem exists_primeCharacterKummerPairing_eq_one (p : ℕ) (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (x : continuousCohomology 1 (Z[p])) (hx : x ≠ 0) :
    ∃ a : Kˣ, primeCharacterKummerPairing K ⟨p, hp.pos⟩ hpK x
      (separableKummerH1Class K ⟨p, hp.pos⟩ hpK a) = 1 := by
  obtain ⟨z, hz⟩ := π_surjective (Z[p]) 1 x
  let c := crossedHomOfCocycle (Z[p]) z
  let χ : G →* Multiplicative (ZMod p) :=
    { toFun := fun σ => Multiplicative.ofAdd (c.toFun σ).down
      map_one' := congrArg (fun y : ULift.{u} (ZMod p) => Multiplicative.ofAdd y.down) c.map_one
      map_mul' := fun σ τ => by
        apply Multiplicative.toAdd.injective
        have h : c.toFun (σ * τ) = c.toFun σ + c.toFun τ := c.map_mul σ τ
        exact congrArg ULift.down h }
  let : DiscreteTopology (Z[p]) := inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))
  have hker : IsOpen (χ.ker : Set G) := by
    convert (isOpen_discrete ({0} : Set (Z[p]))).preimage c.continuous_toFun using 1
    ext σ
    exact ⟨fun h => ULift.ext (congrArg Multiplicative.toAdd h),
      fun h => congrArg (fun y : ULift.{u} (ZMod p) => Multiplicative.ofAdd y.down) h⟩
  have hcycles (w : cocycles (Z[p]) 1) :
      (homogeneousCochains (Z[p])).iCycles 1 w =
        (homogeneousCochains (Z[p])).iCycles 1 z → w = z := by
    let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
    let i := F.map ((homogeneousCochains (Z[p])).iCycles 1)
    exact fun h => (ModuleCat.mono_iff_injective i).mp inferInstance h
  have hnonzero : ∃ σ, χ σ ≠ 1 := by
    by_contra! hc
    have hcz (σ : G) : c.toFun σ = 0 :=
      ULift.ext (congrArg Multiplicative.toAdd (hc σ))
    have hzero : z = 0 := (hcycles 0 (by
      rw [map_zero]
      apply Subtype.ext
      ext g h
      rw [homogeneous_oneCocycle_eq_difference, hcz, hcz, sub_zero]
      rfl)).symm
    exact hx (hz.symm.trans (by rw [hzero, map_zero]))
  obtain ⟨E, g, hg, hd, hχ⟩ := exists_primeCharacterStage hp χ hker hnonzero
  subst p
  let : IsCyclic Gal(E/K) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, (Subgroup.eq_top_iff' _).2 hg⟩
  let : IsAbelianGalois K E := IsAbelianGalois.of_isCyclic K E
  have hc (σ : G) :
      (finiteCyclicCharacterCrossedHom K E g hg).toFun σ = c.toFun σ := by
    apply ULift.ext
    have hh := hχ σ
    change _ = (c.toFun σ).down at hh
    rw [ZMod.castHom_apply, ZMod.cast_id] at hh
    exact hh
  have hclass : π _ 1 (finiteCyclicCharacterCrossedHom K E g hg).toCocycle = x := by
    rw [← hz]
    apply congrArg (π _ 1)
    apply hcycles
    rw [CrossedHom.iCycles_toCocycle]
    apply Subtype.ext
    ext s t
    rw [CrossedHom.homogeneous_apply, homogeneous_oneCocycle_eq_difference, hc, hc]
  obtain ⟨a, -, ha⟩ := exists_cyclicFundamentalClass_baseUnit K E g hg
  refine ⟨a, ?_⟩
  apply zmodToRationalCircle_injective (Nat.card Gal(E/K)) Nat.card_pos
  rw [← hclass]
  change zmodToRationalCircle (Nat.card Gal(E/K)) Nat.card_pos
    (localKummerTrace K (cyclicKummerOrder K E) hpK (cyclicKummerCupOfUnit K E g hg a hpK)) = _
  rw [localKummerTrace_cyclicKummerCupOfUnit_eq_artin, ha, inv_inv]
  change zmodToRationalCircle (Nat.card Gal(E/K)) Nat.card_pos
    (finiteCyclicGeneratorCoordinate g hg g) = _
  rw [finiteCyclicGeneratorCoordinate_generator]
  rfl

/-- Every additive functional of the actual local Kummer classes is realized by
the cup of its original prime-order absolute character. -/
theorem exists_primeCharacterKummerPairing_eq_functional (p : ℕ) (hp : p.Prime)
    (hpK : (p : K) ≠ 0)
    (ℓ : continuousCohomology 1 (Mu[p]) →+ ZMod p) :
    ∃ x : continuousCohomology 1 (Z[p]), ∀ y,
      primeCharacterKummerPairing K ⟨p, hp.pos⟩ hpK x y = ℓ y := by
  let n : ℕ+ := ⟨p, hp.pos⟩
  let κ := separableKummerH1Class K n hpK
  have hκ : Function.Surjective κ := by
    intro y
    obtain ⟨b, hb⟩ := (separableMuH1EquivPowerClasses K n hpK).surjective
      (Multiplicative.ofAdd y)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, congrArg Multiplicative.toAdd hb⟩
  by_cases hℓ : ℓ = 0
  · subst ℓ
    refine ⟨0, fun y => ?_⟩
    change localKummerTrace K n hpK
      (cupOneOne (kummerScalarPairing K p) (kummerScalarPairing_continuous K p)
        (kummerScalarPairing_equivariant K p) 0 y) = 0
    have h := cupOneOne_zero_left (kummerScalarPairing K p)
      (kummerScalarPairing_continuous K p) (kummerScalarPairing_equivariant K p) y
    exact (congrArg (localKummerTrace K n hpK) h).trans (map_zero _)
  let χ : Kˣ →* Multiplicative (ZMod p) :=
    ℓ.toMultiplicative.comp ((separableMuH1EquivPowerClasses K n hpK).toMonoidHom.comp
      (QuotientGroup.mk' _))
  let P := (powMonoidHom p : Kˣ →* Kˣ).range
  let : Finite (Kˣ ⧸ P) := finite_nthPowerQuotient_of_natCast_ne_zero K p hpK
  let : P.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hP : IsOpen (P : Set Kˣ) :=
    P.isOpen_of_isClosed_of_finiteIndex (isClosed_powerSubgroup K p hp.ne_zero)
  have hle : P ≤ χ.ker := by
    rintro _ ⟨a, rfl⟩
    change χ (a ^ p) = 1
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    change p • (χ a).toAdd = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hχ : ∃ a, χ a ≠ 1 := by
    by_contra! hc
    apply hℓ
    ext y
    obtain ⟨a, rfl⟩ := hκ y
    exact congrArg Multiplicative.toAdd (hc a)
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Finite (Multiplicative (ZMod p)) := Finite.of_equiv (ZMod p) Multiplicative.ofAdd
  obtain ⟨E, hab, ψ, hψ, hψπ⟩ :=
    exists_finiteLocalArtinCharacterStage K χ (Subgroup.isOpen_mono hle hP)
  let : IsAbelianGalois K E := hab
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨a, ha⟩ := primeCharacter_surjective hp χ hχ z
    exact ⟨LocalClassFieldTheory.abelianLocalArtinMap K E a, (hψπ a).trans ha⟩
  let e := MulEquiv.ofBijective ψ ⟨hψ, hψs⟩
  obtain ⟨g, hg, hd, hcoord⟩ := exists_primeCoordinate_of_mulEquiv hp e
  subst p
  let : IsCyclic Gal(E/K) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, (Subgroup.eq_top_iff' _).2 hg⟩
  let x := -π _ 1 (finiteCyclicCharacterCrossedHom K E g hg).toCocycle
  refine ⟨x, fun y => ?_⟩
  obtain ⟨a, rfl⟩ := hκ y
  have hrec := localKummerTrace_cyclicKummerCupOfUnit_eq_artin K E g hg a hpK
  have hc : finiteCyclicGeneratorCoordinate g hg
      ((LocalClassFieldTheory.abelianLocalArtinMap K E a)⁻¹) =
      -ℓ (κ a) := by
    have he := hcoord ((LocalClassFieldTheory.abelianLocalArtinMap K E a)⁻¹)
    rw [ZMod.castHom_apply, ZMod.cast_id] at he
    change _ = (ψ ((LocalClassFieldTheory.abelianLocalArtinMap K E a)⁻¹)).toAdd at he
    rw [map_inv, hψπ] at he
    exact he
  have htrace :
      localKummerTrace K (cyclicKummerOrder K E) hpK (cyclicKummerCupOfUnit K E g hg a hpK) =
        -ℓ (κ a) := by
    apply zmodToRationalCircle_injective (Nat.card Gal(E/K)) Nat.card_pos
    rw [hrec]
    exact congrArg (zmodToRationalCircle _ _) hc
  let order := cyclicKummerOrder K E
  let pE := (order : ℕ)
  let pair := kummerScalarPairing K pE
  let cont := kummerScalarPairing_continuous K pE
  let equiv := kummerScalarPairing_equivariant K pE
  let z : continuousCohomology 1 (Z[pE]) :=
    π _ 1 (finiteCyclicCharacterCrossedHom K E g hg).toCocycle
  let trace := localKummerTrace K order hpK
  have hneg := cupOneOne_neg_left pair cont equiv z (κ a)
  have hm := map_neg trace (cyclicKummerCupOfUnit K E g hg a hpK)
  exact (congrArg trace hneg).trans (hm.trans ((congrArg Neg.neg htrace).trans (neg_neg _)))

end ClassFieldTheory.Brauer
