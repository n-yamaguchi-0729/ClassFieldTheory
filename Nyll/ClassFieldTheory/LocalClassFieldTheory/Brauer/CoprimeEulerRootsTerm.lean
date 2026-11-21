/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimePowerClasses
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeStageModuleHom
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.MixedLocalProjectorReduction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
public import Mathlib.RepresentationTheory.Rep.Iso

/-! # Integral root torsion at a finite Galois stage -/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousCohomology KummerTheory LocalClassFieldTheory LocalFieldTheory TopRep
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
open scoped Ring ValuativeRel MonoidAlgebra

namespace ClassFieldTheory.Brauer

universe u

private theorem exists_integerUnit_lift_of_primitiveRoot {L Ω : Type u} [Field L] [Field Ω]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (i : L →+* Ω) (p : ℕ) [Fact p.Prime]
    (hroot : ∃ ζ : L, IsPrimitiveRoot ζ p) (x : Ωˣ) (hx : x ^ p = 1) :
    ∃ w : 𝒪[L]ˣ, w ^ p = 1 ∧ Units.map i.toMonoidHom (integerUnitsToFieldUnits L w) = x := by
  let m : ℕ+ := ⟨p, (Fact.out : p.Prime).pos⟩
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let xRoot : rootsOfUnity p Ω := ⟨x, (mem_rootsOfUnity _ _).mpr hx⟩
  obtain ⟨y, hy⟩ :=
    (RamificationTheory.HilbertRamification.restrictRootsOfUnity_bijective_of_primitiveRoot
      i p hroot).2 xRoot
  let yRoot : nthRootsSubgroup L (m : ℕ) := ⟨y.val, (mem_rootsOfUnity _ _).mp y.property⟩
  let w := Kummer.nthRootIntegerUnit L m yRoot
  refine ⟨w, Kummer.nthRootIntegerUnit_pow L m yRoot, ?_⟩
  rw [Kummer.integerUnitsToFieldUnits_nthRootIntegerUnit]
  exact congrArg Subtype.val hy

theorem additiveMap_groupAlgebra_smul (Q : Type u) [Group Q]
    {V W : ModuleCat.{u} ℤ[Q]} (f : V →+ W)
    (hf : ∀ (g : Q) (x : V), f (MonoidAlgebra.of ℤ Q g • x) = MonoidAlgebra.of ℤ Q g • f x)
    (c : ℤ[Q]) (x : V) : f (c • x) = c • f x := by
  induction c using MonoidAlgebra.induction_on with
  | of g => exact hf g x
  | add c d hc hd => rw [add_smul, map_add, hc, hd, add_smul]
  | smul a c hc =>
    calc
      f ((a • c) • x) = f (a • (c • x)) := congrArg f (smul_assoc a c x)
      _ = a • f (c • x) := map_zsmul f a (c • x)
      _ = a • (c • f x) := congrArg (fun y : W => a • y) hc
      _ = (a • c) • f x := (smul_assoc a c (f x)).symm

section InvariantEvaluation

variable {G Q : Type u} [Group G] [Group Q]
    (A M : TopRep.{u} ℤ G) [DiscreteTopology A]

local notation "Dual" => discreteLinearDual A M

/-- The original bidual evaluation identifies fixed coefficients with maps over
the quotient group algebra. -/
def coprimeInvariantEvaluationEquiv
    (quotient : G →* Q) (surjective : Function.Surjective quotient)
    (source target : ModuleCat.{u} ℤ[Q]) (d : source ≃+ Dual) (e : target ≃+ M)
    (hV : ∀ (g : G) (l : source), d (MonoidAlgebra.of ℤ Q (quotient g) • l) = (Dual).ρ g (d l))
    (hT : ∀ (g : G) (x : target), e (MonoidAlgebra.of ℤ Q (quotient g) • x) = M.ρ g (e x))
    (hb : Function.Bijective (discreteLinearDualBidualMap A M)) :
    A.invariants ≃ (source →ₗ[ℤ[Q]] target) := by
  let : Module ℤ A := A.hV2
  let : Module ℤ M := M.hV2
  let : Module ℤ Dual := (Dual).hV2
  let m (a : A) : source →+ target :=
    e.symm.toAddMonoidHom.comp
      ((discreteLinearDualEvaluation A M a).toAddMonoidHom.comp d.toAddMonoidHom)
  have hm (a : A) (l : source) : e (m a l) = discreteLinearDualEvaluation A M a (d l) :=
    e.apply_symm_apply _
  let evaluation (a : A.invariants) : source →ₗ[ℤ[Q]] target :=
    { toFun := m a.val
      map_add' := (m a.val).map_add
      map_smul' := fun c l => by
        apply additiveMap_groupAlgebra_smul Q (m a.val) ?_ c l
        intro q x
        obtain ⟨g, rfl⟩ := surjective q
        apply e.injective
        calc
          _ = discreteLinearDualEvaluation A M a.val (d (MonoidAlgebra.of ℤ Q (quotient g) • x)) :=
            hm a.val _
          _ = discreteLinearDualEvaluation A M a.val ((Dual).ρ g (d x)) :=
            congrArg (discreteLinearDualEvaluation A M a.val) (hV g x)
          _ = M.ρ g (discreteLinearDualEvaluation A M a.val (d x)) := by
            have h := discreteLinearDualEvaluation_equivariant A M g a.val (d x)
            rw [a.property g] at h
            exact h
          _ = _ := (congrArg (M.ρ g) (hm a.val x).symm).trans (hT g _).symm }
  refine Equiv.ofBijective evaluation ⟨?_, ?_⟩
  · intro a a' h
    apply Subtype.ext
    apply hb.1
    apply LinearMap.ext
    intro l
    obtain ⟨x, rfl⟩ := d.surjective l
    exact (hm a.val x).symm.trans
      ((congrArg (fun f : source →ₗ[ℤ[Q]] target => e (f x)) h).trans (hm a'.val x))
  · intro f
    let b : Dual →+ M := e.toAddMonoidHom.comp (f.toAddMonoidHom.comp d.symm.toAddMonoidHom)
    let f₀ : Dual →ₗ[ℤ] M :=
      { toFun := b
        map_add' := b.map_add
        map_smul' := fun z x =>
          (congrArg b (int_smul_eq_zsmul (Dual).hV2 z x)).trans
            ((map_zsmul b z x).trans (int_smul_eq_zsmul M.hV2 z (b x)).symm) }
    obtain ⟨a, ha⟩ := hb.2 f₀
    have ha' (l : Dual) : discreteLinearDualEvaluation A M a l = f₀ l :=
      LinearMap.congr_fun ha l
    have hf (g : G) (l : Dual) : f₀ ((Dual).ρ g l) = M.ρ g (f₀ l) := by
      obtain ⟨x, rfl⟩ := d.surjective l
      have hx : d.symm ((Dual).ρ g (d x)) = MonoidAlgebra.of ℤ Q (quotient g) • x :=
        (congrArg d.symm (hV g x).symm).trans (d.symm_apply_apply _)
      change e (f (d.symm ((Dual).ρ g (d x)))) = M.ρ g (e (f (d.symm (d x))))
      rw [hx, d.symm_apply_apply]
      exact (congrArg e (f.map_smul (MonoidAlgebra.of ℤ Q (quotient g)) x)).trans (hT g (f x))
    have hfixed (g : G) : A.ρ g a = a := by
      apply hb.1
      apply LinearMap.ext
      intro l
      have hl : (Dual).ρ g ((Dual).ρ g⁻¹ l) = l := by
        have h := congrArg (fun F : Dual →L[ℤ] Dual => F l) (map_mul (Dual).ρ g g⁻¹).symm
        rw [mul_inv_cancel, map_one] at h
        exact h
      calc
        _ = discreteLinearDualEvaluation A M (A.ρ g a) ((Dual).ρ g ((Dual).ρ g⁻¹ l)) :=
          congrArg (discreteLinearDualEvaluation A M (A.ρ g a)) hl.symm
        _ = M.ρ g (discreteLinearDualEvaluation A M a ((Dual).ρ g⁻¹ l)) :=
          discreteLinearDualEvaluation_equivariant A M g a ((Dual).ρ g⁻¹ l)
        _ = M.ρ g (f₀ ((Dual).ρ g⁻¹ l)) := congrArg (M.ρ g) (ha' _)
        _ = f₀ ((Dual).ρ g ((Dual).ρ g⁻¹ l)) := (hf g _).symm
        _ = _ := (congrArg f₀ hl).trans (ha' l).symm
    refine ⟨⟨a, hfixed⟩, LinearMap.ext fun l => e.injective ?_⟩
    exact (hm a l).trans ((ha' (d l)).trans
      (congrArg (fun x : source => e (f x)) (d.symm_apply_apply l)))

end InvariantEvaluation

variable (K : Type u) [Field K] [ValuativeRel K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    [hIntegerClosure :
      @IsIntegralClosure 𝒪[E] 𝒪[K] E _ _ _ (Algebra.ofSubsemiring 𝒪[K]) _]
    (p : ℕ) [Fact p.Prime]

local notation "Ω" => SeparableClosure K
local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Q" => Gal(E/K)
include hIntegerClosure

local notation "O" => @localIntegerUnitRep K E _ _ _ _ _ _ hIntegerClosure
local notation "AlgModules" => localGaloisGroupAlgebraFunctor K E
local notation "UL" =>
  ModuleCat.carrier (Functor.obj AlgModules O)
local notation "T" => LinearMap.ker (LinearMap.nsmulLinear (R := ℤ[Q]) p UL)
local notation "Mu" => separableMuTopRep K p

/-- Inclusion of the actual integer-unit torsion into the separable roots coefficient. -/
def coprimeStageIntegerTorsionToMu : T →ₗ[ℤ] Mu := by
  let f : Additive 𝒪[E]ˣ →+ Additive Ωˣ :=
    ((Units.map E.toIntermediateField.val.toRingHom.toMonoidHom).comp
      (integerUnitsToFieldUnits E)).toAdditive
  refine
    { toFun := fun x => ⟨f x.val, ?_⟩
      map_add' := fun x y => Subtype.ext (f.map_add x.val y.val)
      map_smul' := fun n x => Subtype.ext (map_zsmul f n x.val) }
  let y : Additive 𝒪[E]ˣ := x.val
  change p • f y = 0
  have hx : p • y = 0 := x.property
  exact (map_nsmul f p y).symm.trans ((congrArg f hx).trans f.map_zero)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Fact p.Prime] in
/-- The map takes the same field value as the two underlying unit inclusions. -/
theorem coprimeStageIntegerTorsionToMu_fieldVal (x : T) :
    (Additive.toMul
      (show Additive Ωˣ from (coprimeStageIntegerTorsionToMu K E p x).val)).val =
      E.toIntermediateField.val (integerUnitsToFieldUnits E x.val.toMul : E) := rfl

/-- A stage containing a primitive root already contains every separable root, and
every root in that stage has valuation zero. -/
theorem coprimeStageIntegerTorsionToMu_bijective (ζ : E) (hζ : IsPrimitiveRoot ζ p) :
    Function.Bijective (coprimeStageIntegerTorsionToMu K E p) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  constructor
  · intro x y h
    apply Subtype.ext
    apply Additive.toMul.injective
    apply integerUnitsToFieldUnits_injective E
    apply Units.ext
    apply E.toIntermediateField.val.injective
    exact congrArg (fun z : Mu => (Additive.toMul (show Additive Ωˣ from z.val)).val) h
  · intro z
    let zunit : Ωˣ := Additive.toMul (show Additive Ωˣ from z.val)
    have hz : zunit ^ p = 1 :=
      congrArg (Additive.toMul : Additive Ωˣ → Ωˣ) z.property
    let i : E →+* Ω := E.toIntermediateField.val.toRingHom
    have hroot : ∃ t : E, IsPrimitiveRoot t p := ⟨ζ, hζ⟩
    have hex := exists_integerUnit_lift_of_primitiveRoot (L := ↥E.toIntermediateField)
      i p hroot zunit hz
    obtain ⟨w, hwpow, hw⟩ := hex
    let x : T := ⟨Additive.ofMul w, congrArg Additive.ofMul hwpow⟩
    refine ⟨x, Subtype.ext ?_⟩
    apply Additive.toMul.injective
    change Units.map i.toMonoidHom (integerUnitsToFieldUnits E w) = zunit
    exact hw

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Fact p.Prime] in
/-- Inclusion commutes with the actual restriction action of the absolute group. -/
theorem coprimeStageIntegerTorsionToMu_equivariant (g : Γabs) (x : T) :
    coprimeStageIntegerTorsionToMu K E p
        (MonoidAlgebra.of ℤ Q (finiteGaloisRestriction E g) • x) =
      (Mu).ρ g (coprimeStageIntegerTorsionToMu K E p x) := by
  let s := finiteGaloisRestriction E g
  have hs : MonoidAlgebra.of ℤ Q s • x.val = (O).ρ s x.val :=
    ((O).ρ.asModuleEquiv_symm_map_rho s x.val).symm
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  change E.toIntermediateField.val
      (integerUnitsToFieldUnits E (MonoidAlgebra.of ℤ Q s • x.val).toMul : E) =
    g (E.toIntermediateField.val (integerUnitsToFieldUnits E x.val.toMul : E))
  rw [hs]
  let y : 𝒪[E]ˣ := Additive.toMul (show Additive 𝒪[E]ˣ from x.val)
  have hy := integerUnitsToFieldUnits_galoisGroup_equivariant K E s y
  exact (congrArg (fun a : Eˣ => E.toIntermediateField.val (a : E)) hy).trans
    (finiteGaloisRestriction_commutes E g (integerUnitsToFieldUnits E y : E))

local notation "n" => (Subtype.mk p (Nat.Prime.pos (Fact.out : p.Prime)) : ℕ+)

variable (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [DiscreteTopology A]
    (hfix : ∀ (h : ↥(stageOpenFixingSubgroup K E.toIntermediateField).toSubgroup) (a : A),
      A.ρ (h : Gal(SeparableClosure K/K)) a = a)

local notation "D" => discreteLinearDual A Mu
local notation "Vrep" => coprimeStageDualRep K E p ζ hζ A hfix
local notation "V" =>
  ModuleCat.carrier (Functor.obj AlgModules Vrep)
local notation "r" => ContinuousMonoidHom.toMonoidHom (finiteGaloisRestriction E)


variable [Finite A]

/-- Evaluation on the original coefficient identifies the equivariant Hom into
the actual integer-unit torsion with degree-zero continuous cohomology. -/
def coprimeStageEulerRootsHomEquiv (hn : (p : K) ≠ 0) (hA : ∀ a : A, p • a = 0) :
    continuousCohomology 0 A ≃ (V →ₗ[ℤ[Q]] T) := by
  let : Module ℤ A := A.hV2
  let : Module ℤ (D) := (D).hV2
  let : Module ℤ (Mu) := (Mu).hV2
  let e := LinearEquiv.ofBijective (coprimeStageIntegerTorsionToMu K E p)
    (coprimeStageIntegerTorsionToMu_bijective K E p ζ hζ)
  have hV (g : Γabs) (l : D) : MonoidAlgebra.of ℤ Q (r g) • (show V from l) = (D).ρ g l :=
    ((Vrep).ρ.asModuleEquiv_symm_map_rho (r g) l).symm.trans
      (coprimeStageDualRep_ρ K E p ζ hζ A hfix g l)
  have he (g : Γabs) (x : T) :
      e (MonoidAlgebra.of ℤ Q (r g) • x) = (Mu).ρ g (e x) :=
    coprimeStageIntegerTorsionToMu_equivariant K E p g x
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective Ω
  let h₀ := ContinuousCohomology.zeroIso A
  let e₀ : continuousCohomology 0 A ≃ A.invariants :=
    { toFun := h₀.hom
      invFun := h₀.inv
      left_inv := Iso.hom_inv_id_apply h₀
      right_inv := Iso.inv_hom_id_apply h₀ }
  let d : V ≃+ D := AddEquiv.refl _
  let TQ := ModuleCat.of ℤ[Q] T
  let VQ := ModuleCat.of ℤ[Q] V
  let M := separableMuTopRep K p
  have hbidual := separableMu_bidual_bijective K n hn A hA
  exact e₀.trans (coprimeInvariantEvaluationEquiv A M r hr VQ TQ d e.toAddEquiv hV he hbidual)

/-- The finite-stage root contribution has exactly the cardinality of `H⁰`. -/
theorem coprimeStageEulerRootsHom_card (hn : (p : K) ≠ 0) (hA : ∀ a : A, p • a = 0) :
    Nat.card (V →ₗ[ℤ[Q]] T) = Nat.card (continuousCohomology 0 A) :=
  Nat.card_congr (coprimeStageEulerRootsHomEquiv K E p ζ hζ A hfix hn hA).symm

end ClassFieldTheory.Brauer
