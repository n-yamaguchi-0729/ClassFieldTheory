/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CoprimeEulerCharacters
public import Nyll.GaloisCohomology.GroupTheory.EquivariantPowerReduction
public import Nyll.ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
public import Mathlib.RepresentationTheory.Rep.Iso

/-! # The actual group-algebra Hom computing first cohomology at a coprime stage -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory
open scoped Ring MonoidAlgebra

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (p : ℕ) [Fact p.Prime]

local notation "Ω" => SeparableClosure K
local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Q" => Gal(E/K)
local notation "S" => stageOpenFixingSubgroup K E.toIntermediateField
local notation "I" => Subtype (fun g : Γabs => g ∈ OpenSubgroup.toSubgroup S)
local notation "Mu" => separableMuTopRep K p
local notation "n" => (Subtype.mk p (Nat.Prime.pos (Fact.out : p.Prime)) : ℕ+)

variable (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [DiscreteTopology A]
    (hfix : ∀ (h : ↥(stageOpenFixingSubgroup K E.toIntermediateField).toSubgroup) (a : A),
      A.ρ (h : Gal(SeparableClosure K/K)) a = a)

local notation "D" => discreteLinearDual A Mu
local notation "dualAction" => ContRepresentation.toRepresentation ℤ Γabs D (TopRep.ρ D)
local notation "r" => ContinuousMonoidHom.toMonoidHom (finiteGaloisRestriction E)

private theorem discreteLinearDual_fixed_of_actions
    {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {G : Type u} [Group G] (A B : TopRep.{u} R G) (σ : G)
    (hA : ∀ a : A, A.ρ σ⁻¹ a = a) (hB : ∀ b : B, B.ρ σ b = b)
    (l : discreteLinearDual A B) : (discreteLinearDual A B).ρ σ l = l := by
  apply LinearMap.ext
  intro a
  change discreteLinearDualMap A B ((discreteLinearDual A B).ρ σ l) a =
    discreteLinearDualMap A B l a
  rw [discreteLinearDual_action, hA, hB]

omit [DiscreteTopology ↑A] in
include ζ hζ hfix in
/-- The actual twisted dual is trivial on the same subgroup as the original
coefficient and the roots of unity. -/
theorem coprimeStageDual_ker : (r).ker ≤ (dualAction).ker := by
  intro g hg
  have hg' : g ∈ E.toIntermediateField.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact hg
  let gi : I := ⟨g⁻¹, Subgroup.inv_mem _ hg'⟩
  have fixed (l : D) : (D).ρ g l = l :=
    discreteLinearDual_fixed_of_actions A Mu g (fun a => hfix gi a)
      (stageOpenFixingSubgroup_mu_fixed K E p ζ hζ ⟨g, hg'⟩) l
  change ((dualAction) g) = 1
  apply LinearMap.ext
  intro l
  exact (fixed l).trans (one_apply_eq_self l).symm

/-- The original twisted dual descends to the actual finite Galois group. -/
def coprimeStageDualRep : Rep.{u} ℤ Q := by
  let e := QuotientGroup.quotientKerEquivOfSurjective r (AlgEquiv.restrictNormalHom_surjective Ω)
  exact Rep.of ((QuotientGroup.lift (r).ker dualAction
    (coprimeStageDual_ker K E p ζ hζ A hfix)).comp e.symm.toMonoidHom)

omit [DiscreteTopology ↑A] in
/-- The descended action evaluates to the original action on each restricted element. -/
theorem coprimeStageDualRep_ρ (g : Γabs) (l : D) :
    (coprimeStageDualRep K E p ζ hζ A hfix).ρ (r g) l = (D).ρ g l := by
  let e := QuotientGroup.quotientKerEquivOfSurjective r (AlgEquiv.restrictNormalHom_surjective Ω)
  let m := QuotientGroup.lift (r).ker dualAction
    (coprimeStageDual_ker K E p ζ hζ A hfix)
  change m (e.symm (r g)) l = _
  have he : e (QuotientGroup.mk' (r).ker g) = r g := rfl
  rw [← he, e.symm_apply_apply]
  rfl

local notation "P" => MonoidHom.range (powMonoidHom p : Eˣ →* Eˣ)
local notation "PL" => Additive (Eˣ ⧸ P)

/-- The actual power quotient with the original action on field units. -/
def coprimeStagePowerQuotRep : Rep.{u} ℤ Q := by
  let actualAddGroup : AddCommGroup PL :=
    @Additive.addCommGroup (Eˣ ⧸ P) (QuotientGroup.Quotient.commGroup _)
  let : Module ℤ PL := powerClassesIntegralModule (E := E) (p := p)
  let act (g : Q) : PL →ₗ[ℤ] PL :=
    let e : PL →+ PL :=
      MonoidHom.toAdditive (separableKummerPowerClassConjugation E g.toRingEquiv n)
    @AddMonoidHom.toIntLinearMap PL PL actualAddGroup actualAddGroup e
  refine Rep.of (X := PL) { toFun := act, map_one' := ?_, map_mul' := ?_ }
  · apply LinearMap.ext
    intro x
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective P x.toMul
    have hx : x = Additive.ofMul (QuotientGroup.mk a) := congrArg Additive.ofMul ha.symm
    subst x
    rfl
  · intro g h
    apply LinearMap.ext
    intro x
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective P x.toMul
    have hx : x = Additive.ofMul (QuotientGroup.mk a) := congrArg Additive.ofMul ha.symm
    subst x
    rfl

theorem coprimeStagePowerQuotRep_ρ (g : Q) (x : PL) :
    (coprimeStagePowerQuotRep K E p).ρ g x = Additive.ofMul
      (separableKummerPowerClassConjugation E g.toRingEquiv n x.toMul) := rfl

local notation "F" => Rep.toModuleMonoidAlgebra (k := ℤ) (G := Q)
local notation "U" => Rep.ofAlgebraAutOnUnits K E
local notation "PowerRep" => coprimeStagePowerQuotRep K E p

/-- The original quotient of units, equivariant for the finite Galois action. -/
def coprimeStagePowerClassQuotient : U ⟶ PowerRep :=
  Rep.ofHom ((QuotientGroup.mk' P).toAdditive.toIntLinearMap.intertwiningMap_of_isIntertwiningMap
    (U).ρ (PowerRep).ρ (fun _ _ => rfl))

/-- The same power classes as the quotient by multiplication by the prime
on the actual integral group-algebra module of units. -/
def coprimeStagePowerQuotRepModuleEquiv :
    ((F).obj U ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ[Q]) p ((F).obj U))) ≃ₗ[ℤ[Q]]
      (F).obj PowerRep := by
  let q := ((F).map (coprimeStagePowerClassQuotient K E p)).hom
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective P
  have hker : LinearMap.range (LinearMap.nsmulLinear (R := ℤ[Q]) p ((F).obj U)) =
      LinearMap.ker q := by
    ext x
    let x₀ : Additive Eˣ := x
    change (∃ y : Additive Eˣ, p • y = x₀) ↔ ((QuotientGroup.mk x₀.toMul : Eˣ ⧸ P) = 1)
    refine Iff.trans ?_ (QuotientGroup.eq_one_iff (N := P) x₀.toMul).symm
    exact ⟨fun ⟨y, hy⟩ => ⟨y.toMul, congrArg Additive.toMul hy⟩,
      fun ⟨y, hy⟩ => ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩⟩
  exact (Submodule.quotEquivOfEq _ _ hker).trans (q.quotKerEquivOfSurjective hq)

/-- The original equivariant linear-map condition is precisely linearity
over the actual finite group algebra. -/
def equivariantMapGroupAlgebraEquiv (V W : Rep.{u} ℤ Q) :
    { f : V →ₗ[ℤ] W // ∀ g : Q, ∀ x : V, f (V.ρ g x) = W.ρ g (f x) } ≃
      ((Rep.toModuleMonoidAlgebra.obj V) →ₗ[ℤ[Q]] (Rep.toModuleMonoidAlgebra.obj W)) := by
  let f : { f : V →ₗ[ℤ] W // ∀ g : Q, ∀ x : V, f (V.ρ g x) = W.ρ g (f x) } ≃
      (V ⟶ W) :=
    { toFun := fun φ => Rep.ofHom (φ.val.intertwiningMap_of_isIntertwiningMap V.ρ W.ρ φ.property)
      invFun := fun φ => ⟨φ.hom.toLinearMap, fun g x =>
        Representation.IntertwiningMap.isIntertwining V.ρ W.ρ φ.hom g x⟩
      left_inv := fun φ => Subtype.ext rfl
      right_inv := fun φ => Rep.hom_ext rfl }
  let e := Rep.equivalenceModuleMonoidAlgebra (k := ℤ) (G := Q)
  exact f.trans (e.fullyFaithfulFunctor.homEquiv.trans ModuleCat.homEquiv)

local instance coprimeStageSeparableClosureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

variable [Finite A]
    (j : SeparableClosure K ≃ₐ[E] SeparableClosure E)

/-- At a coprime finite stage containing the roots of unity, the original
first cohomology is the actual group-algebra Hom out of its Tate dual. -/
def coprimeStageH1GroupAlgebraHomEquiv (hnK : (p : K) ≠ 0) (hn : (p : E) ≠ 0)
    (hA : ∀ a : A, p • a = 0) (hdeg : ¬p ∣ Module.finrank K E) :
    continuousCohomology 1 A ≃
      ((Rep.toModuleMonoidAlgebra.obj (coprimeStageDualRep K E p ζ hζ A hfix)) →ₗ[ℤ[Q]]
        (Rep.toModuleMonoidAlgebra.obj (coprimeStagePowerQuotRep K E p))) := by
  let V := coprimeStageDualRep K E p ζ hζ A hfix
  let W := coprimeStagePowerQuotRep K E p
  let X := coprimeStageH1KummerPowerClassEquiv K E j p ζ hζ hn A hnK hA hdeg hfix
  refine X.trans ((Equiv.subtypeEquivRight (fun f => ?_)).trans
    (equivariantMapGroupAlgebraEquiv K E V W))
  change f ∈ coprimeKummerPowerClassMaps K E p A ↔
    ∀ g : Q, ∀ l : V, f (V.ρ g l) = W.ρ g (f l)
  constructor
  · intro hf g l
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective Ω g
    have hσ' : (r) σ = g := hσ
    subst g
    let l₀ : D := l
    have hV := coprimeStageDualRep_ρ K E p ζ hζ A hfix σ l₀
    have hW := coprimeStagePowerQuotRep_ρ K E p ((r) σ) (f l₀)
    exact (congrArg (fun x : D => f x) hV).trans ((hf σ l₀).trans hW.symm)
  · intro hf g l
    rw [← coprimeStageDualRep_ρ K E p ζ hζ A hfix g l, ← coprimeStagePowerQuotRep_ρ]
    exact hf (r g) l

/-- The actual degree-one group-algebra Hom uses the same quotient module as
the finite-index lattice calculation of local power classes. -/
def coprimeStageH1GroupAlgebraReductionHomEquiv (hnK : (p : K) ≠ 0) (hn : (p : E) ≠ 0)
    (hA : ∀ a : A, p • a = 0) (hdeg : ¬p ∣ Module.finrank K E) :
    continuousCohomology 1 A ≃
      (((F).obj (coprimeStageDualRep K E p ζ hζ A hfix)) →ₗ[ℤ[Q]]
        ((F).obj U ⧸ LinearMap.range (LinearMap.nsmulLinear (R := ℤ[Q]) p ((F).obj U)))) := by
  let e := coprimeStagePowerQuotRepModuleEquiv K E p
  exact (coprimeStageH1GroupAlgebraHomEquiv K E p ζ hζ A hfix j hnK hn hA hdeg).trans
    { toFun := fun f => e.symm.toLinearMap.comp f
      invFun := fun f => e.toLinearMap.comp f
      left_inv := fun f => LinearMap.ext fun a => e.apply_symm_apply (f a)
      right_inv := fun f => LinearMap.ext fun a => e.symm_apply_apply (f a) }

end ClassFieldTheory.Brauer
