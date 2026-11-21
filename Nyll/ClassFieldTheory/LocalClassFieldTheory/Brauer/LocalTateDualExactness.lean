/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.Kummer
public import Nyll.GaloisCohomology.Topology.ContinuousDualExactness
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Short exactness of the roots-of-unity dual

For torsion of invertible exponent, the natural Kummer dual reverses short
exact sequences of discrete coefficients. Its cohomology sequence uses the
same two evaluations and coefficient morphisms as the Tate pairing.
-/

@[expose] public section

open CategoryTheory TopRep

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] (n : ℕ+)

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)
local notation "Mu" => separableMuTopRep K n

private def separableMuAddEquivRootsOfUnity : Mu ≃+ Additive (rootsOfUnity (n : ℕ) Ω) where
  toFun x := Additive.ofMul ⟨(show Additive Ωˣ from x.1).toMul,
    (mem_rootsOfUnity _ _).mpr (congrArg Additive.toMul x.2)⟩
  invFun x := ⟨Additive.ofMul x.toMul.1,
    congrArg Additive.ofMul ((mem_rootsOfUnity _ _).mp x.toMul.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

private theorem separableMu_hasEnoughRootsOfUnity (hn : ((n : ℕ) : K) ≠ 0) :
    HasEnoughRootsOfUnity Ω (n : ℕ) := by
  let : NeZero ((n : ℕ) : Ω) := ⟨by
    have h := (algebraMap K Ω).injective.ne hn
    simpa only [map_natCast, map_zero] using h⟩
  exact IsSepClosed.hasEnoughRootsOfUnity Ω n

private def separableMuAddEquivZMod (hn : ((n : ℕ) : K) ≠ 0) : Mu ≃+ ZMod (n : ℕ) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : HasEnoughRootsOfUnity Ω (n : ℕ) := separableMu_hasEnoughRootsOfUnity K n hn
  let hζ := Classical.choose_spec (HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω n)
  let h := hζ.isUnit_unit' n.ne_zero
  exact (separableMuAddEquivRootsOfUnity K n).trans
    ((MulEquiv.toAdditive (MulEquiv.subgroupCongr h.zpowers_eq.symm)).trans h.zmodEquivZPowers.symm)

/-- The actual roots-of-unity coefficient is finite in the étale range. -/
theorem separableMuTopRep_finite (hn : ((n : ℕ) : K) ≠ 0) : Finite Mu := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact Finite.of_equiv (ZMod (n : ℕ)) (separableMuAddEquivZMod K n hn).symm.toEquiv

private def separableMuDualCharacterEquiv (A : TopRep.{u} ℤ G)
    (hA : ∀ a : A, (n : ℕ) • a = 0) :
    discreteLinearDual A Mu ≃ (Multiplicative A →* Ωˣ) := by
  let U := rootsOfUnity (n : ℕ) Ω
  let e := separableMuAddEquivRootsOfUnity K n
  let : Module ℤ A := A.hV2
  let : Module ℤ Mu := (separableMuTopRep K n).hV2
  let toDual (l : A →ₗ[ℤ] Mu) : discreteLinearDual A Mu := l
  refine
    { toFun := fun l => U.subtype.comp
        ((e.toAddMonoidHom.comp (discreteLinearDualMap A Mu l).toAddMonoidHom).toMultiplicative)
      invFun := fun ψ => by
        let f : A →+ Mu := e.symm.toAddMonoidHom.comp ((ψ.codRestrict U (fun a => by
          change ψ a ^ (n : ℕ) = 1
          rw [← map_pow, show a ^ (n : ℕ) = 1 from congrArg Multiplicative.ofAdd (hA a.toAdd),
            map_one])).toAdditive)
        exact toDual {
          toFun := f
          map_add' := f.map_add
          map_smul' := fun r a => by
            rw [RingHom.id_apply]
            exact (congrArg f (int_smul_eq_zsmul A.hV2 r a)).trans
              ((f.map_zsmul r a).trans
                (int_smul_eq_zsmul (separableMuTopRep K n).hV2 r (f a)).symm) }
      left_inv := ?_
      right_inv := ?_ }
  · intro l
    change _ = discreteLinearDualMap A Mu l
    apply LinearMap.ext
    intro a
    exact e.symm_apply_apply (discreteLinearDualMap A Mu l a)
  · intro ψ
    apply MonoidHom.ext
    intro a
    exact congrArg (fun b : Additive U => b.toMul.val) (e.apply_symm_apply
      (Additive.ofMul (show U from ⟨ψ a, by
        change ψ a ^ (n : ℕ) = 1
        rw [← map_pow, show a ^ (n : ℕ) = 1 from congrArg Multiplicative.ofAdd (hA a.toAdd),
          map_one]⟩)))

private theorem separableMu_hasEnoughRootsOfUnity_exponent (hn : ((n : ℕ) : K) ≠ 0)
    (A : TopRep.{u} ℤ G) (hA : ∀ a : A, (n : ℕ) • a = 0) :
    HasEnoughRootsOfUnity Ω (Monoid.exponent (Multiplicative A)) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : HasEnoughRootsOfUnity Ω (n : ℕ) := separableMu_hasEnoughRootsOfUnity K n hn
  exact HasEnoughRootsOfUnity.of_dvd Ω (n := (n : ℕ))
    (Monoid.exponent_dvd_of_forall_pow_eq_one (fun a => congrArg Multiplicative.ofAdd (hA a.toAdd)))

/-- The actual Kummer dual of finite torsion has the same order as its source. -/
theorem separableMu_dual_card (hn : ((n : ℕ) : K) ≠ 0)
    (A : TopRep.{u} ℤ G) [Finite A] (hA : ∀ a : A, (n : ℕ) • a = 0) :
    Nat.card (discreteLinearDual A Mu) = Nat.card A := by
  let : HasEnoughRootsOfUnity Ω (Monoid.exponent (Multiplicative A)) :=
    separableMu_hasEnoughRootsOfUnity_exponent K n hn A hA
  exact (Nat.card_congr (separableMuDualCharacterEquiv K n A hA)).trans
    (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative A) Ω)

/-- The roots-of-unity coefficient exponent also annihilates the genuine linear dual. -/
theorem separableMu_dual_nsmul_eq_zero (A : TopRep.{u} ℤ G)
    (f : discreteLinearDual A Mu) : (n : ℕ) • f = 0 := by
  let : Module ℤ A := A.hV2
  let : Module ℤ Mu := (separableMuTopRep K n).hV2
  change (n : ℕ) • discreteLinearDualMap A Mu f = 0
  exact LinearMap.ext fun a =>
    separableMuTopRep_nsmul_eq_zero K n (discreteLinearDualMap A Mu f a)

/-- For finite torsion, the canonical evaluation into the actual twisted
double dual is bijective. -/
theorem separableMu_bidual_bijective (hn : ((n : ℕ) : K) ≠ 0)
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A] (hA : ∀ a : A, (n : ℕ) • a = 0) :
    Function.Bijective (discreteLinearDualBidualMap A Mu) := by
  let D := discreteLinearDual A Mu
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : Finite Mu := separableMuTopRep_finite K n hn
  let : Finite D := discreteLinearDual_finite A Mu
  let : Finite (discreteLinearDual D Mu) := discreteLinearDual_finite D Mu
  let : HasEnoughRootsOfUnity Ω (Monoid.exponent (Multiplicative A)) :=
    separableMu_hasEnoughRootsOfUnity_exponent K n hn A hA
  let hD := separableMu_dual_nsmul_eq_zero K n A
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · intro a b hab
    by_contra hne
    have hdiff : Multiplicative.ofAdd (a - b) ≠ 1 :=
      fun h => hne (sub_eq_zero.mp (congrArg Multiplicative.toAdd h))
    obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Multiplicative A) Ω hdiff
    let e := separableMuDualCharacterEquiv K n A hA
    let l := e.symm ψ
    have hl : discreteLinearDualMap A Mu l a = discreteLinearDualMap A Mu l b :=
      congrArg (fun t => discreteLinearDualMap D Mu t l) hab
    apply hψ
    rw [← e.apply_symm_apply ψ]
    change (separableMuAddEquivRootsOfUnity K n
      (discreteLinearDualMap A Mu l (a - b))).toMul.val = 1
    rw [map_sub, hl, sub_self, map_zero]
    rfl
  · exact ((separableMu_dual_card K n hn D hD).trans (separableMu_dual_card K n hn A hA)).symm

/-- Dual coefficient maps are surjective along every injection of modules
of exponent dividing `n`, with values in the actual Kummer coefficient. -/
theorem separableMu_dualPullback_surjective (hn : ((n : ℕ) : K) ≠ 0)
    {A B : TopRep.{u} ℤ G} (f : A ⟶ B) (hf : Function.Injective f)
    (hB : ∀ b : B, (n : ℕ) • b = 0) :
    Function.Surjective (discreteLinearDualPullback Mu f) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact discreteLinearDualPullback_surjective_of_zmod Mu n (separableMuAddEquivZMod K n hn) f hf hB

/-- Actual finite discrete coefficient sequences give short exact dual
cochains and hence a long exact sequence in the same continuous cohomology. -/
theorem separableMu_dualContinuousModuleComplex_shortExact
    (hn : ((n : ℕ) : K) ≠ 0) (S : ShortComplex (TopRep.{u} ℤ G))
    [Finite S.X₂] [Finite S.X₃] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hf : Function.Injective S.f) (hg : Function.Surjective S.g)
    (hexact : ∀ b : S.X₂, S.g b = 0 → ∃ a : S.X₁, S.f a = b)
    (hexponent : ∀ b : S.X₂, (n : ℕ) • b = 0)
    (h₂ : Continuous (fun p : G × S.X₂ => S.X₂.ρ p.1 p.2))
    (h₃ : Continuous (fun p : G × S.X₃ => S.X₃.ρ p.1 p.2)) :
    let M : TopRep.{u} ℤ G := separableMuTopRep K n
    let T : ShortComplex (TopRep.{u} ℤ G) := discreteLinearDualShortComplex M S
    let F : TopRep.{u} ℤ G ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ := continuousModuleComplexFunctor G
    let _ : LocallyCompactSpace G :=
      (inferInstance : LocallyCompactSpace (InfiniteGalois.profiniteGalGrp K Ω))
    let _ : F.PreservesZeroMorphisms :=
      inferInstanceAs ((continuousModuleComplexFunctor G).PreservesZeroMorphisms)
    (T.map F).ShortExact := by
  intro M T F hLC hF
  let : DiscreteTopology M := separableMuTopRep_discrete K n
  have hextend : Function.Surjective (discreteLinearDualPullback M S.f) :=
    separableMu_dualPullback_surjective K n hn S.f hf hexponent
  have hM : Continuous (fun p : G × M => M.ρ p.1 p.2) :=
    separableMuTopRep_action_continuous K n
  exact continuousModuleComplex_discreteLinearDual_shortExact M S hg hexact hextend h₂ h₃ hM

end ClassFieldTheory.Brauer
