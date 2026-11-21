/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalCohomologicalDimension
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePairingDevissage
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.PrimeCharacterPairing
public import Nyll.GaloisCohomology.Topology.ContinuousRestrictionEquiv

/-! # The degree-zero and degree-two local Tate pairings of the trivial prime line -/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory ClassFieldTower.Cohomology ContinuousCohomology LocalFieldTheory TopRep

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

private theorem addHom_of_zmodEquiv_apply {A : Type u} [AddCommGroup A] {p : ℕ}
    (e : A ≃+ ZMod p) (f : A →+ ZMod p) (a : A) : f a = e a * f (e.symm 1) := by
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective (e a)
  have ha : a = m • e.symm 1 := by
    apply e.injective
    rw [map_zsmul, e.apply_symm_apply, zsmul_eq_mul, mul_one, hm]
  calc
    f a = f (m • e.symm 1) := congrArg f ha
    _ = (m : ZMod p) * f (e.symm 1) := by rw [map_zsmul, zsmul_eq_mul]
    _ = _ := by rw [hm]

private theorem bijective_cyclic_pairing_of_exists_one {A B : Type u}
    [AddCommGroup A] [AddCommGroup B]
    {p : ℕ} [Fact p.Prime] (eA : A ≃+ ZMod p) (eB : B ≃+ ZMod p)
    (P : A →+ (B →+ ZMod p)) (a : A) (b : B) (hab : P a b = 1) : Function.Bijective P := by
  let a₁ := eA.symm 1
  let b₁ := eB.symm 1
  let c := P a₁ b₁
  have hleft (x : A) (y : B) : P x y = eA x * P a₁ y :=
    addHom_of_zmodEquiv_apply eA ((AddMonoidHom.eval y).comp P) x
  have hright (x : A) (y : B) : P x y = eB y * P x b₁ :=
    addHom_of_zmodEquiv_apply eB (P x) y
  have hc : c ≠ 0 := by
    intro h
    have hzero : P a b = 0 := by
      rw [hleft a b, hright a₁ b]
      change eA a * (eB b * c) = 0
      rw [h, mul_zero, mul_zero]
    exact one_ne_zero (hab.symm.trans hzero)
  refine ⟨(injective_iff_map_eq_zero P).mpr ?_, ?_⟩
  · intro x hx
    apply eA.injective
    rw [map_zero]
    have hzero : eA x * c = 0 := (hleft x b₁).symm.trans (DFunLike.congr_fun hx b₁)
    exact (mul_eq_zero.mp hzero).resolve_right hc
  · intro targetCharacter
    let x := eA.symm (targetCharacter b₁ / c)
    refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
    rw [hright x y, hleft x b₁, addHom_of_zmodEquiv_apply eB targetCharacter y]
    change eB y * (eA (eA.symm (targetCharacter b₁ / c)) * c) = eB y * targetCharacter b₁
    rw [eA.apply_symm_apply, div_mul_cancel₀ _ hc]

section InvariantEvaluation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C : TopRep.{u} ℤ G}
  (q : A →ₗ[ℤ] B →ₗ[ℤ] C) (hq : Continuous (fun t : A × B => q t.1 t.2))
  (he : ∀ (g : G) (a : A) (b : B), q (A.ρ g a) (B.ρ g b) = C.ρ g (q a b))

private theorem cupZeroTwo_of_invariant (a : A.invariants) (y : continuousCohomology 2 B) :
    cupZeroTwo q hq he ((zeroIso A).inv a) y =
      map (ContinuousMonoidHom.id G) (cupLeftInvariant q hq he a) 2 y := by
  let e : continuousCohomology 0 A ≅ A.invariants := zeroIso A
  have hcomp : e.inv ≫ e.hom = 𝟙 A.invariants := e.inv_hom_id
  have hx : e.hom (e.inv a) = a :=
    DFunLike.congr_fun (congrArg TopModuleCat.Hom.hom hcomp) a
  let evaluate (z : A.invariants) :=
    map (ContinuousMonoidHom.id G) (cupLeftInvariant q hq he z) 2 y
  change evaluate (e.hom (e.inv a)) = evaluate a
  exact congrArg evaluate hx

private theorem cupTwoZero_of_invariant (x : continuousCohomology 2 A) (b : B.invariants) :
    cupTwoZero q hq he x ((zeroIso B).inv b) =
      map (ContinuousMonoidHom.id G) (rightInvariantCoefficientMap q hq he b) 2 x := by
  let e : continuousCohomology 0 B ≅ B.invariants := zeroIso B
  have hcomp : e.inv ≫ e.hom = 𝟙 B.invariants := e.inv_hom_id
  have hy : e.hom (e.inv b) = b :=
    DFunLike.congr_fun (congrArg TopModuleCat.Hom.hom hcomp) b
  let evaluate (z : B.invariants) :=
    map (ContinuousMonoidHom.id G) (rightInvariantCoefficientMap q hq he z) 2 x
  change evaluate (e.hom (e.inv b)) = evaluate b
  exact congrArg evaluate hy

end InvariantEvaluation

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime]

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "N" => (Subtype.mk p (Nat.Prime.pos (Fact.out : p.Prime)) : ℕ+)
local notation "T" => trivialIntegralZModPLifted p Γabs
local notation "M" => separableMuTopRep K p
local notation "D" => discreteLinearDual (R := ℤ) (G := Γabs) T M
local notation "H" => _root_.continuousCohomology (k := ℤ) (G := Γabs)
local notation "m" => map (ContinuousMonoidHom.id Γabs)

local instance trivialPrimeDiscrete : DiscreteTopology T :=
  inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod p)))

private def primeCohomologyIso {X Y : TopRep.{u} ℤ Γabs} (f : X ≅ Y) (i : ℕ) : H i X ≃+ H i Y := by
  exact AddEquiv.ofBijective ((m f.hom i).hom.toLinearMap.toAddMonoidHom)
    (map_bijective_of_coeffIso f i)

private def trivialPrimeInvariantEquiv : (T).invariants ≃+ ZMod p :=
  { toFun := fun t => (show ULift.{u} (ZMod p) from t.val).down
    invFun := fun a => ⟨ULift.up a, fun _ => rfl⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }

private def trivialPrimeH0Equiv : H 0 T ≃+ ZMod p :=
  (AddEquiv.ofBijective ((zeroIso T).hom.hom.toLinearMap.toAddMonoidHom)
    (ConcreteCategory.bijective_of_isIso (zeroIso T).hom)).trans (trivialPrimeInvariantEquiv K p)

private def trivialPrimeInvariantOne : (T).invariants := ⟨ULift.up (1 : ZMod p), fun _ => rfl⟩

/-- The scalar Kummer cup of a trivial prime character agrees with the
ordinary local Tate pairing under the actual dual isomorphism. -/
theorem primeCharacterKummerPairing_eq_localTatePairingOne (hpK : (p : K) ≠ 0)
    (x : H 1 T) (y : H 1 D) :
    primeCharacterKummerPairing K N hpK x (m (primeCharacterDualIso K p).hom 1 y) =
      localTatePairingOne K N T hpK x y := by
  let f := primeCharacterDualIso K p
  have h := map_cupOneOne (discreteLinearDualIntEvaluation T M)
    (discreteLinearDualIntEvaluation_continuous T M)
    (discreteLinearDualIntEvaluation_equivariant T M)
    (ContinuousMonoidHom.id Γabs) (𝟙 T) f.hom (𝟙 M)
    (kummerScalarPairing K p) (kummerScalarPairing_continuous K p)
    (kummerScalarPairing_equivariant K p)
    (fun a b => (kummerScalarPairing_primeCharacterDual K p a b).symm) x y
  simp only [ContinuousCohomology.map_id, ConcreteCategory.id_apply] at h
  exact congrArg (localKummerTrace K N hpK) h.symm

/-- The degree-one adjoint of the trivial prime line is bijective by actual
local Artin character realization and detection by the Kummer cup. -/
theorem localTatePairingOneAdjoint_bijective_trivialPrime (hpK : (p : K) ≠ 0) :
    Function.Bijective (localTatePairingOneAdjoint K N T hpK) := by
  let f := primeCharacterDualIso K p
  let e := primeCohomologyIso K f 1
  let P := localTatePairingOneAdjoint K N T hpK
  refine ⟨(injective_iff_map_eq_zero P).mpr ?_, ?_⟩
  · intro x hx
    by_contra hne
    obtain ⟨a, ha⟩ := exists_primeCharacterKummerPairing_eq_one K p (Fact.out : p.Prime) hpK x hne
    let y := e.symm (separableKummerH1Class K N hpK a)
    have hy : m f.hom 1 y = separableKummerH1Class K N hpK a := e.apply_symm_apply _
    have h := primeCharacterKummerPairing_eq_localTatePairingOne K p hpK x y
    change primeCharacterKummerPairing K N hpK x (m f.hom 1 y) =
      localTatePairingOne K N T hpK x y at h
    have hh := congrArg (primeCharacterKummerPairing K N hpK x) hy
    have hzero : (1 : ZMod p) = 0 :=
      (hh.trans ha).symm.trans (h.trans (DFunLike.congr_fun hx y))
    exact (one_ne_zero : (1 : ZMod p) ≠ 0) hzero
  · intro ℓ
    let ℓ' := ℓ.comp e.symm.toAddMonoidHom
    obtain ⟨x, hx⟩ :=
      exists_primeCharacterKummerPairing_eq_functional K p (Fact.out : p.Prime) hpK ℓ'
    refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
    change localTatePairingOne K N T hpK x y = ℓ y
    calc
      _ = primeCharacterKummerPairing K N hpK x (e y) :=
        (primeCharacterKummerPairing_eq_localTatePairingOne K p hpK x y).symm
      _ = ℓ (e.symm (e y)) := hx (e y)
      _ = ℓ y := congrArg ℓ (e.symm_apply_apply y)

/-- The canonical degree-zero adjoint of the trivial prime line is bijective.
The invariant scalar one pairs with a dual class of arithmetic trace one. -/
theorem localTatePairingZeroAdjoint_bijective_trivialPrime (hpK : (p : K) ≠ 0) :
    Function.Bijective (localTatePairingZeroAdjoint K N T hpK) := by
  let f := primeCharacterDualIso K p
  let e := (primeCohomologyIso K f 2).trans (localKummerTrace K N hpK)
  let a := trivialPrimeInvariantOne K p
  let x := (zeroIso T).inv a
  let y := e.symm 1
  let P : H 0 T →+ (H 2 D →+ ZMod p) := localTatePairingZeroAdjoint K N T hpK
  have hPair : P x y = 1 := by
    let q := discreteLinearDualIntEvaluation T M
    let hq := discreteLinearDualIntEvaluation_continuous T M
    let he := discreteLinearDualIntEvaluation_equivariant T M
    have hf : cupLeftInvariant q hq he a = f.hom := by
      apply TopRep.hom_ext
      apply ContIntertwiningMap.ext (π₁ := (D).ρ) (π₂ := (M).ρ)
      apply ContinuousLinearMap.ext
      intro l
      exact (primeCharacterDualIso_hom_apply K p l).symm
    let evaluate (φ : D ⟶ M) := localKummerTrace K N hpK (m φ 2 y)
    have h₀ := cupZeroTwo_of_invariant q hq he a y
    have h₁ := congrArg (localKummerTrace K N hpK) h₀
    exact h₁.trans ((congrArg evaluate hf).trans (e.apply_symm_apply 1))
  exact bijective_cyclic_pairing_of_exists_one (p := p) (trivialPrimeH0Equiv K p) e P x y hPair

/-- The canonical degree-two adjoint of the trivial prime line is bijective
when the field contains a primitive root of that order. -/
theorem localTatePairingTwoAdjoint_bijective_trivialPrime (hpK : (p : K) ≠ 0)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Function.Bijective (localTatePairingTwoAdjoint K N T hpK) := by
  let f := primeCharacterDualIso K p
  let g := primitiveKummerTrivialIso K p hζ
  let e₂ := (primeCohomologyIso K g 2).trans (localKummerTrace K N hpK)
  let e₀ := (primeCohomologyIso K (f ≪≫ g.symm) 0).trans (trivialPrimeH0Equiv K p)
  let a := trivialPrimeInvariantOne K p
  let b : (D).invariants := (TopRep.invariantsFunctor ℤ Γabs).map (g ≪≫ f.symm).hom a
  let x := e₂.symm 1
  let y := (zeroIso D).inv b
  let P : H 2 T →+ (H 0 D →+ ZMod p) := localTatePairingTwoAdjoint K N T hpK
  have hPair : P x y = 1 := by
    let q := discreteLinearDualIntEvaluation T M
    let hq := discreteLinearDualIntEvaluation_continuous T M
    let he := discreteLinearDualIntEvaluation_equivariant T M
    have hg : rightInvariantCoefficientMap q hq he b = g.hom := by
      apply TopRep.hom_ext
      apply ContIntertwiningMap.ext (π₁ := (T).ρ) (π₂ := (M).ρ)
      apply ContinuousLinearMap.ext
      intro t
      obtain ⟨k, hk⟩ := ZMod.intCast_surjective (show ULift.{u} (ZMod p) from t).down
      have ht : t = k • a.val := by
        apply ULift.ext
        change (show ULift.{u} (ZMod p) from t).down = k • (1 : ZMod p)
        rw [← hk, zsmul_eq_mul, mul_one]
      let r := discreteLinearDualMap T M b.val
      have h₀ : r a.val = g.hom a.val := by
        change discreteLinearDualMap T M b.val (ULift.up (1 : ZMod p)) = g.hom a.val
        let i : D ⟶ M := f.hom
        let j : M ⟶ D := f.inv
        have hf : j ≫ i = 𝟙 M := f.inv_hom_id
        have hval : i (j (g.hom a.val)) = g.hom a.val :=
          DFunLike.congr_fun (congrArg TopRep.Hom.hom hf) (g.hom a.val)
        exact (primeCharacterDualIso_hom_apply K p b.val).symm.trans hval
      have hleft := (congrArg r ht).trans (map_zsmul r k a.val)
      let j : T →ₗ[ℤ] M := g.hom.hom.toContinuousLinearMap.toLinearMap
      have hright := (congrArg j ht).trans (map_zsmul j k a.val)
      exact hleft.trans ((congrArg (fun v : M => k • v) h₀).trans hright.symm)
    let evaluate (φ : T ⟶ M) := localKummerTrace K N hpK (m φ 2 x)
    have h₀ := cupTwoZero_of_invariant q hq he x b
    have h₁ := congrArg (localKummerTrace K N hpK) h₀
    exact h₁.trans ((congrArg evaluate hg).trans (e₂.apply_symm_apply 1))
  exact bijective_cyclic_pairing_of_exists_one (p := p) e₂ e₀ P x y hPair

end ClassFieldTheory.Brauer
