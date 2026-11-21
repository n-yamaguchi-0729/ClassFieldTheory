/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Nyll.GaloisCohomology.Topology.AlgebraicGaloisOrbits

/-! # Coprime abelian stages for prime scalar coefficients -/

@[expose] public section

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] (p : ℕ) [Fact p.Prime]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)

/-- The index of the scalar-action kernel divides the order of the nonzero
scalars in the prime coefficient field. -/
theorem scalarCharacter_kernelIndex_dvd (χ : G →* (ZMod p)ˣ) : χ.ker.index ∣ p - 1 := by
  change Nat.card (G ⧸ χ.ker) ∣ p - 1
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv]
  have h : Nat.card (ZMod p)ˣ = p - 1 :=
    Nat.card_eq_fintype_card.trans (ZMod.card_units p)
  exact h ▸ Subgroup.card_subgroup_dvd_card χ.range

/-- The kernel of the actual cyclotomic scalar action is the stabilizer of a
chosen primitive root in the separable closure. -/
theorem cyclotomicScalar_eq_one_iff_fixed {ζ : Ω} (hζ : IsPrimitiveRoot ζ p)
    [NeZero p] (σ : G) : hζ.autToPow K σ = 1 ↔ σ ζ = ζ := by
  let : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hspec := hζ.autToPow_spec K σ
  constructor
  · intro h
    rw [h, Units.val_one, ZMod.val_one, pow_one] at hspec
    exact hspec.symm
  · intro h
    apply Units.ext
    apply ZMod.val_injective p
    rw [Units.val_one, ZMod.val_one]
    exact hζ.pow_inj (ZMod.val_lt _) (Fact.out : 1 < p)
      (hspec.trans (h.trans (pow_one ζ).symm))

/-- A locally constant character of prime-to-`p` finite abelian order and the
prime cyclotomic character
factor through one finite abelian Galois stage of degree prime to `p`. The
stage contains an actual primitive root and its fixing subgroup kills the
original scalar character. -/
theorem exists_coprimeCommutativeCharacterStage (hpK : (p : K) ≠ 0)
    {D : Type*} [CommGroup D] [Finite D] (hD : ¬ p ∣ Nat.card D)
    (χ : G →* D) (hχ : IsLocallyConstant χ) :
    ∃ E : FiniteGaloisIntermediateField K Ω, IsMulCommutative Gal(E/K) ∧
      ∃ ζ : E, IsPrimitiveRoot ζ p ∧ ¬ p ∣ Module.finrank K E ∧
        ∀ σ : G, σ ∈ E.toIntermediateField.fixingSubgroup → χ σ = 1 := by
  let hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω p
  let ψ := hζ.autToPow K
  let f : G →* D × (ZMod p)ˣ := χ.prod ψ
  let N := f.ker
  have hNset : (N : Set G) = (χ.ker : Set G) ∩ {σ : G | σ ζ = ζ} := by
    ext σ
    change (χ σ, ψ σ) = ((1, 1) : D × (ZMod p)ˣ) ↔ χ σ = 1 ∧ σ ζ = ζ
    exact ⟨fun h => ⟨congrArg Prod.fst h,
      (cyclotomicScalar_eq_one_iff_fixed K p hζ σ).mp (congrArg Prod.snd h)⟩,
      fun h => Prod.ext h.1 ((cyclotomicScalar_eq_one_iff_fixed K p hζ σ).mpr h.2)⟩
  have hχopen : IsOpen (χ.ker : Set G) := hχ.isOpen_fiber 1
  have hζopen : IsOpen {σ : G | σ ζ = ζ} :=
    (GaloisCohomology.isLocallyConstant_galois_apply (K := K) ζ).isOpen_fiber ζ
  have hN : IsOpen (N : Set G) := hNset.symm ▸ hχopen.inter hζopen
  let C : ClosedSubgroup G := ⟨N, (⟨N, hN⟩ : OpenSubgroup G).isClosed⟩
  let F := IntermediateField.fixedField N
  have hfix : F.fixingSubgroup = N := InfiniteGalois.fixingSubgroup_fixedField C
  let E : FiniteGaloisIntermediateField K Ω :=
    { toIntermediateField := F
      finiteDimensional := (InfiniteGalois.isOpen_iff_finite F).mp (hfix.symm ▸ hN)
      isGalois := (InfiniteGalois.normal_iff_isGalois F).mp (hfix.symm ▸ inferInstanceAs N.Normal) }
  let : FiniteDimensional K E := E.finiteDimensional
  let : IsGalois K E := E.isGalois
  let : C.toSubgroup.Normal := inferInstanceAs N.Normal
  let q : (G ⧸ N) ≃* Gal(E/K) := InfiniteGalois.normalAutEquivQuotient C
  let e : Gal(E/K) ≃* f.range := q.symm.trans (QuotientGroup.quotientKerEquivRange f)
  have hab : IsMulCommutative Gal(E/K) := isMulCommutative_iff.mpr fun g h =>
    e.injective (by rw [map_mul, map_mul, mul_comm])
  have hcard : Module.finrank K E ∣ Nat.card D * (p - 1) := by
    rw [← IsGalois.card_aut_eq_finrank K E, Nat.card_congr e.toEquiv]
    have hc : Nat.card (D × (ZMod p)ˣ) = Nat.card D * (p - 1) := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := (ZMod p)ˣ), ZMod.card_units]
    exact hc ▸ Subgroup.card_subgroup_dvd_card f.range
  have hd : ¬ p ∣ Module.finrank K E := by
    intro h
    have hsmall : ¬ p ∣ p - 1 := Nat.not_dvd_of_pos_of_lt
      (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos Nat.zero_lt_one)
    exact (hp.dvd_mul.mp (h.trans hcard)).elim hD hsmall
  have hζF : ζ ∈ F := by
    apply (IntermediateField.mem_fixedField_iff N ζ).mpr
    intro σ hσ
    have hs : σ ∈ ((χ.ker : Set G) ∩ {τ : G | τ ζ = ζ}) := hNset ▸ hσ
    exact hs.2
  let ζE : E := ⟨ζ, hζF⟩
  have hζE : IsPrimitiveRoot ζE p :=
    IsPrimitiveRoot.of_map_of_injective (f := F.val) hζ F.val.injective
  refine ⟨E, hab, ζE, hζE, hd, fun σ hσ => ?_⟩
  have hn : σ ∈ N := hfix ▸ hσ
  have hs : σ ∈ ((χ.ker : Set G) ∩ {τ : G | τ ζ = ζ}) := hNset ▸ hn
  exact hs.1

/-- The coprime scalar stage specialized to a character over the prime field. -/
theorem exists_coprimeScalarCharacterStage (hpK : (p : K) ≠ 0)
    (χ : G →* (ZMod p)ˣ) (hχ : IsLocallyConstant χ) :
    ∃ E : FiniteGaloisIntermediateField K Ω, IsMulCommutative Gal(E/K) ∧
      ∃ ζ : E, IsPrimitiveRoot ζ p ∧ ¬ p ∣ Module.finrank K E ∧
        ∀ σ : G, σ ∈ E.toIntermediateField.fixingSubgroup → χ σ = 1 := by
  have hp : p.Prime := Fact.out
  apply exists_coprimeCommutativeCharacterStage K p hpK _ χ hχ
  rw [Nat.card_eq_fintype_card, ZMod.card_units]
  exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.one_lt) (Nat.sub_lt hp.pos Nat.zero_lt_one)

/-- The unit group of a finite field has order prime to its characteristic. -/
theorem finiteFieldUnits_card_not_dvd (k : Type*) [Field k] [Finite k] [CharP k p] :
    ¬ p ∣ Nat.card kˣ := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨m, _, hm⟩ := FiniteField.card k p
  have hcard : p ∣ Nat.card k := by
    rw [Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self p m.ne_zero
  intro h
  have hd := Nat.dvd_sub hcard h
  rw [Nat.card_eq_card_units_add_one k] at hd
  have hs : Nat.card kˣ + 1 - Nat.card kˣ = 1 := by omega
  exact (Fact.out : p.Prime).not_dvd_one (hs ▸ hd)

/-- A scalar line over a finite coefficient field is trivialized over a
coprime abelian stage with a primitive root in the original separable closure. -/
theorem exists_coprimeFiniteFieldScalarLineStage (hpK : (p : K) ≠ 0)
    (k : Type*) [Field k] [Finite k] [CharP k p] (A : TopRep.{u} ℤ G)
    (e : A ≃+ k) (χ : G →* kˣ) (hχ : IsLocallyConstant χ)
    (hact : ∀ σ a, e (A.ρ σ a) = (χ σ : k) * e a) :
    ∃ E : FiniteGaloisIntermediateField K Ω, IsMulCommutative Gal(E/K) ∧
      ∃ ζ : E, IsPrimitiveRoot ζ p ∧ ¬ p ∣ Module.finrank K E ∧
        ∀ σ : G, σ ∈ E.toIntermediateField.fixingSubgroup → ∀ a : A, A.ρ σ a = a := by
  obtain ⟨E, hab, ζ, hζ, hd, hfix⟩ := exists_coprimeCommutativeCharacterStage K p hpK
    (finiteFieldUnits_card_not_dvd p k) χ hχ
  refine ⟨E, hab, ζ, hζ, hd, fun σ hσ a => e.injective ?_⟩
  rw [hact, hfix σ hσ, Units.val_one, one_mul]

/-- A continuous scalar line on the original coefficient module is trivialized
at a finite abelian stage of degree prime to its coefficient prime. The same
stage contains the actual primitive root needed for Kummer theory. -/
theorem exists_coprimeScalarLineStage (hpK : (p : K) ≠ 0) (A : TopRep.{u} ℤ G)
    [DiscreteTopology A] (e : A ≃+ ZMod p)
    (hcont : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) :
    ∃ E : FiniteGaloisIntermediateField K Ω, IsMulCommutative Gal(E/K) ∧
      ∃ ζ : E, IsPrimitiveRoot ζ p ∧ ¬ p ∣ Module.finrank K E ∧
        ∀ σ : G, σ ∈ E.toIntermediateField.fixingSubgroup → ∀ a : A, A.ρ σ a = a := by
  let a₀ := e.symm 1
  have he₀ : e a₀ = 1 := e.apply_symm_apply 1
  let scalar (g : G) : ZMod p := e (A.ρ g a₀)
  have hscalar (g : G) (a : A) : e (A.ρ g a) = scalar g * e a := by
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective (e a)
    have ha : m • a₀ = a := e.injective (by
      rw [map_zsmul, he₀, zsmul_eq_mul, mul_one, hm])
    calc
      e (A.ρ g a) = e (A.ρ g (m • a₀)) := congrArg (fun x => e (A.ρ g x)) ha.symm
      _ = m • scalar g := by rw [map_zsmul, map_zsmul]
      _ = scalar g * e a := by rw [zsmul_eq_mul, hm, mul_comm]
  let f : G →* ZMod p := {
    toFun := scalar
    map_one' := by
      change e (A.ρ 1 a₀) = 1
      rw [map_one]
      exact he₀
    map_mul' := fun g h => by
      change e (A.ρ (g * h) a₀) = scalar g * scalar h
      rw [map_mul]
      exact hscalar g (A.ρ h a₀) }
  let χ : G →* (ZMod p)ˣ := MonoidHom.toHomUnits f
  have hlc : IsLocallyConstant (fun g : G => A.ρ g a₀) :=
    (IsLocallyConstant.iff_continuous _).mpr
      (hcont.comp (continuous_id.prodMk continuous_const))
  have hχ : IsLocallyConstant χ := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro g
    obtain ⟨W, hW, hg, h⟩ := hlc.exists_open g
    exact ⟨W, hW, hg, fun t ht => Units.ext (congrArg e (h t ht))⟩
  obtain ⟨E, hab, ζ, hζ, hd, hfix⟩ := exists_coprimeScalarCharacterStage K p hpK χ hχ
  refine ⟨E, hab, ζ, hζ, hd, fun σ hσ a => e.injective ?_⟩
  have hs : scalar σ = 1 := congrArg Units.val (hfix σ hσ)
  exact (hscalar σ a).trans (by rw [hs, one_mul])

end ClassFieldTheory.Brauer
