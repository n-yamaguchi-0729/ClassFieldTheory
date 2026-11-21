/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.Index
public import Nyll.GaloisCohomology.Topology.FiniteCoefficientPrimeDevissage
public import Nyll.GaloisCohomology.Topology.FinitePGroupCoefficientVanishing
public import Nyll.GaloisCohomology.GroupTheory.FiniteExactSequence
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness

/-! # Euler multiplicativity on the actual low-degree homology sequence -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ContinuousCohomology

universe u

private def rangeCard {X Y : ModuleCat.{u} ℤ} (φ : X ⟶ Y) : ℕ :=
  Nat.card φ.hom.toAddMonoidHom.range

private theorem rangeCard_injective {X Y : ModuleCat.{u} ℤ} (φ : X ⟶ Y) (h : Function.Injective φ) :
    rangeCard φ = Nat.card X :=
  Nat.card_range_of_injective h

private theorem rangeCard_surjective {X Y : ModuleCat.{u} ℤ} (φ : X ⟶ Y)
    (h : Function.Surjective φ) :
    rangeCard φ = Nat.card Y := by
  let f := φ.hom.toAddMonoidHom
  exact Nat.card_congr (Equiv.ofBijective (fun y : f.range => (y : Y))
    ⟨Subtype.val_injective, fun y => ⟨⟨y, h y⟩, rfl⟩⟩)

private theorem card_middle_of_exact {X Y Z : ModuleCat.{u} ℤ} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : f ≫ g = 0} (e : (ShortComplex.mk f g h).Exact) :
    Nat.card Y = rangeCard f * rangeCard g := by
  let f' := f.hom.toAddMonoidHom
  let g' := g.hom.toAddMonoidHom
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp e
  have hg : g'.ker = f'.range := AddSubgroup.ext fun y => hex y
  change Nat.card Y = Nat.card f'.range * Nat.card g'.range
  rw [← hg, ← AddSubgroup.index_ker, g'.ker.card_mul_index]

/-- Finiteness of the outer homology groups gives finiteness and a cardinal bound in the middle. -/
theorem finite_homology_of_shortExact (S : ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ))
    (hS : S.ShortExact) (i : ℕ)
    [Finite (S.X₁.homology i)] [Finite (S.X₃.homology i)] :
    Finite (S.X₂.homology i) ∧
      Nat.card (S.X₂.homology i) ≤ Nat.card (S.X₁.homology i) * Nat.card (S.X₃.homology i) := by
  let f := (HomologicalComplex.homologyMap S.f i).hom.toAddMonoidHom
  let g := (HomologicalComplex.homologyMap S.g i).hom.toAddMonoidHom
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.homology_exact₂ i)
  exact f.finite_natCard_le_mul_of_ker_le_range g fun x hx => (he x).mp hx

/-- The cardinal ratio used for a continuous cohomology complex of dimension two. -/
def lowDegreeEulerCharacteristic (C : CochainComplex (ModuleCat.{u} ℤ) ℕ) : ℚ :=
  ((Nat.card (C.homology 0) : ℚ) * (Nat.card (C.homology 2) : ℚ)) /
    (Nat.card (C.homology 1) : ℚ)

/-- The exact low-degree sequence gives Euler multiplicativity as soon as
the displayed groups are finite and the next degree on the left vanishes. -/
theorem lowDegreeEulerCharacteristic_mul_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ))
    (hS : S.ShortExact)
    [Mono (S.f.f 0)]
    [Finite (S.X₁.homology 0)] [Finite (S.X₁.homology 1)] [Finite (S.X₁.homology 2)]
    [Finite (S.X₂.homology 0)] [Finite (S.X₂.homology 1)] [Finite (S.X₂.homology 2)]
    [Finite (S.X₃.homology 0)] [Finite (S.X₃.homology 1)] [Finite (S.X₃.homology 2)]
    (h₃ : IsZero (S.X₁.homology 3)) :
    lowDegreeEulerCharacteristic S.X₂ =
      lowDegreeEulerCharacteristic S.X₁ * lowDegreeEulerCharacteristic S.X₃ := by
  let f (i : ℕ) := HomologicalComplex.homologyMap S.f i
  let g (i : ℕ) := HomologicalComplex.homologyMap S.g i
  have hf₀ : Mono (f 0) := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (by
    intro i hi
    change i + 1 = 0 at hi
    omega)
  have hg₂ : Function.Surjective (g 2) := by
    have e := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ 2 3 rfl)
    intro x
    have hx : hS.δ 2 3 rfl x = 0 :=
      ConcreteCategory.congr_hom (h₃.eq_of_tgt (hS.δ 2 3 rfl) 0) x
    exact (e x).mp hx
  have hA₀ : Nat.card (S.X₁.homology 0) = rangeCard (f 0) :=
    (rangeCard_injective (f 0) ((ModuleCat.mono_iff_injective _).mp hf₀)).symm
  have hC₂ : Nat.card (S.X₃.homology 2) = rangeCard (g 2) := (rangeCard_surjective (g 2) hg₂).symm
  have h₀ := card_middle_of_exact (hS.homology_exact₂ 0)
  have h₁ := card_middle_of_exact (hS.homology_exact₂ 1)
  have h₂ := card_middle_of_exact (hS.homology_exact₂ 2)
  have hC₀ := card_middle_of_exact (hS.homology_exact₃ 0 1 rfl)
  have hC₁ := card_middle_of_exact (hS.homology_exact₃ 1 2 rfl)
  have hA₁ := card_middle_of_exact (hS.homology_exact₁ 0 1 rfl)
  have hA₂ := card_middle_of_exact (hS.homology_exact₁ 1 2 rfl)
  let rangeF (i : ℕ) := rangeCard (f i)
  let rangeG (i : ℕ) := rangeCard (g i)
  let rangeδ₀ := rangeCard (hS.δ 0 1 rfl)
  let rangeδ₁ := rangeCard (hS.δ 1 2 rfl)
  have hprod : Nat.card (S.X₂.homology 0) * Nat.card (S.X₂.homology 2) *
      (Nat.card (S.X₁.homology 1) * Nat.card (S.X₃.homology 1)) =
      (Nat.card (S.X₁.homology 0) * Nat.card (S.X₁.homology 2)) *
        (Nat.card (S.X₃.homology 0) * Nat.card (S.X₃.homology 2)) * Nat.card (S.X₂.homology 1) := by
    rw [h₀, h₂, hA₁, hC₁, hA₀, hA₂, hC₀, hC₂, h₁]
    change (rangeF 0 * rangeG 0) * (rangeF 2 * rangeG 2) *
        ((rangeδ₀ * rangeF 1) * (rangeG 1 * rangeδ₁)) =
      (rangeF 0 * (rangeδ₁ * rangeF 2)) * ((rangeG 0 * rangeδ₀) * rangeG 2) *
        (rangeF 1 * rangeG 1)
    ac_rfl
  have hA : (Nat.card (S.X₁.homology 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hB : (Nat.card (S.X₂.homology 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hC : (Nat.card (S.X₃.homology 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold lowDegreeEulerCharacteristic
  rw [div_mul_div_comm]
  exact (div_eq_div_iff hB (mul_ne_zero hA hC)).mpr (by exact_mod_cast hprod)

end ContinuousCohomology

namespace TopRep

open ContinuousCohomology

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G]

local notation "C" => continuousModuleComplexFunctor G

/-- The first three cohomology groups are finite and their Euler ratio has the given value. -/
def hasLowDegreeEulerCharacteristic (w : ℕ → ℚ) (A : TopRep.{u} ℤ G) : Prop :=
  (∀ i < 3, Finite (((C).obj A).homology i)) ∧
    lowDegreeEulerCharacteristic ((C).obj A) = w (Nat.card A)

variable (w : ℕ → ℚ)

theorem hasLowDegreeEulerCharacteristic_of_subsingleton (hw : w 1 = 1)
    (A : TopRep.{u} ℤ G) [Subsingleton A] : hasLowDegreeEulerCharacteristic G w A := by
  have hs (i : ℕ) : Subsingleton (((C).obj A).homology i) :=
    ModuleCat.isZero_iff_subsingleton.mp (continuousModuleHomology_isZero_of_subsingleton G A i)
  have hc (i : ℕ) : Nat.card (((C).obj A).homology i) = 1 := by
    let : Subsingleton (((C).obj A).homology i) := hs i
    exact Nat.card_unique
  refine ⟨fun i _ => ?_, ?_⟩
  · let : Subsingleton (((C).obj A).homology i) := hs i
    infer_instance
  · simp only [lowDegreeEulerCharacteristic, hc, Nat.card_unique, hw, Nat.cast_one, one_mul,
      div_one]

/-- Euler multiplicativity and finiteness extend across the actual coefficient quotient. -/
theorem hasLowDegreeEulerCharacteristic_of_range (hmul : ∀ m n : ℕ, 0 < m → 0 < n →
    w (m * n) = w m * w n)
    (h₃ : ∀ (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A],
      Continuous (fun ga : G × A => A.ρ ga.1 ga.2) → IsZero (((C).obj A).homology 3))
    (A B : TopRep.{u} ℤ G) [Finite A] [Finite B] [DiscreteTopology A] [DiscreteTopology B]
    (f : A ⟶ B) (hf : Function.Injective f)
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (hB : Continuous (fun gb : G × B => B.ρ gb.1 gb.2))
    (hI : hasLowDegreeEulerCharacteristic G w A)
    (hQ : hasLowDegreeEulerCharacteristic G w (coefficientRangeShortComplex ℤ G A B f).X₃) :
    hasLowDegreeEulerCharacteristic G w B := by
  let S := coefficientRangeShortComplex ℤ G A B f
  let T := S.map C
  have hT : T.ShortExact := coefficientRangeContinuousModule_shortExact G A B f hf hA hB
  let : Mono (T.f.f 0) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp hT 0).mono_f
  have hfin (i : ℕ) (hi : i < 3) : Finite (T.X₂.homology i) := by
    let : Finite (T.X₁.homology i) := hI.1 i hi
    let : Finite (T.X₃.homology i) := hQ.1 i hi
    exact (finite_homology_of_shortExact T hT i).1
  let : Finite (T.X₁.homology 0) := hI.1 0 (by decide)
  let : Finite (T.X₁.homology 1) := hI.1 1 (by decide)
  let : Finite (T.X₁.homology 2) := hI.1 2 (by decide)
  let : Finite (T.X₂.homology 0) := hfin 0 (by decide)
  let : Finite (T.X₂.homology 1) := hfin 1 (by decide)
  let : Finite (T.X₂.homology 2) := hfin 2 (by decide)
  let : Finite (T.X₃.homology 0) := hQ.1 0 (by decide)
  let : Finite (T.X₃.homology 1) := hQ.1 1 (by decide)
  let : Finite (T.X₃.homology 2) := hQ.1 2 (by decide)
  let : Module ℤ A := A.hV2
  let : Module ℤ B := B.hV2
  let f₀ := f.hom.toContinuousLinearMap.toLinearMap
  let W := LinearMap.range f₀
  let : Finite (B ⧸ W) := Finite.of_surjective W.mkQ W.mkQ_surjective
  let : Finite S.X₃ := inferInstanceAs (Finite (B ⧸ W))
  have hc : Nat.card B = Nat.card S.X₃ * Nat.card A := by
    change Nat.card B = Nat.card (B ⧸ W) * Nat.card A
    have hW : Nat.card W = Nat.card A :=
      Nat.card_congr (LinearEquiv.ofInjective f₀ hf).symm.toEquiv
    rw [W.card_eq_card_quotient_mul_card, hW, mul_comm]
  refine ⟨hfin, ?_⟩
  change lowDegreeEulerCharacteristic T.X₂ = w (Nat.card B)
  rw [lowDegreeEulerCharacteristic_mul_of_shortExact T hT (h₃ A hA)]
  change lowDegreeEulerCharacteristic ((C).obj A) * lowDegreeEulerCharacteristic ((C).obj S.X₃) = _
  rw [hI.2, hQ.2, hc, hmul _ _ (Nat.card_pos : 0 < Nat.card S.X₃) Nat.card_pos, mul_comm]

/-- The local Euler ratio reduces to its prime-annihilated coefficient cases. -/
theorem hasLowDegreeEulerCharacteristic_of_prime_coefficients
    (hone : w 1 = 1) (hmul : ∀ m n : ℕ, 0 < m → 0 < n → w (m * n) = w m * w n)
    (h₃ : ∀ (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A],
      Continuous (fun ga : G × A => A.ρ ga.1 ga.2) → IsZero (((C).obj A).homology 3))
    (hprime : ∀ (p : ℕ) [Fact p.Prime] (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A],
      Continuous (fun ga : G × A => A.ρ ga.1 ga.2) →
      (∀ a : A, p • a = 0) → hasLowDegreeEulerCharacteristic G w A)
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) :
    hasLowDegreeEulerCharacteristic G w A :=
  finiteCoefficient_of_prime_coefficients G (hasLowDegreeEulerCharacteristic G w)
    (hasLowDegreeEulerCharacteristic_of_subsingleton G w hone)
    (hasLowDegreeEulerCharacteristic_of_range G w hmul h₃) hprime A hA

/-- The trivial coefficient case gives the Euler ratio for finite prime-annihilated
coefficients whose actual action image is a p-group. -/
theorem hasLowDegreeEulerCharacteristic_of_pGroup_image (p : ℕ) [Fact p.Prime]
    (hone : w 1 = 1) (hmul : ∀ m n : ℕ, 0 < m → 0 < n → w (m * n) = w m * w n)
    (h₃ : ∀ (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A],
      Continuous (fun ga : G × A => A.ρ ga.1 ga.2) → IsZero (((C).obj A).homology 3))
    (htriv : hasLowDegreeEulerCharacteristic G w
      (ClassFieldTower.Cohomology.trivialIntegralZModPLifted p G))
    (A : TopRep.{u} ℤ G) [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) (hp : ∀ a : A, p • a = 0)
    (hρ : let _ : Module ℤ A := A.hV2; IsPGroup p A.ρ.toRepresentation.asGroupHom.range) :
    hasLowDegreeEulerCharacteristic G w A :=
  finiteCoefficient_of_pGroup_image G p (hasLowDegreeEulerCharacteristic G w)
    (hasLowDegreeEulerCharacteristic_of_subsingleton G w hone)
    (hasLowDegreeEulerCharacteristic_of_range G w hmul h₃) htriv A hA hp hρ

end TopRep
