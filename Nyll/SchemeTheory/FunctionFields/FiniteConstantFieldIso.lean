/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Recovering the original field map and its finite constants

An additive extension of a multiplicative field map makes the original map
additive through the literal field inclusions. For finite constant fields of
the same cardinality, the original scalar images are exactly the roots of
`X ^ q - X`, so the same field isomorphism determines a unique scalar
isomorphism. Neither step replaces the original multiplicative map.
-/

@[expose] public section

noncomputable section

namespace FieldTheory

universe u₁ u₂ v₁ v₂ w₁ w₂

/-- Additivity descends along the actual field embeddings, retaining the
given multiplicative map on every original element. -/
def ringEquivOfMultiplicativeExtension
    {F₁ : Type v₁} {F₂ : Type v₂} {L₁ : Type w₁} {L₂ : Type w₂}
    [Field F₁] [Field F₂] [Field L₁] [Field L₂]
    (φ : F₁ ≃* F₂) (i₁ : F₁ →+* L₁) (i₂ : F₂ →+* L₂)
    (Φ : L₁ ≃+* L₂) (hΦ : ∀ a, Φ (i₁ a) = i₂ (φ a)) : F₁ ≃+* F₂ :=
  { φ with
    map_add' := fun a b => by
      apply i₂.injective
      calc
        i₂ (φ (a + b)) = Φ (i₁ (a + b)) := (hΦ (a + b)).symm
        _ = Φ (i₁ a) + Φ (i₁ b) := by rw [map_add, map_add]
        _ = i₂ (φ a) + i₂ (φ b) := by rw [hΦ a, hΦ b]
        _ = i₂ (φ a + φ b) := (map_add i₂ _ _).symm }

/-- The specified finite scalar field is characterized inside any field
extension by its cardinality polynomial. -/
theorem mem_base_iff_pow_natCard
    (k : Type u₁) (F : Type v₁) [Field k] [Finite k] [Field F]
    [Algebra k F] (x : F) :
    x ∈ (algebraMap k F).range ↔ x ^ Nat.card k = x := by
  let _ : Fintype k := Fintype.ofFinite k
  rw [← Fintype.card_eq_nat_card]
  constructor
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have hs : (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial k).Splits := by
      rw [Polynomial.splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
        ← Finset.card_def, Finset.card_univ,
        FiniteField.X_pow_card_sub_X_natDegree_eq k Fintype.one_lt_card]
    apply hs.mem_range_of_isRoot
      (FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card)
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero] using hx

/-- Two embeddings of finite fields of equal cardinality into the same
field have the same literal image: both images are the roots of the same
cardinality polynomial. -/
theorem finiteFieldEmbedding_range_eq_of_natCard_eq
    {A : Type u₁} {B : Type u₂} {Ω : Type v₁}
    [Field A] [Finite A] [Field B] [Finite B] [Field Ω]
    (f : A →+* Ω) (g : B →+* Ω) (hcard : Nat.card A = Nat.card B) :
    f.range = g.range := by
  let : Algebra A Ω := f.toAlgebra
  let : Algebra B Ω := g.toAlgebra
  apply Subring.ext
  intro x
  change x ∈ (algebraMap A Ω).range ↔ x ∈ (algebraMap B Ω).range
  rw [mem_base_iff_pow_natCard, mem_base_iff_pow_natCard, hcard]

/-- A field isomorphism transports the specified finite scalar fields of
equal cardinality and determines their scalar isomorphism uniquely. -/
theorem exists_unique_finiteConstantRingEquiv
    {k₁ : Type u₁} {k₂ : Type u₂} {F₁ : Type v₁} {F₂ : Type v₂}
    [Field k₁] [Finite k₁] [Field k₂] [Finite k₂]
    [Field F₁] [Field F₂] [Algebra k₁ F₁] [Algebra k₂ F₂]
    (hcard : Nat.card k₁ = Nat.card k₂) (φ : F₁ ≃+* F₂) :
    ∃! σ : k₁ ≃+* k₂,
      ∀ a, φ (algebraMap k₁ F₁ a) = algebraMap k₂ F₂ (σ a) := by
  have hex (a : k₁) : ∃ b : k₂,
      algebraMap k₂ F₂ b = φ (algebraMap k₁ F₁ a) := by
    apply (mem_base_iff_pow_natCard k₂ F₂ _).mpr
    have ha := (mem_base_iff_pow_natCard k₁ F₁ (algebraMap k₁ F₁ a)).mp ⟨a, rfl⟩
    rw [← hcard, ← map_pow, ha]
  let m : k₁ → k₂ := fun a => Classical.choose (hex a)
  have hm (a : k₁) : algebraMap k₂ F₂ (m a) = φ (algebraMap k₁ F₁ a) :=
    Classical.choose_spec (hex a)
  have hinj : Function.Injective m := by
    intro a b hab
    apply (algebraMap k₁ F₁).injective
    apply φ.injective
    rw [← hm a, ← hm b, hab]
  have hsurj : Function.Surjective m := by
    intro b
    have hb := (mem_base_iff_pow_natCard k₂ F₂ (algebraMap k₂ F₂ b)).mp ⟨b, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : k₁,
        algebraMap k₁ F₁ a = φ.symm (algebraMap k₂ F₂ b) := by
      apply (mem_base_iff_pow_natCard k₁ F₁ _).mpr
      rw [hcard, ← map_pow, hb]
    refine ⟨a, ?_⟩
    apply (algebraMap k₂ F₂).injective
    rw [hm a, ha, RingEquiv.apply_symm_apply]
  let σ : k₁ ≃+* k₂ :=
    { toEquiv := Equiv.ofBijective m ⟨hinj, hsurj⟩
      map_mul' := fun a b => by
        apply (algebraMap k₂ F₂).injective
        calc
          algebraMap k₂ F₂ (m (a * b)) =
              φ (algebraMap k₁ F₁ (a * b)) := hm (a * b)
          _ = φ (algebraMap k₁ F₁ a) * φ (algebraMap k₁ F₁ b) := by
            rw [map_mul, map_mul]
          _ = algebraMap k₂ F₂ (m a) * algebraMap k₂ F₂ (m b) := by
            rw [hm a, hm b]
          _ = algebraMap k₂ F₂ (m a * m b) := (map_mul _ _ _).symm
      map_add' := fun a b => by
        apply (algebraMap k₂ F₂).injective
        calc
          algebraMap k₂ F₂ (m (a + b)) =
              φ (algebraMap k₁ F₁ (a + b)) := hm (a + b)
          _ = φ (algebraMap k₁ F₁ a) + φ (algebraMap k₁ F₁ b) := by
            rw [map_add, map_add]
          _ = algebraMap k₂ F₂ (m a) + algebraMap k₂ F₂ (m b) := by
            rw [hm a, hm b]
          _ = algebraMap k₂ F₂ (m a + m b) := (map_add _ _ _).symm }
  refine ⟨σ, fun a => (hm a).symm, fun τ hτ => ?_⟩
  apply RingEquiv.ext
  intro a
  apply (algebraMap k₂ F₂).injective
  exact (hτ a).symm.trans (hm a).symm

end FieldTheory
