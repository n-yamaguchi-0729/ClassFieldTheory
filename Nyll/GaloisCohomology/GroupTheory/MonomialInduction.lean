/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Group

/-! # Induction from a line in a simple monomial representation -/

@[expose] public section

noncomputable section

open scoped MonoidAlgebra TensorProduct

namespace Representation

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

private theorem monomial_action_mul (g h : G) (x : V) :
    ρ (g * h) x = ρ g (ρ h x) :=
  congrArg (fun f : Module.End k V => f x) (map_mul ρ g h)

private theorem monomial_action_one (x : V) : ρ 1 x = x :=
  congrArg (fun f : Module.End k V => f x) (map_one ρ)

private theorem monomial_action_injective (g : G) : Function.Injective (ρ g) := by
  intro x y h
  have h' := congrArg (ρ g⁻¹) h
  simpa only [← monomial_action_mul ρ, inv_mul_cancel, monomial_action_one ρ] using h'

private theorem monomial_scalar_eq {x : V} (hx : x ≠ 0) {a b : k} (h : a • x = b • x) :
    a = b := by
  apply sub_eq_zero.mp
  have hz : (a - b) • x = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_right hx

private theorem monomial_basis_orbit [IsIrreducible ρ] {J : Type*}
    (b : Module.Basis J k V) (j₀ : J)
    (hmonomial : ∀ g j, ∃ j' : J, ∃ a : k, a ≠ 0 ∧ ρ g (b j) = a • b j') (j : J) :
    ∃ g : G, ∃ a : k, a ≠ 0 ∧ ρ g (b j₀) = a • b j := by
  let O : Set J := {i | ∃ g : G, ∃ a : k, a ≠ 0 ∧ ρ g (b j₀) = a • b i}
  let W₀ := Submodule.span k (b '' O)
  let W : Subrepresentation ρ := {
    toSubmodule := W₀
    apply_mem_toSubmodule := by
      intro g x hx
      have hstable : W₀ ≤ W₀.comap (ρ g) := Submodule.span_le.mpr (by
        rintro _ ⟨i, ⟨h, a, ha, hs⟩, rfl⟩
        obtain ⟨i', c, hc, hi⟩ := hmonomial g i
        have hO : i' ∈ O := ⟨g * h, a * c, mul_ne_zero ha hc, by
          rw [monomial_action_mul, hs, map_smul, hi, smul_smul]⟩
        change ρ g (b i) ∈ W₀
        rw [hi]
        exact W₀.smul_mem c (Submodule.subset_span ⟨i', hO, rfl⟩))
      exact hstable hx }
  have hmem : b j₀ ∈ W := Submodule.subset_span
    ⟨j₀, ⟨1, 1, one_ne_zero, by rw [monomial_action_one, one_smul]⟩, rfl⟩
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left (fun h => by
    rw [h] at hmem
    exact b.ne_zero j₀ ((Submodule.mem_bot (R := k)).mp hmem))
  have hj : b j ∈ W := by
    rw [hW]
    exact Submodule.mem_top
  exact (b.self_mem_span_image.mp hj : j ∈ O)

/-- The original simple monomial module is an actual induced representation of
a scalar character of the stabilizer of a basis line. -/
theorem exists_induced_of_simple_monomial [IsIrreducible ρ] {J : Type*}
    (b : Module.Basis J k V) (j₀ : J)
    (hmonomial : ∀ g j, ∃ j' : J, ∃ a : k, a ≠ 0 ∧ ρ g (b j) = a • b j') :
    ∃ H : Subgroup G, ∃ χ : H →* k,
      Nonempty (Representation.Equiv
        (Representation.ind H.subtype ((Algebra.lsmul k k k).toMonoidHom.comp χ)) ρ) := by
  classical
  let x₀ := b j₀
  have hx₀ : x₀ ≠ 0 := b.ne_zero j₀
  let H : Subgroup G := {
    carrier := {g | ∃ a : k, ρ g x₀ = a • x₀}
    one_mem' := ⟨1, by rw [monomial_action_one, one_smul]⟩
    mul_mem' := fun {g h} ⟨a, ha⟩ ⟨c, hc⟩ => ⟨c * a, by
      rw [monomial_action_mul, hc, map_smul, ha, smul_smul]⟩
    inv_mem' := fun {g} ⟨a, ha⟩ => by
      have ha₀ : a ≠ 0 := fun h => hx₀ (monomial_action_injective ρ g (by
        rw [ha, h, zero_smul, map_zero]))
      have hi := congrArg (ρ g⁻¹) ha
      rw [← monomial_action_mul, inv_mul_cancel, monomial_action_one, map_smul] at hi
      refine ⟨a⁻¹, ?_⟩
      calc
        ρ g⁻¹ x₀ = a⁻¹ • (a • ρ g⁻¹ x₀) := by
          rw [smul_smul, inv_mul_cancel₀ ha₀, one_smul]
        _ = a⁻¹ • x₀ := congrArg (fun x => a⁻¹ • x) hi.symm }
  let χ₀ : H → k := fun s => Classical.choose s.property
  have hχ₀ (s : H) : ρ s.val x₀ = χ₀ s • x₀ := Classical.choose_spec s.property
  let χ : H →* k := {
    toFun := χ₀
    map_one' := monomial_scalar_eq hx₀ (by
      rw [← hχ₀ 1, one_smul]
      exact monomial_action_one ρ x₀)
    map_mul' := fun s t => monomial_scalar_eq hx₀ (by
      rw [← hχ₀ (s * t)]
      change ρ (s.val * t.val) x₀ = (χ₀ s * χ₀ t) • x₀
      rw [monomial_action_mul, hχ₀ t, map_smul, hχ₀ s, smul_smul, mul_comm]) }
  let τ : Representation k H k := (Algebra.lsmul k k k).toMonoidHom.comp χ
  let R := Representation.tprod ((leftRegular k G).comp H.subtype) τ
  let line : k →ₗ[k] V := (LinearMap.id : k →ₗ[k] k).smulRight x₀
  let F₀ : k[G] ⊗[k] k →ₗ[k] V := TensorProduct.lift
    ((MonoidAlgebra.basis G k).constr k (fun g => (ρ g⁻¹).comp line))
  have hF₀ (g : G) (a : k) :
      F₀ (MonoidAlgebra.single g 1 ⊗ₜ[k] a) = ρ g⁻¹ (a • x₀) := by
    dsimp only [F₀]
    rw [TensorProduct.lift.tmul, ← MonoidAlgebra.basis_apply, Module.Basis.constr_basis]
    rfl
  have hR (s : H) : F₀ ∘ₗ R s = F₀ := by
    apply TensorProduct.ext
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext_ring
    apply LinearMap.ext
    intro a
    change F₀ (R s (MonoidAlgebra.single g 1 ⊗ₜ[k] a)) =
      F₀ (MonoidAlgebra.single g 1 ⊗ₜ[k] a)
    change F₀ ((Representation.tprod ((leftRegular k G).comp H.subtype) τ) s
      (MonoidAlgebra.single g 1 ⊗ₜ[k] a)) = _
    rw [Representation.tprod_apply, TensorProduct.map_tmul]
    change F₀ ((leftRegular k G) s.val (MonoidAlgebra.single g 1) ⊗ₜ[k] (χ s * a)) = _
    rw [Representation.ofMulAction_single]
    change F₀ (MonoidAlgebra.single (s.val * g) 1 ⊗ₜ[k] (χ s * a)) = _
    rw [hF₀, hF₀]
    have hs : (χ s * a) • x₀ = ρ s.val (a • x₀) := by
      rw [map_smul, hχ₀ s, smul_smul, mul_comm]
      rfl
    rw [hs, ← monomial_action_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  let F : IndV H.subtype τ →ₗ[k] V := Coinvariants.lift R F₀ hR
  have hF (g : G) (a : k) : F (IndV.mk H.subtype τ g a) = ρ g⁻¹ (a • x₀) :=
    hF₀ g a
  let ge (j : J) : G := Classical.choose (monomial_basis_orbit ρ b j₀ hmonomial j)
  let c (j : J) : k := Classical.choose
    (Classical.choose_spec (monomial_basis_orbit ρ b j₀ hmonomial j))
  have hge (j : J) : c j ≠ 0 ∧ ρ (ge j) x₀ = c j • b j :=
    Classical.choose_spec (Classical.choose_spec (monomial_basis_orbit ρ b j₀ hmonomial j))
  let I : V →ₗ[k] IndV H.subtype τ := b.constr k
    (fun j => IndV.mk H.subtype τ (ge j)⁻¹ (c j)⁻¹)
  have hI (j : J) : I (b j) = IndV.mk H.subtype τ (ge j)⁻¹ (c j)⁻¹ :=
    Module.Basis.constr_basis _ _ _ _
  have hFI : F.comp I = LinearMap.id := by
    apply b.ext
    intro j
    change F (I (b j)) = b j
    rw [hI, hF, inv_inv, map_smul, (hge j).2, smul_smul, inv_mul_cancel₀ (hge j).1,
      one_smul]
  have hIF : I.comp F = LinearMap.id := by
    apply IndV.hom_ext
    intro g
    apply LinearMap.ext_ring
    change I (F (IndV.mk H.subtype τ g 1)) = IndV.mk H.subtype τ g 1
    obtain ⟨j, a, _, h⟩ := hmonomial g⁻¹ j₀
    have hj : ρ g⁻¹ x₀ = a • b j := h
    rw [hF, one_smul, hj, map_smul, hI]
    have hs : ρ ((ge j)⁻¹ * g⁻¹) x₀ = (a / c j) • x₀ := by
      apply monomial_action_injective ρ (ge j)
      rw [← monomial_action_mul, mul_inv_cancel_left, hj, map_smul, (hge j).2,
        smul_smul, div_mul_cancel₀ _ (hge j).1]
    let s : H := ⟨(ge j)⁻¹ * g⁻¹, ⟨a / c j, hs⟩⟩
    have hsχ : χ s = a / c j := monomial_scalar_eq hx₀ ((hχ₀ s).symm.trans hs)
    have hg : s.val⁻¹ * (ge j)⁻¹ = g := by
      change ((ge j)⁻¹ * g⁻¹)⁻¹ * (ge j)⁻¹ = g
      group
    have hgen : IndV.mk H.subtype τ (s.val⁻¹ * (ge j)⁻¹) 1 =
        IndV.mk H.subtype τ (ge j)⁻¹ (χ s) := by
      have h := Coinvariants.mk_inv_tmul ((leftRegular k G).comp H.subtype) τ
        (MonoidAlgebra.single (ge j)⁻¹ 1) 1 s
      change Coinvariants.mk R
        ((leftRegular k G) s.val⁻¹ (MonoidAlgebra.single (ge j)⁻¹ 1) ⊗ₜ[k] (1 : k)) =
        IndV.mk H.subtype τ (ge j)⁻¹ (χ s * 1) at h
      rw [Representation.ofMulAction_single, mul_one] at h
      exact h
    rw [← map_smul, smul_eq_mul, ← div_eq_mul_inv, ← hsχ, ← hgen, hg]
  refine ⟨H, χ, ⟨Representation.Equiv.mk (LinearEquiv.ofLinearMap F I hFI hIF) ?_⟩⟩
  intro s
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext_ring
  change F (Representation.ind H.subtype τ s (IndV.mk H.subtype τ g 1)) =
    ρ s (F (IndV.mk H.subtype τ g 1))
  rw [Representation.ind_mk, hF, hF, mul_inv_rev, inv_inv, monomial_action_mul]

end Representation
