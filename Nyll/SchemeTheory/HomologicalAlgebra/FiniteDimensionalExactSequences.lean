/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LinearMap_finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Tactic.Ext
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SimpRw

/-!
# Linear Map finite Dimensional ker and quotient range of exact of finite Dimensional
-/

section LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional

universe u v

theorem _root_.LinearMap.finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional
    {k : Type u} [Field k]
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type v}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃)
    (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂)
    (h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂)
    [FiniteDimensional k (LinearMap.ker d₂)] [FiniteDimensional k (B₂ ⧸ LinearMap.range d₂)]
    [FiniteDimensional k (LinearMap.ker d₃)] :
    FiniteDimensional k (LinearMap.ker d₁) ∧ FiniteDimensional k (B₁ ⧸ LinearMap.range d₁) := by
  classical
  have hc₁ : ∀ a, g₁ (d₁ a) = d₂ (f₁ a) := fun a => congrArg (fun φ : A₁ →ₗ[k] B₂ => φ a) h₁
  have hc₂ : ∀ a, g₂ (d₂ a) = d₃ (f₂ a) := fun a => congrArg (fun φ : A₂ →ₗ[k] B₃ => φ a) h₂
  refine ⟨?_, ?_⟩
  · let ι : LinearMap.ker d₁ →ₗ[k] LinearMap.ker d₂ :=
      LinearMap.codRestrict _ (f₁ ∘ₗ (LinearMap.ker d₁).subtype) fun a => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← hc₁,
          LinearMap.mem_ker.mp a.2,
          map_zero]
    have hι : Function.Injective ι := by
      intro a b h
      apply Subtype.ext
      apply hf₁
      exact congrArg Subtype.val h
    exact Module.Finite.of_injective ι hι
  · have hle : LinearMap.range d₁ ≤ (LinearMap.range d₂).comap g₁ := by
      rintro _ ⟨a, rfl⟩
      exact ⟨f₁ a, (hc₁ a).symm⟩
    let φ : (B₁ ⧸ LinearMap.range d₁) →ₗ[k] (B₂ ⧸ LinearMap.range d₂) := Submodule.mapQ _ _ g₁ hle
    obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective f₂ (LinearMap.range_eq_top.mpr
      hf₂)
    have hσ' : ∀ c, f₂ (σ c) = c := fun c => congrArg (fun ψ : A₃ →ₗ[k] A₃ => ψ c) hσ
    let e := LinearEquiv.ofInjective g₁ hg₁
    have hker : ∀ a : A₂, d₃ (f₂ a) = 0 → d₂ a ∈ LinearMap.range g₁ := by
      intro a ha
      have : g₂ (d₂ a) = 0 := by rw [hc₂, ha]
      obtain ⟨b, hb⟩ := (hg (d₂ a)).mp this
      exact ⟨b, hb⟩
    let pre : LinearMap.ker d₃ →ₗ[k] LinearMap.range g₁ :=
      LinearMap.codRestrict _ (d₂ ∘ₗ σ ∘ₗ (LinearMap.ker d₃).subtype) fun c =>
        hker _ (by
          rw [LinearMap.comp_apply, Submodule.subtype_apply, hσ']
          exact LinearMap.mem_ker.mp c.2)
    let Λ : LinearMap.ker d₃ →ₗ[k] (B₁ ⧸ LinearMap.range d₁) :=
      (LinearMap.range d₁).mkQ ∘ₗ e.symm.toLinearMap ∘ₗ pre
    have hkerφ : LinearMap.ker φ ≤ LinearMap.range Λ := by
      intro q hq
      obtain ⟨b₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [LinearMap.mem_ker] at hq
      change Submodule.Quotient.mk (g₁ b₁) = (0 : B₂ ⧸ LinearMap.range d₂) at hq
      rw [Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨a₂, ha₂⟩ := hq
      have hc : d₃ (f₂ a₂) = 0 := by rw [← hc₂, ha₂, (hg (g₁ b₁)).mpr ⟨b₁, rfl⟩]
      refine ⟨⟨f₂ a₂, LinearMap.mem_ker.mpr hc⟩, ?_⟩
      obtain ⟨a₁, ha₁⟩ := (hf (σ (f₂ a₂) - a₂)).mp (by rw [map_sub, hσ', sub_self])
      have hd : d₂ (σ (f₂ a₂)) = g₁ (b₁ + d₁ a₁) := by
        rw [map_add, hc₁, ha₁, map_sub, ha₂]; abel
      have hpre : (pre ⟨f₂ a₂, LinearMap.mem_ker.mpr hc⟩ : LinearMap.range g₁) = ⟨g₁ (b₁ + d₁ a₁),
        b₁ + d₁ a₁, rfl⟩ := by
        apply Subtype.ext
        change d₂ (σ (f₂ a₂)) = g₁ (b₁ + d₁ a₁)
        exact hd
      have he : e.symm ⟨g₁ (b₁ + d₁ a₁), b₁ + d₁ a₁, rfl⟩ = b₁ + d₁ a₁ := by
        apply e.injective
        rw [LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [LinearEquiv.ofInjective_apply]
      change (LinearMap.range d₁).mkQ (e.symm (pre ⟨f₂ a₂, _⟩)) = Submodule.Quotient.mk b₁
      rw [hpre, he, Submodule.mkQ_apply, Submodule.Quotient.mk_add,
        (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self d₁ a₁), add_zero]
    have : Module.Finite k (LinearMap.range Λ) := inferInstance
    have hkfg : (LinearMap.ker φ).FG := (Module.Finite.iff_fg.mp (Module.Finite.of_injective
      (Submodule.inclusion hkerφ) (Submodule.inclusion_injective hkerφ)))
    have hrfg : ((⊤ : Submodule k (B₁ ⧸ LinearMap.range d₁)).map φ).FG :=
      IsNoetherian.noetherian _
    have htop : (⊤ : Submodule k (B₁ ⧸ LinearMap.range d₁)).FG :=
      Submodule.fg_of_fg_map_of_fg_inf_ker φ hrfg (by rw [top_inf_eq]; exact hkfg)
    exact ⟨htop⟩
end LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional

section LinearMap_finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso

/-!
# Linear Map finrank ker eq and finrank add finrank eq of quasi Iso
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.LinearMapFinrankKerFinrankAdd

universe u v

theorem _root_.LinearMap.finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso
    {A : Type u} [Field A]
    (K : ℕ → Type v) [∀ i, AddCommGroup (K i)] [∀ i, Module A (K i)] [∀ i, Module.Finite A (K i)]
    (δ : ∀ i, K i →ₗ[A] K (i + 1))
    (C : ℕ → Type v) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)] (d : ∀ i, C i →ₗ[A] C (i + 1))
    (φ : ∀ i, K i →ₗ[A] C i) (hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
    (h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
    (h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
    (hinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 → φ (i + 1) x ∈ LinearMap.range (d i) →
      x ∈ LinearMap.range (δ i))
    (hsurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
      ∃ x : K (i + 1), δ (i + 1) x = 0 ∧ φ (i + 1) x - y ∈ LinearMap.range (d i)) :
    Module.finrank A ↥(LinearMap.ker (d 0)) = Module.finrank A ↥(LinearMap.ker (δ 0)) ∧
      ∀ (i : ℕ) (H : Type v) [AddCommGroup H] [Module A H] (ψ : ↥(LinearMap.ker (d (i + 1))) →ₗ[A]
        H),
        Function.Surjective ψ →
        LinearMap.ker ψ = (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype →
        Module.finrank A H +
            Module.finrank A ↥((LinearMap.range (δ i)).comap (LinearMap.ker (δ (i + 1))).subtype) =
          Module.finrank A ↥(LinearMap.ker (δ (i + 1))) := by
  classical
  have hφ' : ∀ (i : ℕ) (x : K i), d i (φ i x) = φ (i + 1) (δ i x) := fun i x =>
    congrArg (fun f => f x) (hφ i) |>.trans rfl
  refine ⟨?_, ?_⟩
  · let e0 : ↥(LinearMap.ker (δ 0)) →ₗ[A] ↥(LinearMap.ker (d 0)) :=
      LinearMap.codRestrict (LinearMap.ker (d 0))
        ((φ 0).domRestrict (LinearMap.ker (δ 0))) fun x => by
          change d 0 (φ 0 x.1) = 0
          rw [hφ' 0, LinearMap.mem_ker.mp x.2, map_zero]
    have hinj0 : Function.Injective e0 := by
      intro x y hxy
      apply Subtype.ext
      have h := congrArg Subtype.val hxy
      change φ 0 x.1 = φ 0 y.1 at h
      have : x.1 - y.1 = 0 := h0inj (x.1 - y.1)
        (by rw [map_sub, LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2, sub_zero])
        (by rw [map_sub, h, sub_self])
      exact sub_eq_zero.mp this
    have hsurj0 : Function.Surjective e0 := by
      intro y
      obtain ⟨x, hx, hxy⟩ := h0surj y.1 (LinearMap.mem_ker.mp y.2)
      exact ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, Subtype.ext hxy⟩
    exact (LinearEquiv.ofBijective e0 ⟨hinj0, hsurj0⟩).finrank_eq.symm
  · intro i H _ _ ψ hψ hker
    let r : ↥(LinearMap.ker (δ (i + 1))) →ₗ[A] ↥(LinearMap.ker (d (i + 1))) :=
      LinearMap.codRestrict (LinearMap.ker (d (i + 1)))
        ((φ (i + 1)).domRestrict (LinearMap.ker (δ (i + 1)))) fun x => by
          change d (i + 1) (φ (i + 1) x.1) = 0
          rw [hφ' (i + 1), LinearMap.mem_ker.mp x.2, map_zero]
    let Φ : ↥(LinearMap.ker (δ (i + 1))) →ₗ[A] H := ψ ∘ₗ r
    have hΦsurj : Function.Surjective Φ := by
      intro h
      obtain ⟨y, rfl⟩ := hψ h
      obtain ⟨x, hx, hxy⟩ := hsurj i y.1 (LinearMap.mem_ker.mp y.2)
      refine ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, ?_⟩
      change ψ (r ⟨x, _⟩) = ψ y
      rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, hker, Submodule.mem_comap]
      exact hxy
    have hΦker : LinearMap.ker Φ = (LinearMap.range (δ i)).comap (LinearMap.ker (δ (i +
      1))).subtype := by
      ext x
      rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
      change ψ (r x) = 0 ↔ x.1 ∈ LinearMap.range (δ i)
      rw [← LinearMap.mem_ker, hker, Submodule.mem_comap, Submodule.coe_subtype]
      change φ (i + 1) x.1 ∈ LinearMap.range (d i) ↔ x.1 ∈ LinearMap.range (δ i)
      constructor
      · exact hinj i x.1 (LinearMap.mem_ker.mp x.2)
      · rintro ⟨z, hz⟩
        exact ⟨φ i z, by rw [hφ' i, hz]⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    rw [LinearMap.range_eq_top.mpr hΦsurj, finrank_top, hΦker] at hrn
    exact hrn
end AlgebraicCurves.Foundations.Algebra.Proofs.LinearMapFinrankKerFinrankAdd
end ProofImplementation

end LinearMap_finrank_ker_eq_and_finrank_add_finrank_eq_of_quasiIso

section LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact

/-!
Relate kernel and cokernel dimensions along an exact sequence.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact

namespace C2EulerCharAux

open Function

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [DivisionRing k]
  {M : Type u₁} {N : Type u₂} {P : Type u₃}
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup P] [Module k P]

lemma finiteDimensional_of_exact {f : M →ₗ[k] N} {g : N →ₗ[k] P} (h : Exact f g)
    [FiniteDimensional k M] [FiniteDimensional k P] : FiniteDimensional k N :=
  Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict]; exact h.linearMap_ker_eq))
    g.surjective_rangeRestrict

lemma finrank_eq_of_exact {f : M →ₗ[k] N} {g : N →ₗ[k] P} (h : Exact f g)
    [FiniteDimensional k N] :
    Module.finrank k N
      = Module.finrank k (LinearMap.range f) + Module.finrank k (LinearMap.range g) := by
  rw [← g.finrank_range_add_finrank_ker, h.linearMap_ker_eq, add_comm]

end C2EulerCharAux

universe u v

open C2EulerCharAux in
theorem _root_.LinearMap.finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
    {k : Type u} [Field k]
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type v}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃)
    (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂)
    [FiniteDimensional k (LinearMap.ker d₁)] [FiniteDimensional k (B₁ ⧸ LinearMap.range d₁)]
    [FiniteDimensional k (LinearMap.ker d₃)] [FiniteDimensional k (B₃ ⧸ LinearMap.range d₃)] :
    FiniteDimensional k (LinearMap.ker d₂) ∧ FiniteDimensional k (B₂ ⧸ LinearMap.range d₂) ∧
    (Module.finrank k (LinearMap.ker d₂) : ℤ) - Module.finrank k (B₂ ⧸ LinearMap.range d₂)
      = ((Module.finrank k (LinearMap.ker d₁) : ℤ) - Module.finrank k (B₁ ⧸ LinearMap.range d₁))
        + ((Module.finrank k (LinearMap.ker d₃) : ℤ) - Module.finrank k (B₃ ⧸ LinearMap.range
          d₃)) := by
  have h₁' : ∀ x, g₁ (d₁ x) = d₂ (f₁ x) := fun x => LinearMap.congr_fun h₁ x
  have h₂' : ∀ x, g₂ (d₂ x) = d₃ (f₂ x) := fun x => LinearMap.congr_fun h₂ x
  have hF₁ : ∀ x ∈ LinearMap.ker d₁, f₁ x ∈ LinearMap.ker d₂ := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← h₁', hx, map_zero]
  have hF₂ : ∀ x ∈ LinearMap.ker d₂, f₂ x ∈ LinearMap.ker d₃ := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← h₂', hx, map_zero]
  let F₁ : LinearMap.ker d₁ →ₗ[k] LinearMap.ker d₂ := f₁.restrict hF₁
  let F₂ : LinearMap.ker d₂ →ₗ[k] LinearMap.ker d₃ := f₂.restrict hF₂
  have hG₁ : LinearMap.range d₁ ≤ (LinearMap.range d₂).comap g₁ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨f₁ a, (h₁' a).symm⟩
  have hG₂ : LinearMap.range d₂ ≤ (LinearMap.range d₃).comap g₂ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨f₂ a, (h₂' a).symm⟩
  let G₁ : (B₁ ⧸ LinearMap.range d₁) →ₗ[k] (B₂ ⧸ LinearMap.range d₂) :=
    (LinearMap.range d₁).mapQ (LinearMap.range d₂) g₁ hG₁
  let G₂ : (B₂ ⧸ LinearMap.range d₂) →ₗ[k] (B₃ ⧸ LinearMap.range d₃) :=
    (LinearMap.range d₂).mapQ (LinearMap.range d₃) g₂ hG₂
  let δ : LinearMap.ker d₃ →ₗ[k] (B₁ ⧸ LinearMap.range d₁) :=
    SnakeLemma.δ' d₁ d₂ d₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
      (LinearMap.ker d₃).subtype (LinearMap.exact_subtype_ker_map d₃)
      (LinearMap.range d₁).mkQ (LinearMap.exact_map_mkQ_range d₁) hf₂ hg₁
  have eF₁ : Function.Injective F₁ := fun x y hxy =>
    Subtype.ext (hf₁ (by simpa [F₁] using congrArg Subtype.val hxy))
  have eK₂ : Function.Exact F₁ F₂ := by
    intro x
    constructor
    · intro hx
      have hx' : f₂ (x : A₂) = 0 := by simpa [F₂] using congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (hf _).mp hx'
      have hy' : y ∈ LinearMap.ker d₁ := by
        rw [LinearMap.mem_ker]
        apply hg₁
        rw [h₁', hy, map_zero]
        exact x.2
      exact ⟨⟨y, hy'⟩, Subtype.ext (by simpa [F₁] using hy)⟩
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simp [F₁, F₂, hf.apply_apply_eq_zero]
  have eK₃ : Function.Exact F₂ δ :=
    SnakeLemma.exact_δ'_right d₁ d₂ d₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
      (LinearMap.ker d₂).subtype (LinearMap.exact_subtype_ker_map d₂)
      (LinearMap.ker d₃).subtype (LinearMap.exact_subtype_ker_map d₃)
      (LinearMap.range d₁).mkQ (LinearMap.exact_map_mkQ_range d₁) hf₂ hg₁
      F₂ (by ext; rfl) (LinearMap.ker d₃).injective_subtype
  have eC₁ : Function.Exact δ G₁ :=
    SnakeLemma.exact_δ'_left d₁ d₂ d₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
      (LinearMap.ker d₃).subtype (LinearMap.exact_subtype_ker_map d₃)
      (LinearMap.range d₁).mkQ (LinearMap.exact_map_mkQ_range d₁)
      (LinearMap.range d₂).mkQ (LinearMap.exact_map_mkQ_range d₂) hf₂ hg₁
      G₁ (Submodule.mapQ_mkQ _ _ _) (Submodule.mkQ_surjective _)
  have eC₂ : Function.Exact G₁ G₂ := by
    intro c
    constructor
    · intro hy
      obtain ⟨y, rfl⟩ := (LinearMap.range d₂).mkQ_surjective c
      have hy' : g₂ y ∈ LinearMap.range d₃ := by
        simpa [G₂, Submodule.mapQ_apply] using hy
      obtain ⟨z, hz⟩ := hy'
      obtain ⟨w, rfl⟩ := hf₂ z
      have hv : y - d₂ w ∈ LinearMap.range g₁ := by
        rw [← hg.linearMap_ker_eq, LinearMap.mem_ker, map_sub, h₂', hz, sub_self]
      obtain ⟨v, hv⟩ := hv
      refine ⟨(LinearMap.range d₁).mkQ v, ?_⟩
      simp only [G₁, Submodule.mkQ_apply, Submodule.mapQ_apply, hv]
      rw [Submodule.Quotient.eq]
      exact ⟨-w, by rw [map_neg, sub_sub_cancel_left]⟩
    · rintro ⟨c', rfl⟩
      obtain ⟨v, rfl⟩ := (LinearMap.range d₁).mkQ_surjective c'
      simp [G₁, G₂, Submodule.mapQ_apply, hg.apply_apply_eq_zero]
  have eG₂ : Function.Surjective G₂ := by
    intro c
    obtain ⟨z, rfl⟩ := (LinearMap.range d₃).mkQ_surjective c
    obtain ⟨y, rfl⟩ := hg₂ z
    exact ⟨(LinearMap.range d₂).mkQ y, by simp [G₂, Submodule.mapQ_apply]⟩
  have iK₂ : FiniteDimensional k (LinearMap.ker d₂) := finiteDimensional_of_exact eK₂
  have iC₂ : FiniteDimensional k (B₂ ⧸ LinearMap.range d₂) := finiteDimensional_of_exact eC₂
  refine ⟨iK₂, iC₂, ?_⟩
  have n₁ : Module.finrank k (LinearMap.ker d₁) = Module.finrank k (LinearMap.range F₁) :=
    (LinearMap.finrank_range_of_inj eF₁).symm
  have n₂ := finrank_eq_of_exact eK₂
  have n₃ := finrank_eq_of_exact eK₃
  have n₄ := finrank_eq_of_exact eC₁
  have n₅ := finrank_eq_of_exact eC₂
  have n₆ : Module.finrank k (B₃ ⧸ LinearMap.range d₃) = Module.finrank k (LinearMap.range G₂) := by
    rw [LinearMap.range_eq_top.2 eG₂, finrank_top]
  omega
end LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end LinearMap_finrank_ker_sub_finrank_quotient_range_eq_add_of_exact

section LinearMap_nonempty_kerModRange_equiv_of_equiv_comm

/-!
# Linear Map nonempty ker Mod Range equiv of equiv comm
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace LinearMap_nonempty_kerModRange_equiv_of_equiv_comm

universe u v w

namespace LinearMap
open _root_.LinearMap

section KerModRange

variable {R : Type u} [CommRing R] {C : ℕ → Type v} {C' : ℕ → Type w}
  [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
  (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x))

include he

theorem kerModRange_map_ker (i : ℕ) :
    (LinearMap.ker (d i)).map (e i : C i →ₗ[R] C' i) = LinearMap.ker (d' i) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he, hx, map_zero]
  · intro hy
    refine ⟨(e i).symm y, ?_, (e i).apply_symm_apply y⟩
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hy, map_zero]

/-- The kernel equivalence induced by a commuting family of componentwise linear equivalences. -/
def kerEquivOfComm (i : ℕ) : LinearMap.ker (d i) ≃ₗ[R] LinearMap.ker (d' i) :=
  ((e i).submoduleMap (LinearMap.ker (d i))).trans (LinearEquiv.ofEq _ _ (kerModRange_map_ker d d'
    e he i))

theorem kerEquivOfComm_apply (i : ℕ) (x : LinearMap.ker (d i)) :
    ((kerEquivOfComm d d' e he i x : LinearMap.ker (d' i)) : C' i) = e i x := rfl

theorem kerModRange_map_comap (i : ℕ) :
    ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype).map
        (kerEquivOfComm d d' e he (i + 1) : LinearMap.ker (d (i + 1)) →ₗ[R] LinearMap.ker (d' (i +
          1)))
      = (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range,
    LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, ⟨w, hw⟩, rfl⟩
    refine ⟨e i w, ?_⟩
    rw [kerEquivOfComm_apply, ← he, hw]
  · rintro ⟨w, hw⟩
    refine ⟨(kerEquivOfComm d d' e he (i + 1)).symm y, ⟨(e i).symm w, ?_⟩,
      (kerEquivOfComm d d' e he (i + 1)).apply_symm_apply y⟩
    have h1 : ((kerEquivOfComm d d' e he (i + 1)).symm y : C (i + 1))
        = (e (i + 1)).symm (y : C' (i + 1)) := by
      apply (e (i + 1)).injective
      rw [LinearEquiv.apply_symm_apply, ← kerEquivOfComm_apply d d' e he,
        LinearEquiv.apply_symm_apply]
    rw [h1]
    apply (e (i + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hw]

theorem nonempty_kerModRange_equiv_of_equiv_comm' :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i +
         1))).subtype)) :=
  ⟨⟨kerEquivOfComm d d' e he 0⟩, fun i =>
    ⟨Submodule.Quotient.equiv _ _ (kerEquivOfComm d d' e he (i + 1)) (kerModRange_map_comap d d' e
      he i)⟩⟩

end KerModRange

end LinearMap

theorem _root_.LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    {R : Type u} [CommRing R] {C C' : ℕ → Type u}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C'
      i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
    (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x)) :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i +
         1))).subtype)) :=
  LinearMap.nonempty_kerModRange_equiv_of_equiv_comm' d d' e he
end AlgebraicCurves.Foundations.Algebra.Proofs.LinearMap_nonempty_kerModRange_equiv_of_equiv_comm
end ProofImplementation

end LinearMap_nonempty_kerModRange_equiv_of_equiv_comm

section LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact

/-!
# Linear Map sum neg one pow mul finrank eq zero of exact
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact

open Module

universe u v

namespace P2mLES

variable {k : Type u} [DivisionRing k]

theorem finrank_eq_range_add_ker {M N : Type v} [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N]
    [Module.Finite k M] (f : M →ₗ[k] N) :
    finrank k M = finrank k (LinearMap.range f) + finrank k (LinearMap.ker f) :=
  (LinearMap.finrank_range_add_finrank_ker f).symm

theorem main
    (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, Module.Finite k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, Module.Finite k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, Module.Finite k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hf0 : Function.Injective (f 0))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (N : ℕ) (hN : Subsingleton (A N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
        ((finrank k (A i) : ℤ) - finrank k (B i) + finrank k (C i)) = 0 := by
  set a : ℕ → ℕ := fun i => finrank k (LinearMap.range (f i)) with ha
  set b : ℕ → ℕ := fun i => finrank k (LinearMap.range (g i)) with hb
  set r : ℕ → ℕ := fun i => finrank k (LinearMap.range (δ i)) with hr
  have hB : ∀ i, finrank k (B i) = b i + a i := fun i => by
    rw [finrank_eq_range_add_ker (g i), (LinearMap.exact_iff.mp (hfg i))]
  have hC : ∀ i, finrank k (C i) = r i + b i := fun i => by
    rw [finrank_eq_range_add_ker (δ i), (LinearMap.exact_iff.mp (hgδ i))]
  have hA : ∀ i, finrank k (A (i + 1)) = a (i + 1) + r i := fun i => by
    rw [finrank_eq_range_add_ker (f (i + 1)), (LinearMap.exact_iff.mp (hδf i))]
  have hA0 : finrank k (A 0) = a 0 := by
    rw [finrank_eq_range_add_ker (f 0), LinearMap.ker_eq_bot.mpr hf0, finrank_bot, add_zero]
  set t : ℕ → ℤ := fun i => Nat.rec (motive := fun _ => ℤ) 0 (fun j _ => (r j : ℤ)) i with ht
  have ht0 : t 0 = 0 := rfl
  have htS : ∀ i, t (i + 1) = r i := fun i => rfl
  have hterm : ∀ i, ((finrank k (A i) : ℤ) - finrank k (B i) + finrank k (C i)) = t i + t (i + 1)
    := by
    intro i
    cases i with
    | zero =>
      rw [hA0, hB 0, hC 0, ht0, htS]
      push_cast
      ring
    | succ j =>
      rw [hA j, hB (j + 1), hC (j + 1), htS, htS]
      push_cast
      ring
  have htel : ∀ i, (-1 : ℤ) ^ i * (t i + t (i + 1))
      = (-1 : ℤ) ^ i * t i - (-1 : ℤ) ^ (i + 1) * t (i + 1) := fun i => by
    rw [pow_succ]
    ring
  simp_rw [hterm, htel]
  rw [Finset.sum_range_sub' (fun i => (-1 : ℤ) ^ i * t i) N, ht0, mul_zero, zero_sub, neg_eq_zero]
  cases N with
  | zero => rw [ht0, mul_zero]
  | succ m =>
    rw [htS]
    have : r m = 0 := by
      simp only [hr]
      have : Subsingleton (LinearMap.range (δ m)) := inferInstance
      exact Module.finrank_zero_of_subsingleton
    rw [this, Nat.cast_zero, mul_zero]

end P2mLES

theorem _root_.LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact
    {k : Type u} [DivisionRing k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, Module.Finite k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, Module.Finite k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, Module.Finite k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hf0 : Function.Injective (f 0))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (N : ℕ) (hN : Subsingleton (A N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
        ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) = 0 :=
  P2mLES.main A B C f g δ hf0 hfg hgδ hδf N hN
end LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact
