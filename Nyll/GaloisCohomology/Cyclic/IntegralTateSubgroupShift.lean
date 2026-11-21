/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.FiniteIndex
public import Nyll.GaloisCohomology.Cyclic.IntegralTateExactness
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTraceVanishing
public import Nyll.GaloisCohomology.GroupTheory.CoinducedShift
public import Nyll.GaloisCohomology.GroupTheory.CoinducedShiftNaturality
public import Nyll.GaloisCohomology.GroupTheory.InducedShift
public import Nyll.GaloisCohomology.GroupTheory.InducedShiftNaturality

/-!
# Restricted integral Tate dimension shifts

The shift sequences are still exact when restricting to a subgroup. The
projection onto one point in each coset proves acyclicity of their middle
terms under this restriction by the original finite-group trace.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] (H : Subgroup G)

/-- Restricting a short exact sequence preserves the actual underlying maps. -/
theorem subgroupRestrict_shortExact {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact) :
    (S.map (Rep.resFunctor H.subtype)).ShortExact := by
  let F := forget₂ (Rep.{v} ℤ G) (ModuleCat.{v} ℤ)
  let F' := forget₂ (Rep.{v} ℤ H) (ModuleCat.{v} ℤ)
  let T := S.map (Rep.resFunctor H.subtype)
  have hT : (T.map F').ShortExact := hS.map_of_exact F
  exact {
    exact := F'.reflects_exact_of_faithful T hT.exact
    mono_f := F'.mono_of_mono_map hT.mono_f
    epi_g := F'.epi_of_epi_map hT.epi_g }

variable [Fintype H]

/-- The original restricted coinduced functions with support projected onto
one chosen point per coset of the subgroup. -/
def subgroupCoindTraceProjection (B : Rep.{u} ℤ (⊥ : Subgroup G)) :
    let C := Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype B)
    C →+ C := by
  intro C
  classical
  exact {
    toFun := fun f => ⟨fun g => if g = (g : G ⧸ H).out then f.val g else 0, by
      intro s g
      have hs : s = 1 := Subsingleton.elim _ _
      subst s
      change (fun h : G => if h = (h : G ⧸ H).out then f.val h else 0) ((1 : G) * g) =
        B.ρ 1 (if g = (g : G ⧸ H).out then f.val g else 0)
      rw [one_mul, map_one, one_apply_eq_self]⟩
    map_add' f b := by
      apply Subtype.ext
      funext g
      change (if g = (g : G ⧸ H).out then f.val g + b.val g else 0) =
        (if g = (g : G ⧸ H).out then f.val g else 0) +
          (if g = (g : G ⧸ H).out then b.val g else 0)
      by_cases hg : g = (g : G ⧸ H).out
      · simp only [ite_eq_left hg]
      · simp only [ite_eq_right hg, zero_add]
    map_zero' := by
      apply Subtype.ext
      funext g
      change (if g = (g : G ⧸ H).out then (0 : B) else 0) = 0
      exact ite_self _ }

/-- Every restricted coinduced function is recovered by the original
subgroup trace of the chosen coset projection. -/
theorem subgroupCoindTraceProjection_trace (B : Rep.{u} ℤ (⊥ : Subgroup G)) :
    let C := Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype B)
    ∀ f : C, f = ∑ h : H, C.ρ h⁻¹ (subgroupCoindTraceProjection H B (C.ρ h f)) := by
  intro C f
  classical
  let p := subgroupCoindTraceProjection H B
  apply Subtype.ext
  funext g
  let q : G ⧸ H := g
  let h₀ : H := ⟨q.out⁻¹ * g, QuotientGroup.eq.mp (QuotientGroup.out_eq' q)⟩
  have term (h : H) : (C.ρ h⁻¹ (p (C.ρ h f))).val g =
      if g * (h : G)⁻¹ = q.out then f.val g else 0 := by
    have he : ((g * (h : G)⁻¹ : G) : G ⧸ H) = q :=
      QuotientGroup.mk_mul_of_mem g (H.inv_mem h.property)
    change (if g * (h : G)⁻¹ = ((g * (h : G)⁻¹ : G) : G ⧸ H).out then
        f.val ((g * (h : G)⁻¹) * (h : G)) else 0) = _
    rw [he, inv_mul_cancel_right]
  have h₀eq : g * (h₀ : G)⁻¹ = q.out := by
    change g * (q.out⁻¹ * g)⁻¹ = q.out
    rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have hother (h : H) (hne : h ≠ h₀) : g * (h : G)⁻¹ ≠ q.out := by
    intro he
    apply hne
    apply Subtype.ext
    calc
      (h : G) = q.out⁻¹ * ((g * (h : G)⁻¹) * (h : G)) := by
        rw [he, inv_mul_cancel_left]
      _ = (h₀ : G) := by
        change q.out⁻¹ * ((g * (h : G)⁻¹) * (h : G)) = q.out⁻¹ * g
        rw [inv_mul_cancel_right]
  let eval : C →+ B := {
    toFun := fun x => x.val g
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  change f.val g = eval (∑ h : H, C.ρ h⁻¹ (p (C.ρ h f)))
  rw [map_sum]
  have hsum : (∑ h : H, eval (C.ρ h⁻¹ (p (C.ρ h f)))) =
      ∑ h : H, if g * (h : G)⁻¹ = q.out then f.val g else 0 :=
    Finset.sum_congr rfl (fun h _ => term h)
  rw [hsum, Finset.sum_eq_single h₀ (fun h _ hn => ite_eq_right (hother h hn))
    (fun hn => (hn (Finset.mem_univ h₀)).elim), ite_eq_left h₀eq]

private def traceProjectionLinear {C : Rep.{u} ℤ H} (p : C →+ C) : C →ₗ[ℤ] C where
  toFun := p
  map_add' := map_add p
  map_smul' z a :=
    (congrArg p (int_smul_eq_zsmul C.hV2 z a)).trans
      ((map_zsmul p z a).trans (int_smul_eq_zsmul C.hV2 z (p a)).symm)

/-- Restriction of a representation coinduced from the trivial subgroup
remains Tate acyclic in every degree. -/
theorem tate_resCoindBot_isZero (B : Rep.{u} ℤ (⊥ : Subgroup G)) (n : ℤ) :
    IsZero (tate (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype B)) n) := by
  let C : Rep.{u} ℤ H := Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype B)
  let p := traceProjectionLinear H (C := C) (subgroupCoindTraceProjection H B)
  have hp (f : C) : f = ∑ h : H, C.ρ h⁻¹ (p (C.ρ h f)) := by
    change f = ∑ h : H, C.ρ h⁻¹ (subgroupCoindTraceProjection H B (C.ρ h f))
    exact subgroupCoindTraceProjection_trace H B f
  exact tate_isZero_of_trace_identity C p hp n

variable [Finite G]

/-- The restriction of the induced middle term vanishes by the original
finite-index comparison, applied before restricting the coefficients. -/
theorem tate_resIndBot_isZero (B : Rep.{u} ℤ (⊥ : Subgroup G)) (n : ℤ) :
    IsZero (tate (Rep.res H.subtype (Rep.ind (⊥ : Subgroup G).subtype B)) n) := by
  classical
  exact (tate_resCoindBot_isZero H B n).of_iso
    ((tateFunctor H n).mapIso ((Rep.resFunctor H.subtype).mapIso (Rep.indCoindIso.{u} B)))

/-- The actual connecting map in the restricted coinduction sequence. -/
def subgroupCoindShiftEquiv (A : Rep.{u} ℤ G) (n : ℤ) :
    tate (Rep.res H.subtype (Rep.coindShiftUp A)) n ≃ₗ[ℤ]
      tate (Rep.res H.subtype A) (n + 1) :=
  tateδEquiv (subgroupRestrict_shortExact H (Rep.coindShiftSequence_shortExact A)) n
    (tate_resCoindBot_isZero H (Rep.res (⊥ : Subgroup G).subtype A) n)
    (tate_resCoindBot_isZero H (Rep.res (⊥ : Subgroup G).subtype A) (n + 1))

/-- The actual connecting map in the restricted induction sequence. -/
def subgroupIndShiftEquiv (A : Rep.{u} ℤ G) (n : ℤ) :
    tate (Rep.res H.subtype A) n ≃ₗ[ℤ]
      tate (Rep.res H.subtype (Rep.indShiftDown A)) (n + 1) :=
  tateδEquiv (subgroupRestrict_shortExact H (Rep.indShiftSequence_shortExact A)) n
    (tate_resIndBot_isZero H (Rep.res (⊥ : Subgroup G).subtype A) n)
    (tate_resIndBot_isZero H (Rep.res (⊥ : Subgroup G).subtype A) (n + 1))

omit [Finite G] in
/-- Naturality of the connecting map in the restricted coinduction sequence. -/
theorem subgroupCoindShiftEquiv_naturality {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n : ℤ)
    (x : tate (Rep.res H.subtype (Rep.coindShiftUp A)) n) :
    (tateFunctor H (n + 1)).map ((Rep.resFunctor H.subtype).map f)
        (subgroupCoindShiftEquiv H A n x) =
      subgroupCoindShiftEquiv H B n ((tateFunctor H n).map
        ((Rep.resFunctor H.subtype).map (Rep.coindShiftUpMap f)) x) :=
  congrArg (fun m : tate (Rep.res H.subtype (Rep.coindShiftUp A)) n ⟶
      tate (Rep.res H.subtype B) (n + 1) => m x)
    (tateδ_naturality
      (subgroupRestrict_shortExact H (Rep.coindShiftSequence_shortExact A))
      (subgroupRestrict_shortExact H (Rep.coindShiftSequence_shortExact B))
      ((Rep.resFunctor H.subtype).mapShortComplex.map (Rep.coindShiftSequenceMap f)) n)

/-- Naturality of the connecting map in the restricted induction sequence. -/
theorem subgroupIndShiftEquiv_naturality {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n : ℤ)
    (x : tate (Rep.res H.subtype A) n) :
    (tateFunctor H (n + 1)).map ((Rep.resFunctor H.subtype).map (Rep.indShiftDownMap f))
        (subgroupIndShiftEquiv H A n x) =
      subgroupIndShiftEquiv H B n ((tateFunctor H n).map ((Rep.resFunctor H.subtype).map f) x) :=
  congrArg (fun m : tate (Rep.res H.subtype A) n ⟶
      tate (Rep.res H.subtype (Rep.indShiftDown B)) (n + 1) => m x)
    (tateδ_naturality
      (subgroupRestrict_shortExact H (Rep.indShiftSequence_shortExact A))
      (subgroupRestrict_shortExact H (Rep.indShiftSequence_shortExact B))
      ((Rep.resFunctor H.subtype).mapShortComplex.map (Rep.indShiftSequenceMap f)) n)

end IntegralGroupCohomology.Universe
