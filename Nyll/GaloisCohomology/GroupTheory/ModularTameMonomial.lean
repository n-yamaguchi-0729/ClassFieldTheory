/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.Group
public import Nyll.GaloisCohomology.GroupTheory.FinitePGroupInvariants

/-! # Simple representations and tame cyclic layers -/

@[expose] public section

noncomputable section

namespace Representation

open Polynomial

variable {G V : Type*} [Group G] [AddCommGroup V]

/-- A normal `p`-subgroup acts trivially on a simple finite representation in characteristic `p`.
The nonzero fixed vector lies in an invariant subspace for the whole group. -/
theorem isTrivial_restrict_of_normal_isPGroup_charP
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p] [Module k V] [Finite V]
    [Nontrivial V] (ρ : Representation k G V) [IsIrreducible ρ]
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) (g : P) (v : V) :
    ρ g.val v = v := by
  let ρP : Representation k P V := ρ.comp P.subtype
  let σ : Representation ℤ P V := {
    toFun := fun a => (ρP a).restrictScalars ℤ
    map_one' := LinearMap.ext (fun x => congrArg (fun f : Module.End k V => f x) (map_one ρP))
    map_mul' := fun a b => LinearMap.ext (fun x =>
      congrArg (fun f : Module.End k V => f x) (map_mul ρP a b)) }
  have hp (x : V) : p • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]
  let W : Subrepresentation ρ :=
    { toSubmodule := Representation.invariants ρP
      apply_mem_toSubmodule := by
        intro a x hx
        apply (Representation.mem_invariants ρP _).mpr
        intro b
        let c : P := ⟨a⁻¹ * b.val * a,
          Subgroup.Normal.conj_mem' inferInstance b.val b.property a⟩
        have hc : ρ c.val x = x := (Representation.mem_invariants ρP x).mp hx c
        change ρ b.val (ρ a x) = ρ a x
        rw [← mul_apply_eq_comp, ← map_mul]
        have hba : b.val * a = a * c.val := by
          change b.val * a = a * (a⁻¹ * b.val * a)
          rw [mul_assoc, mul_inv_cancel_left]
        rw [hba, map_mul, mul_apply_eq_comp, hc] }
  obtain ⟨x, hx, hfix⟩ := exists_nonzero_fixed_of_isPGroup_int σ hP hp
  have hxW : x ∈ W := (Representation.mem_invariants ρP x).mpr hfix
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left (fun hw => by
    rw [hw] at hxW
    change x ∈ (⊥ : Submodule k V) at hxW
    exact hx ((Submodule.mem_bot (R := k)).mp hxW))
  have hv : v ∈ W := by
    rw [hW]
    exact Submodule.mem_top
  exact (Representation.mem_invariants ρP v).mp hv g

/-- In characteristic `p`, the wild subgroup acts trivially in particular over `ZMod p`. -/
theorem isTrivial_restrict_of_normal_isPGroup
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) V] [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod p) G V) [IsIrreducible ρ]
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) (g : P) (v : V) :
    ρ g.val v = v :=
  isTrivial_restrict_of_normal_isPGroup_charP ρ P hP g v

section Tame

variable {k : Type*} [Field k] [Module k V] (ρ : Representation k G V)

/-- The simultaneous scalar eigenspace for a character of the inertia subgroup. -/
def characterEigenspace (I : Subgroup G) (χ : I →* k) : Submodule k V :=
  ⨅ i : I, Module.End.eigenspace (ρ i.val) (χ i)

theorem mem_characterEigenspace (I : Subgroup G) (χ : I →* k) (x : V) :
    x ∈ characterEigenspace ρ I χ ↔ ∀ i : I, ρ i.val x = χ i • x := by
  simp only [characterEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

private theorem tameAction_mul (g h : G) (x : V) :
    ρ (g * h) x = ρ g (ρ h x) :=
  congrArg (fun f : Module.End k V => f x) (map_mul ρ g h)

private theorem tameAction_one (x : V) : ρ 1 x = x :=
  congrArg (fun f : Module.End k V => f x) (map_one ρ)

private theorem tameAction_injective (g : G) : Function.Injective (ρ g) := by
  intro x y h
  have hx := congrArg (ρ g⁻¹) h
  simpa only [← tameAction_mul ρ, inv_mul_cancel, tameAction_one ρ] using hx

private theorem tame_eq_of_smul_eq {x : V} (hx : x ≠ 0) {a b : k} (h : a • x = b • x) :
    a = b := by
  apply sub_eq_zero.mp
  exact (smul_eq_zero.mp (by rw [sub_smul, h, sub_self] : (a - b) • x = 0)).resolve_right hx

private theorem tameAction_pow_of_eigen (g : G) (x : V) (ev : k) (hx : ρ g x = ev • x)
    (m : ℕ) : ρ (g ^ m) x = ev ^ m • x := by
  induction m with
  | zero => rw [pow_zero, pow_zero, one_smul, tameAction_one]
  | succ m ih =>
    rw [pow_succ', pow_succ', tameAction_mul, ih, map_smul, hx, smul_smul, mul_comm]

/-- Finite cyclic inertia has a nonzero weight space whenever its generator has an
eigenvalue over the coefficient field. -/
theorem exists_characterEigenspace_of_cyclic
    {I : Subgroup G} [Finite I] (i₀ : I) (hi₀ : ∀ i : I, i ∈ Subgroup.zpowers i₀)
    (ev : k) (hev : Module.End.HasEigenvalue (ρ i₀.val) ev) :
    ∃ χ : I →* k, characterEigenspace ρ I χ ≠ ⊥ := by
  classical
  let E := Module.End.eigenspace (ρ i₀.val) ev
  obtain ⟨x, hxE, hx⟩ := (Submodule.ne_bot_iff E).mp hev
  have hall (i : I) : ∃ b : k, ∀ y : V, y ∈ E → ρ i.val y = b • y := by
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff i i₀).mp
      (mem_powers_iff_mem_zpowers.mpr (hi₀ i))
    have hval : i₀.val ^ m = i.val := congrArg Subtype.val hm
    refine ⟨ev ^ m, fun y hy => ?_⟩
    rw [← hval]
    exact tameAction_pow_of_eigen ρ i₀.val y ev (Module.End.mem_eigenspace_iff.mp hy) m
  let χ₀ : I → k := fun i => Classical.choose (hall i)
  have hχ (i : I) (y : V) (hy : y ∈ E) : ρ i.val y = χ₀ i • y :=
    Classical.choose_spec (hall i) y hy
  let χ : I →* k := {
    toFun := χ₀
    map_one' := tame_eq_of_smul_eq hx ((hχ 1 x hxE).symm.trans
      ((tameAction_one ρ x).trans (one_smul k x).symm))
    map_mul' := fun i j => tame_eq_of_smul_eq hx (by
      rw [← hχ (i * j) x hxE]
      change ρ (i.val * j.val) x = (χ₀ i * χ₀ j) • x
      rw [tameAction_mul, hχ j x hxE, map_smul, hχ i x hxE, smul_smul, mul_comm]) }
  refine ⟨χ, Submodule.ne_bot_iff _ |>.mpr ⟨x, ?_, hx⟩⟩
  exact (mem_characterEigenspace ρ I χ x).mpr (fun i => hχ i x hxE)

variable (I : Subgroup G) [I.Normal]

/-- The actual inverse conjugation on the normal inertia subgroup. -/
def inverseConjugationOnSubgroup (g : G) : I →* I where
  toFun i := ⟨g⁻¹ * i.val * g, Subgroup.Normal.conj_mem' inferInstance i.val i.property g⟩
  map_one' := Subtype.ext (by change g⁻¹ * 1 * g = 1; group)
  map_mul' i j := Subtype.ext (by
    change g⁻¹ * (i.val * j.val) * g = (g⁻¹ * i.val * g) * (g⁻¹ * j.val * g)
    group)

theorem inverseConjugationOnSubgroup_mul (g h : G) (i : I) :
    inverseConjugationOnSubgroup I (g * h) i =
      inverseConjugationOnSubgroup I h (inverseConjugationOnSubgroup I g i) := by
  apply Subtype.ext
  change (g * h)⁻¹ * i.val * (g * h) = h⁻¹ * (g⁻¹ * i.val * g) * h
  group

/-- The subgroup fixing the character of inertia under conjugation. -/
def inertiaCharacterStabilizer (χ : I →* k) : Subgroup G where
  carrier := {g | ∀ i : I, χ (inverseConjugationOnSubgroup I g i) = χ i}
  one_mem' := by
    intro i
    congr 1
    apply Subtype.ext
    change (1 : G)⁻¹ * i.val * 1 = i.val
    group
  mul_mem' {g h} hg hh := by
    intro i
    rw [inverseConjugationOnSubgroup_mul, hh, hg]
  inv_mem' {g} hg := by
    intro i
    have h := hg (inverseConjugationOnSubgroup I g⁻¹ i)
    have hconj : inverseConjugationOnSubgroup I g
        (inverseConjugationOnSubgroup I g⁻¹ i) = i := by
      apply Subtype.ext
      change g⁻¹ * ((g⁻¹)⁻¹ * i.val * g⁻¹) * g = i.val
      group
    rw [hconj] at h
    exact h.symm

open scoped IsMulCommutative in
theorem inertia_le_characterStabilizer [IsCyclic I] (χ : I →* k) :
    I ≤ inertiaCharacterStabilizer I χ := by
  intro g hg i
  congr 1
  let g' : I := ⟨g, hg⟩
  change g'⁻¹ * i * g' = i
  rw [mul_comm g'⁻¹ i, mul_assoc, inv_mul_cancel, mul_one]

theorem tameAction_characterEigenspace (χ : I →* k) (g : G) {x : V}
    (hx : x ∈ characterEigenspace ρ I χ) :
    ρ g x ∈ characterEigenspace ρ I (χ.comp (inverseConjugationOnSubgroup I g)) := by
  apply (mem_characterEigenspace ρ I _ _).mpr
  intro i
  let j := inverseConjugationOnSubgroup I g i
  have hj : i.val * g = g * j.val := by
    change i.val * g = g * (g⁻¹ * i.val * g)
    group
  change ρ i.val (ρ g x) = χ j • ρ g x
  rw [← tameAction_mul, hj, tameAction_mul, (mem_characterEigenspace ρ I χ x).mp hx j, map_smul]

theorem inertiaCharacterStabilizer_preserves_eigenspace (χ : I →* k)
    (g : inertiaCharacterStabilizer I χ) {x : V} (hx : x ∈ characterEigenspace ρ I χ) :
    ρ g.val x ∈ characterEigenspace ρ I χ := by
  have he : χ.comp (inverseConjugationOnSubgroup I g.val) = χ :=
    MonoidHom.ext g.property
  simpa only [he] using tameAction_characterEigenspace ρ I χ g.val hx

private theorem tameEndomorphism_exists_eigenvalue {W : Type*} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [Nontrivial W] (f : Module.End k W) {n : ℕ} (hn : 0 < n)
    (hpow : f ^ n = 1) (hsplit : Splits ((X : k[X]) ^ n - C 1)) : ∃ ev, f.HasEigenvalue ev := by
  have hdiv : minpoly k f ∣ (X : k[X]) ^ n - C 1 := by
    apply minpoly.dvd k f
    rw [map_sub, aeval_X_pow, hpow, aeval_C, map_one, sub_self]
  have hmin := hsplit.of_dvd (X_pow_sub_C_ne_zero hn 1) hdiv
  obtain ⟨ev, hev⟩ := hmin.exists_eval_eq_zero
    (minpoly.degree_pos (Algebra.IsIntegral.isIntegral f)).ne'
  exact ⟨ev, Module.End.hasEigenvalue_of_isRoot hev⟩

/-- A character weight over split coefficients has a nonzero line fixed by the
character stabilizer whenever the quotient by cyclic inertia is cyclic. -/
theorem exists_stabilizer_eigenline [Finite G] [IsCyclic I] [IsCyclic (G ⧸ I)]
    [FiniteDimensional k V] (hsplit : Splits ((X : k[X]) ^ Nat.card G - C 1)) (χ : I →* k)
    (hχ : characterEigenspace ρ I χ ≠ ⊥) :
    ∃ v : V, v ∈ characterEigenspace ρ I χ ∧ v ≠ 0 ∧
      ∀ g : inertiaCharacterStabilizer I χ, ∃ c : k, ρ g.val v = c • v := by
  let H := inertiaCharacterStabilizer I χ
  let q := (QuotientGroup.mk' I).comp H.subtype
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := q.range)
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp c.property
  have hgen (g : H) : ∃ m : ℕ, ∃ a : I, g.val = t.val ^ m * a.val := by
    let d : q.range := ⟨q g, ⟨g, rfl⟩⟩
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff d c).mp
      (mem_powers_iff_mem_zpowers.mpr (hc d))
    have hm' : (QuotientGroup.mk' I) (t.val ^ m) = (QuotientGroup.mk' I) g.val := by
      rw [map_pow]
      change q t ^ m = q g
      rw [ht]
      exact congrArg Subtype.val hm
    let a : I := ⟨(t.val ^ m)⁻¹ * g.val, QuotientGroup.eq.mp hm'⟩
    exact ⟨m, a, (mul_inv_cancel_left (t.val ^ m) g.val).symm⟩
  let E := characterEigenspace ρ I χ
  obtain ⟨x, hxE, hxn⟩ := (Submodule.ne_bot_iff E).mp hχ
  let : Nontrivial E := ⟨⟨⟨x, hxE⟩, 0, fun h => hxn (congrArg Subtype.val h)⟩⟩
  have htE (y : V) (hy : y ∈ E) : ρ t.val y ∈ E :=
    inertiaCharacterStabilizer_preserves_eigenspace ρ I χ t hy
  let f : Module.End k E := (ρ t.val).restrict htE
  have hf : f ^ Nat.card G = 1 := by
    change ((ρ t.val).restrict htE)^ Nat.card G = 1
    rw [Module.End.pow_restrict]
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    change ((ρ t.val) ^ Nat.card G) y.val = y.val
    rw [← map_pow, pow_card_eq_one', tameAction_one]
  obtain ⟨ev, hev⟩ := tameEndomorphism_exists_eigenvalue f Nat.card_pos hf hsplit
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hv₀ : v.val ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have htV : ρ t.val v.val = ev • v.val := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨v.val, v.property, hv₀, fun g => ?_⟩
  obtain ⟨m, a, hga⟩ := hgen g
  refine ⟨χ a * ev ^ m, ?_⟩
  rw [hga, tameAction_mul, (mem_characterEigenspace ρ I χ v.val).mp v.property a, map_smul,
    tameAction_pow_of_eigen ρ t.val v.val ev htV m, smul_smul]

/-- An irreducible representation of a finite group with cyclic normal inertia and
cyclic quotient has a basis whose lines are permuted by the group over any coefficient
field splitting the group order power polynomial. Each line is an inertia weight. -/
theorem exists_tameMonomialBasis_of_splits [Finite G] [IsCyclic I] [IsCyclic (G ⧸ I)]
    [FiniteDimensional k V] [Nontrivial V] [IsIrreducible ρ]
    (hsplit : Splits ((X : k[X]) ^ Nat.card G - C 1)) :
    ∃ S : Set k, ∃ b : Module.Basis S k V,
      (∀ g : G, ∀ j : S, ∃ j' : S, ∃ c : k, c ≠ 0 ∧ ρ g (b j) = c • b j') ∧
      ∃ i₀ : I, (∀ i : I, i ∈ Subgroup.zpowers i₀) ∧
        ∀ j : S, ρ i₀.val (b j) = j.val • b j := by
  classical
  obtain ⟨i₀, hi₀⟩ := IsCyclic.exists_generator (α := I)
  have hpow : (ρ i₀.val) ^ Nat.card G = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  obtain ⟨ev, hev⟩ := tameEndomorphism_exists_eigenvalue _ Nat.card_pos hpow hsplit
  obtain ⟨χ, hχ⟩ := exists_characterEigenspace_of_cyclic ρ i₀ hi₀ ev hev
  obtain ⟨v, hvχ, hv₀, hvH⟩ := exists_stabilizer_eigenline ρ I hsplit χ hχ
  let w : G → k := fun g => χ (inverseConjugationOnSubgroup I g i₀)
  let S := Set.range w
  let a : S → G := fun j => Classical.choose j.property
  have ha (j : S) : w (a j) = j.val := Classical.choose_spec j.property
  let b₀ : S → V := fun j => ρ (a j) v
  have hvOrbit (g : G) : ρ g v ≠ 0 := fun h =>
    hv₀ (tameAction_injective ρ g (h.trans (map_zero (ρ g)).symm))
  have hb (j : S) : ρ i₀.val (b₀ j) = j.val • b₀ j := by
    have h := (mem_characterEigenspace ρ I _ _).mp
      (tameAction_characterEigenspace ρ I χ (a j) hvχ) i₀
    change ρ i₀.val (b₀ j) = w (a j) • b₀ j at h
    rwa [ha j] at h
  have hlinear : LinearIndependent k b₀ :=
    Module.End.eigenvectors_linearIndependent (ρ i₀.val) S b₀ (fun j =>
      Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hb j), hvOrbit (a j)⟩)
  have hstabilizer (g h : G) (hgh : w g = w h) :
      h⁻¹ * g ∈ inertiaCharacterStabilizer I χ := by
    have hall (i : I) : χ (inverseConjugationOnSubgroup I g i) =
        χ (inverseConjugationOnSubgroup I h i) := by
      obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff i i₀).mp
        (mem_powers_iff_mem_zpowers.mpr (hi₀ i))
      calc
        χ (inverseConjugationOnSubgroup I g i) = w g ^ m := by rw [← hm, map_pow, map_pow]
        _ = w h ^ m := congrArg (fun x : k => x ^ m) hgh
        _ = χ (inverseConjugationOnSubgroup I h i) := by rw [← hm, map_pow, map_pow]
    intro i
    rw [inverseConjugationOnSubgroup_mul, hall]
    congr 1
    apply Subtype.ext
    change h⁻¹ * ((h⁻¹)⁻¹ * i.val * h⁻¹) * h = i.val
    group
  have horbit (g : G) : ∃ j : S, ∃ c : k, c ≠ 0 ∧ ρ g v = c • b₀ j := by
    let j : S := ⟨w g, ⟨g, rfl⟩⟩
    let σ : inertiaCharacterStabilizer I χ :=
      ⟨(a j)⁻¹ * g, hstabilizer g (a j) (ha j).symm⟩
    obtain ⟨c, hc⟩ := hvH σ
    have hg : g = a j * σ.val := by
      change g = a j * ((a j)⁻¹ * g)
      group
    have h : ρ g v = c • b₀ j := by
      rw [hg, tameAction_mul, hc, map_smul]
    refine ⟨j, c, ?_, h⟩
    intro hc₀
    exact hvOrbit g (h.trans (by rw [hc₀, zero_smul]))
  have hperm (g : G) (j : S) :
      ∃ j' : S, ∃ c : k, c ≠ 0 ∧ ρ g (b₀ j) = c • b₀ j' := by
    change ∃ j' : S, ∃ c : k, c ≠ 0 ∧ ρ g (ρ (a j) v) = c • b₀ j'
    rw [← tameAction_mul]
    exact horbit (g * a j)
  let W₀ := Submodule.span k (Set.range b₀)
  let W : Subrepresentation ρ := {
    toSubmodule := W₀
    apply_mem_toSubmodule := by
      intro g x hx
      have hstable : W₀ ≤ W₀.comap (ρ g) := Submodule.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        obtain ⟨j', c, _, hc⟩ := hperm g j
        change ρ g (b₀ j) ∈ W₀
        rw [hc]
        exact W₀.smul_mem c (Submodule.subset_span ⟨j', rfl⟩))
      exact hstable hx }
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left (fun h => by
    let j : S := ⟨w 1, ⟨1, rfl⟩⟩
    have hmem : b₀ j ∈ W := Submodule.subset_span ⟨j, rfl⟩
    rw [h] at hmem
    change b₀ j ∈ (⊥ : Submodule k V) at hmem
    exact hvOrbit (a j) ((Submodule.mem_bot (R := k)).mp hmem))
  have hspan : (⊤ : Submodule k V) ≤ W₀ := by
    intro x hx
    change x ∈ W
    rw [hW]
    exact hx
  let b : Module.Basis S k V := Module.Basis.mk hlinear hspan
  refine ⟨S, b, fun g j => ?_, i₀, hi₀, fun j => ?_⟩
  · simpa only [b, Module.Basis.mk_apply] using hperm g j
  · simpa only [b, Module.Basis.mk_apply] using hb j

/-- In particular the monomial basis exists over algebraically closed coefficients. -/
theorem exists_tameMonomialBasis [Finite G] [IsCyclic I] [IsCyclic (G ⧸ I)]
    [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] [IsIrreducible ρ] :
    ∃ S : Set k, ∃ b : Module.Basis S k V,
      (∀ g : G, ∀ j : S, ∃ j' : S, ∃ c : k, c ≠ 0 ∧ ρ g (b j) = c • b j') ∧
      ∃ i₀ : I, (∀ i : I, i ∈ Subgroup.zpowers i₀) ∧
        ∀ j : S, ρ i₀.val (b j) = j.val • b j :=
  exists_tameMonomialBasis_of_splits ρ I (IsAlgClosed.splits _)

omit [Group G] in
/-- The power polynomial for a finite group splits in its finite splitting extension. -/
theorem splits_tameGroupPowerPolynomial (k : Type*) [Field k] :
    let F := ((X : k[X]) ^ Nat.card G - C 1).SplittingField
    Splits ((X : F[X]) ^ Nat.card G - C 1) := by
  let P : k[X] := (X : k[X]) ^ Nat.card G - C 1
  let F := P.SplittingField
  change Splits ((X : F[X]) ^ Nat.card G - C 1)
  have h := Polynomial.SplittingField.splits P
  change Splits (((X : k[X]) ^ Nat.card G - C 1).map (algebraMap k F)) at h
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_one] at h
  exact h

end Tame

/-- A simple representation with a trivial normal-subgroup action is
monomial when its quotient has cyclic normal inertia and cyclic residue quotient. -/
theorem exists_tameMonomialBasis_of_ker_le
    {k : Type*} [Field k] [Module k V]
    [Finite G] [Nontrivial V] [FiniteDimensional k V]
    (ρ : Representation k G V) [IsIrreducible ρ]
    (P : Subgroup G) [P.Normal] (hker : P ≤ ρ.ker)
    (T : Subgroup (G ⧸ P)) [T.Normal] [IsCyclic T] [IsCyclic ((G ⧸ P) ⧸ T)]
    (hsplit : Splits ((X : k[X]) ^ Nat.card (G ⧸ P) - C 1)) :
    ∃ S : Set k, ∃ b : Module.Basis S k V,
      ∀ g : G, ∀ j : S, ∃ j' : S, ∃ c : k, c ≠ 0 ∧ ρ g (b j) = c • b j' := by
  let σ : Representation k (G ⧸ P) V := QuotientGroup.lift P ρ hker
  have hσ (g : G) : σ ((QuotientGroup.mk' P) g) = ρ g := QuotientGroup.lift_mk' P hker g
  have hnontrivial : Nontrivial (Subrepresentation σ) := by
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    refine ⟨⟨⊥, ⊤, fun h => hx ?_⟩⟩
    have htop : x ∈ (⊤ : Subrepresentation σ) := Submodule.mem_top
    rw [← h] at htop
    exact (Submodule.mem_bot (R := k)).mp (show x ∈ (⊥ : Submodule k V) from htop)
  let : IsIrreducible σ := {
    toNontrivial := hnontrivial
    eq_bot_or_eq_top := fun W => by
      let W' : Subrepresentation ρ := {
        toSubmodule := W.toSubmodule
        apply_mem_toSubmodule := by
          intro g x hx
          rw [← hσ g]
          exact W.apply_mem_toSubmodule ((QuotientGroup.mk' P) g) hx }
      rcases eq_bot_or_eq_top W' with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective
          (congrArg (fun X : Subrepresentation ρ => X.toSubmodule) h))
      · exact Or.inr (Subrepresentation.toSubmodule_injective
          (congrArg (fun X : Subrepresentation ρ => X.toSubmodule) h)) }
  obtain ⟨S, b, hmonomial, _⟩ := exists_tameMonomialBasis_of_splits σ T hsplit
  refine ⟨S, b, fun g j => ?_⟩
  simpa only [hσ g] using hmonomial ((QuotientGroup.mk' P) g) j

/-- After quotienting by a normal `p`-subgroup, a simple representation in
characteristic `p` has a monomial basis if its tame quotient has cyclic
normal inertia and cyclic residue quotient. -/
theorem exists_tameMonomialBasis_of_normal_isPGroup
    {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [CharP k p] [Module k V]
    [Finite G] [Finite V] [Nontrivial V] [FiniteDimensional k V]
    (ρ : Representation k G V) [IsIrreducible ρ]
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (T : Subgroup (G ⧸ P)) [T.Normal] [IsCyclic T] [IsCyclic ((G ⧸ P) ⧸ T)]
    (hsplit : Splits ((X : k[X]) ^ Nat.card (G ⧸ P) - C 1)) :
    ∃ S : Set k, ∃ b : Module.Basis S k V,
      ∀ g : G, ∀ j : S, ∃ j' : S, ∃ c : k, c ≠ 0 ∧ ρ g (b j) = c • b j' := by
  have hker : P ≤ ρ.ker := fun g hg => MonoidHom.mem_ker.mpr
    (LinearMap.ext (fun x => isTrivial_restrict_of_normal_isPGroup_charP ρ P hP ⟨g, hg⟩ x))
  exact exists_tameMonomialBasis_of_ker_le ρ P hker T hsplit

end Representation
