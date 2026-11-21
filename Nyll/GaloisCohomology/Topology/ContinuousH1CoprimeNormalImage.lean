/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.LocallyConstant.Basic
public import Nyll.GaloisCohomology.Topology.ContinuousH1CocycleSurjectivity

/-! # Continuous degree one with coprime normal images -/

@[expose] public section

open scoped BigOperators Topology
open CategoryTheory ContRepresentation TopRep

noncomputable section

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : TopRep.{u} ℤ G)

/-- The translation and linear action belonging to one original crossed homomorphism. -/
def crossedAffineValue (c : CrossedHom A) (g : G) (a : A) : A := c.toFun g + A.ρ g a

omit [IsTopologicalGroup G] in
/-- The identity acts as the identity affine map. -/
theorem crossedAffineValue_one (c : CrossedHom A) (a : A) :
    crossedAffineValue A c 1 a = a := by
  unfold crossedAffineValue
  rw [c.map_one, map_one, one_apply_eq_self, zero_add]

omit [IsTopologicalGroup G] in
/-- The cocycle relation gives composition of affine maps. -/
theorem crossedAffineValue_mul (c : CrossedHom A) (g h : G) (a : A) :
    crossedAffineValue A c (g * h) a = crossedAffineValue A c g (crossedAffineValue A c h a) := by
  unfold crossedAffineValue
  have hρ : A.ρ (g * h) a = A.ρ g (A.ρ h a) := DFunLike.congr_fun (map_mul A.ρ g h) a
  rw [c.map_mul, hρ, map_add, add_assoc]

/-- Realize the original cocycle and its coefficient action together as affine permutations. -/
def crossedAffinePerm (c : CrossedHom A) : G →* Equiv.Perm A where
  toFun g := {
    toFun := crossedAffineValue A c g
    invFun := crossedAffineValue A c g⁻¹
    left_inv a := (crossedAffineValue_mul A c g⁻¹ g a).symm.trans
      (by rw [inv_mul_cancel, crossedAffineValue_one])
    right_inv a := (crossedAffineValue_mul A c g g⁻¹ a).symm.trans
      (by rw [mul_inv_cancel, crossedAffineValue_one]) }
  map_one' := Equiv.ext (crossedAffineValue_one A c)
  map_mul' g h := Equiv.ext (crossedAffineValue_mul A c g h)

omit [IsTopologicalGroup G] in
/-- A cocycle with finite discrete coefficients induces a locally constant permutation action. -/
theorem crossedAffinePerm_locallyConstant [Finite A] [DiscreteTopology A]
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) (c : CrossedHom A) :
    IsLocallyConstant (crossedAffinePerm A c) := by
  have hc : Continuous (fun g : G => fun a : A => crossedAffinePerm A c g a) := by
    apply continuous_pi
    intro a
    exact c.continuous_toFun.add (hA.comp (continuous_id.prodMk continuous_const))
  have h := (IsLocallyConstant.iff_continuous _).mpr hc
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  obtain ⟨W, hW, hg, hconst⟩ := h.exists_open g
  exact ⟨W, hW, hg, fun x hx => Equiv.ext (congrFun (hconst x hx))⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem nsmul_bijective_of_coprime_finite_torsion [Finite A]
    (p n : ℕ) [Fact p.Prime] (hpA : ∀ a : A, p • a = 0) (hn : ¬ p ∣ n) :
    Function.Bijective (fun a : A => n • a) := by
  let : Module (ZMod p) A := AddCommGroup.zmodModule hpA
  let : Fintype A := Fintype.ofFinite A
  have hcard : Nat.card A = p ^ Module.finrank (ZMod p) A := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have h : (Nat.card A).Coprime n := by
    rw [hcard]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn).pow_left _
  exact Nat.Coprime.nsmul_right_bijective h

omit [IsTopologicalGroup G] in
/-- Averaging over the finite affine image produces a primitive on the actual subgroup. -/
theorem crossedHom_primitive_on_coprimeAffineImage [Finite A] (N : Subgroup G)
    (p : ℕ) [Fact p.Prime] (hpA : ∀ a : A, p • a = 0) (c : CrossedHom A)
    (hcard : ¬ p ∣ Nat.card (((crossedAffinePerm A c).comp N.subtype).range)) :
    ∃ b : A, ∀ g : N, c.toFun g.val = A.ρ g.val b - b := by
  let φ := (crossedAffinePerm A c).comp N.subtype
  let Q := φ.range
  let : Fintype Q := Fintype.ofFinite Q
  let d := Fintype.card Q
  have hd : ¬ p ∣ d := by
    change ¬ p ∣ Fintype.card Q
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let s : A := ∑ q : Q, q.val (0 : A)
  have hsum (g : N) : s = d • c.toFun g.val + A.ρ g.val s := by
    let qg : Q := ⟨φ g, ⟨g, rfl⟩⟩
    have hperm : (∑ q : Q, (qg * q).val (0 : A)) = s :=
      Fintype.sum_equiv (Equiv.mulLeft qg) _ _ (fun _ => rfl)
    calc
      s = ∑ q : Q, (qg * q).val (0 : A) := hperm.symm
      _ = ∑ q : Q, (c.toFun g.val + A.ρ g.val (q.val (0 : A))) := rfl
      _ = d • c.toFun g.val + A.ρ g.val s := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum]
  have hi := nsmul_bijective_of_coprime_finite_torsion A p d hpA hd
  obtain ⟨b, hb₀⟩ := hi.2 (-s)
  have hb : d • b = -s := hb₀
  refine ⟨b, fun g => hi.1 ?_⟩
  change d • c.toFun g.val = d • (A.ρ g.val b - b)
  rw [nsmul_sub, ← map_nsmul, hb, map_neg]
  exact (eq_sub_iff_add_eq.mpr (hsum g).symm).trans (by abel)

omit [IsTopologicalGroup G] in
/-- A primitive on a normal subgroup with zero invariants already trivializes
the original crossed homomorphism on the whole group. -/
theorem crossedHom_primitive_of_normal_noInvariants (N : Subgroup G) [N.Normal]
    (hfix : ∀ a : A, (∀ h : N, A.ρ h.val a = a) → a = 0) (c : CrossedHom A) (b : A)
    (hb : ∀ h : N, c.toFun h.val = A.ρ h.val b - b) :
    ∀ g : G, c.toFun g = A.ρ g b - b := by
  let v (g : G) := c.toFun g - (A.ρ g b - b)
  have hv (g h : G) : v (g * h) = v g + A.ρ g (v h) := by
    have hρ : A.ρ (g * h) b = A.ρ g (A.ρ h b) := DFunLike.congr_fun (map_mul A.ρ g h) b
    dsimp only [v]
    rw [c.map_mul, hρ, map_sub, map_sub]
    abel
  have hn (g : N) : v g.val = 0 := sub_eq_zero.mpr (hb g)
  intro g
  apply sub_eq_zero.mp
  apply hfix (v g)
  intro h
  let k : N := ⟨g⁻¹ * h.val * g, Subgroup.Normal.conj_mem' inferInstance h.val h.property g⟩
  have hk : h.val * g = g * k.val := by
    change h.val * g = g * (g⁻¹ * h.val * g)
    rw [mul_assoc, mul_inv_cancel_left]
  have h₁ : v (h.val * g) = A.ρ h.val (v g) := by rw [hv, hn h, zero_add]
  have h₂ : v (g * k.val) = v g := by rw [hv, hn k, map_zero, add_zero]
  exact h₁.symm.trans ((congrArg v hk).trans h₂)

private theorem oneCocycle_eq_zero_of_primitive
    (hcont : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (z : cocycles A 1) (b : A)
    (hb : ∀ g : G, (crossedHomOfCocycle A z).toFun g = A.ρ g b - b) : π A 1 z = 0 := by
  let C := homogeneousCochains A
  let f : C(G, A) := ⟨fun g => A.ρ g b, hcont.comp (continuous_id.prodMk continuous_const)⟩
  let t : C.X 0 := ⟨f, by
    intro g
    apply ContinuousMap.ext
    intro h
    change A.ρ g (A.ρ (g⁻¹ * h) b) = A.ρ h b
    have hm := DFunLike.congr_fun (map_mul A.ρ g (g⁻¹ * h)) b
    rw [mul_inv_cancel_left] at hm
    exact hm.symm⟩
  have hd : C.d 0 1 t = C.iCycles 1 z := by
    apply Subtype.ext
    ext g h
    have he := congrArg (fun w => w g h) (homogeneousCochains.d_apply A 0 t)
    change (C.d 0 1 t).val g h = (C.iCycles 1 z).val g h
    rw [he, homogeneous_oneCocycle_eq_difference, hb g, hb h]
    change A.ρ h b - A.ρ g b = (A.ρ h b - b) - (A.ρ g b - b)
    abel
  have ht : C.toCycles 0 1 t = z := by
    let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
    let i := F.map (C.iCycles 1)
    apply (ModuleCat.mono_iff_injective i).mp inferInstance
    exact (ConcreteCategory.congr_hom (C.toCycles_i 0 1) t).trans hd
  change C.homologyπ 1 z = 0
  rw [← ht]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 0 1) t

/-- Continuous first cohomology vanishes when the actual cocycle images on a
normal subgroup have order prime to the coefficient prime and there are no
nonzero vectors fixed by that subgroup. -/
theorem continuousH1_eq_zero_of_normal_coprimeAffineImages [Finite A] (N : Subgroup G) [N.Normal]
    (p : ℕ) [Fact p.Prime] (hpA : ∀ a : A, p • a = 0)
    (hcont : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (hfix : ∀ a : A, (∀ g : N, A.ρ g.val a = a) → a = 0)
    (hcard : ∀ c : CrossedHom A, ¬ p ∣ Nat.card ((crossedAffinePerm A c).comp N.subtype).range)
    (x : continuousCohomology 1 A) : x = 0 := by
  obtain ⟨z, rfl⟩ := π_surjective A 1 x
  let c := crossedHomOfCocycle A z
  obtain ⟨b, hb⟩ := crossedHom_primitive_on_coprimeAffineImage A N p hpA c (hcard c)
  exact oneCocycle_eq_zero_of_primitive A hcont z b
    (crossedHom_primitive_of_normal_noInvariants A N hfix c b hb)

/-- A finite normal subgroup of order prime to the coefficient prime can be
averaged directly through the images of the original affine actions. -/
theorem continuousH1_eq_zero_of_normal_finiteCoprime [Finite A] (N : Subgroup G)
    [N.Normal] [Finite N] (p : ℕ) [Fact p.Prime] (hpA : ∀ a : A, p • a = 0)
    (hcont : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (hfix : ∀ a : A, (∀ g : N, A.ρ g.val a = a) → a = 0)
    (hN : ¬ p ∣ Nat.card N) (x : continuousCohomology 1 A) : x = 0 := by
  apply continuousH1_eq_zero_of_normal_coprimeAffineImages A N p hpA hcont hfix _ x
  intro c hc
  let f := (crossedAffinePerm A c).comp N.subtype
  have hd : Nat.card f.range ∣ Nat.card N :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv) ▸
      Subgroup.card_quotient_dvd_card f.ker
  exact hN (hc.trans hd)

/-- A normal subgroup whose finite locally constant images are `q`-groups can
be used with the original discrete coefficients of any distinct prime `p`. -/
theorem continuousH1_eq_zero_of_normal_primaryImages [Finite A] [DiscreteTopology A]
    (N : Subgroup G) [N.Normal] (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hpA : ∀ a : A, p • a = 0) (hcont : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (hfix : ∀ a : A, (∀ g : N, A.ρ g.val a = a) → a = 0)
    (hprimary : ∀ (D : Type u) [Group D] [Finite D] (f : N →* D),
      IsLocallyConstant f → IsPGroup q f.range)
    (x : continuousCohomology 1 A) : x = 0 := by
  apply continuousH1_eq_zero_of_normal_coprimeAffineImages A N p hpA hcont hfix _ x
  intro c hc
  let f := (crossedAffinePerm A c).comp N.subtype
  have hf : IsLocallyConstant f :=
    (crossedAffinePerm_locallyConstant A hcont c).comp_continuous continuous_subtype_val
  obtain ⟨m, hm⟩ := (hprimary (Equiv.Perm A) f hf).exists_card_eq
  have hd : p ∣ q ^ m := hm ▸ hc
  exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : q.Prime)).mp
    ((Fact.out : p.Prime).dvd_of_dvd_pow hd))

end ContinuousCohomology
