/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.GroupAlgebraReduction
public import Nyll.GaloisCohomology.GroupTheory.MatrixProjectorExactness
public import Nyll.GaloisCohomology.GroupTheory.PrimePowerIdempotentLift
public import Nyll.GaloisCohomology.GroupTheory.PrimePrimaryModule
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # Prime projector weights on finite integral group-algebra modules -/

@[expose] public section

open Function Matrix.Module
open scoped Ring

noncomputable section

namespace Matrix

variable {R S J : Type*} [Ring R] [Ring S] [Fintype J] [DecidableEq J]

private theorem isUnit_intertwiner_of_projectors (φ : R →+* S)
    (hφ : ∀ r, φ r = 0 → IsNilpotent r) {e f : R}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (h : φ e = φ f) :
    ∃ u : R, IsUnit u ∧ u * e = f * u := by
  let u := f * e + (1 - f) * (1 - e)
  have h₁ : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have h₂ : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hf.eq, sub_self]
  have h₃ : IsIdempotentElem (φ f) := hf.map φ
  have h₄ : φ u = 1 := by
    change φ (f * e + (1 - f) * (1 - e)) = 1
    simp only [map_add, map_mul, map_sub, map_one, h, h₃.eq, h₃.one_sub.eq, add_sub_cancel]
  have hn : IsNilpotent (1 - u) := hφ _ (by rw [map_sub, map_one, h₄, sub_self])
  refine ⟨u, (sub_sub_cancel 1 u) ▸ hn.isUnit_one_sub, ?_⟩
  change (f * e + (1 - f) * (1 - e)) * e = f * (f * e + (1 - f) * (1 - e))
  rw [add_mul, mul_add, mul_assoc f e e, he.eq, mul_assoc (1 - f) (1 - e) e,
    h₁, mul_zero, add_zero, ← mul_assoc f f e, hf.eq,
    ← mul_assoc f (1 - f) (1 - e), h₂, zero_mul, add_zero]

/-- Congruent idempotents along a nilpotent kernel have isomorphic fixed
subgroups on any actual matrix module. -/
theorem card_projectorFixed_eq_of_map_eq (φ : Matrix J J R →+* S)
    (hφ : ∀ r, φ r = 0 → IsNilpotent r) (M : Type*) [AddCommGroup M] [Module R M]
    {e f : Matrix J J R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (h : φ e = φ f) :
    Nat.card (projectorFixed e M) = Nat.card (projectorFixed f M) := by
  obtain ⟨u, hu, huf⟩ := isUnit_intertwiner_of_projectors φ hφ he hf h
  let b : (J → M) → J → M := fun x => u • x
  have hb : Bijective b := hu.smul_bijective
  let g : projectorFixed e M → projectorFixed f M := fun x => ⟨b x.val, by
    change f • (u • x.val) = u • x.val
    rw [smul_smul, ← huf, mul_smul, smul_projectorFixed]⟩
  apply Nat.card_congr (Equiv.ofBijective g ?_)
  refine ⟨fun _ _ hxy => Subtype.ext (hb.1 (congrArg Subtype.val hxy)), ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hb.2 y.val
  have hx' : e • x = x := by
    apply hb.1
    change u • (e • x) = u • x
    rw [smul_smul, huf, mul_smul, show u • x = y.val from hx, smul_projectorFixed]
  exact ⟨⟨x, hx'⟩, Subtype.ext hx⟩

end Matrix

namespace MonoidAlgebra

variable {p : ℕ} (G : Type*) [Group G] [Finite G]
  {J : Type*} [Fintype J] [DecidableEq J]
  {A : Type*} [AddCommGroup A] [Module ℤ[G] A]

/-- The cardinal of a lifted projector on the actual primary part. -/
def primeProjectorCardAt {m : ℕ}
    (hA : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ m) • a = 0)
    (e : Matrix J J ((ZMod (p ^ m))[G])) : ℕ :=
  letI := modModule G (p ^ m) hA
  Nat.card (Matrix.projectorFixed e (Submodule.primePrimary p ℤ[G] A))

omit [Finite G] in
private theorem primePowerReduction_comp_change {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (h : n ≤ m) (x : (ZMod (p ^ m))[G]) :
    primePowerReduction hn G (mapRingHom G (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))) x) =
      primePowerReduction hm G x := by
  obtain ⟨r, rfl⟩ := intReduction_surjective G (p ^ m) x
  change mapRingHom G (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p))
    (mapRingHom G (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))) (intReduction G (p ^ m) r)) =
      mapRingHom G (ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p)) (intReduction G (p ^ m) r)
  simp only [mapRingHom_castHom_intReduction]

private theorem primeProjectorCardAt_change {n m : ℕ} (h : n ≤ m)
    (hA : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ m) • a = 0)
    (hA' : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ n) • a = 0)
    (e : Matrix J J ((ZMod (p ^ m))[G])) :
    primeProjectorCardAt G hA e = primeProjectorCardAt G hA'
      ((mapRingHom G (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n)))).mapMatrix e) := by
  let P := Submodule.primePrimary p ℤ[G] A
  let := modModule G (p ^ m) hA
  let := modModule G (p ^ n) hA'
  let c := mapRingHom G (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n)))
  have hact (x : J → P) : (c.mapMatrix e) • x = e • x := by
    funext i
    apply Finset.sum_congr rfl
    intro j _
    exact modModule_smul_change G (p ^ m) (pow_dvd_pow p h) hA hA' (e i j) (x j)
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
    show e • x = x ↔ (c.mapMatrix e) • x = x by rw [hact]))

/-- The weighted cardinal is independent of the chosen lift at a common bound. -/
theorem primeProjectorCardAt_eq_of_lifts {m : ℕ} (hm : 0 < m) (hp : p ≠ 0)
    (hA : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ m) • a = 0)
    {e f : Matrix J J ((ZMod (p ^ m))[G])} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : (primePowerReduction hm G).mapMatrix e = (primePowerReduction hm G).mapMatrix f) :
    primeProjectorCardAt G hA e = primeProjectorCardAt G hA f := by
  let := modModule G (p ^ m) hA
  exact Matrix.card_projectorFixed_eq_of_map_eq ((primePowerReduction hm G).mapMatrix)
    (fun x hx => primePowerReduction_matrix_isNilpotent hm G J hp x hx)
    (Submodule.primePrimary p ℤ[G] A) he hf h

private theorem primeProjectorCardAt_eq_of_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : n ≤ m)
    (hp : p ≠ 0)
    (hmA : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ m) • a = 0)
    (hnA : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ n) • a = 0)
    {e : Matrix J J ((ZMod (p ^ m))[G])} {f : Matrix J J ((ZMod (p ^ n))[G])}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hred : (primePowerReduction hm G).mapMatrix e = (primePowerReduction hn G).mapMatrix f) :
    primeProjectorCardAt G hmA e = primeProjectorCardAt G hnA f := by
  let r : Matrix J J ((ZMod (p ^ m))[G]) →+* Matrix J J ((ZMod (p ^ n))[G]) :=
    (mapRingHom G (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n)))).mapMatrix
  have hr : (primePowerReduction hn G).mapMatrix (r e) =
      (primePowerReduction hm G).mapMatrix e :=
    Matrix.ext fun i j => primePowerReduction_comp_change G hn hm h (e i j)
  exact (primeProjectorCardAt_change G h hmA hnA e).trans
    (primeProjectorCardAt_eq_of_lifts G hn hp hnA (he.map r) hf (hr.trans hred))

/-- The projected cardinal is independent of the positive bound and lift. -/
theorem primeProjectorCardAt_eq {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hp : p ≠ 0)
    (hmA : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ m) • a = 0)
    (hnA : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ n) • a = 0)
    {e : Matrix J J ((ZMod (p ^ m))[G])} {f : Matrix J J ((ZMod (p ^ n))[G])}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hred : (primePowerReduction hm G).mapMatrix e = (primePowerReduction hn G).mapMatrix f) :
    primeProjectorCardAt G hmA e = primeProjectorCardAt G hnA f := by
  rcases le_total n m with h | h
  · exact primeProjectorCardAt_eq_of_le G hn hm h hp hmA hnA he hf hred
  · exact (primeProjectorCardAt_eq_of_le G hm hn h hp hnA hmA hf he hred.symm).symm

variable (e : Matrix J J ((ZMod p)[G])) (he : IsIdempotentElem e) (hp : p.Prime)

/-- The cardinal attached to the given modular projector on any finite
integral group-algebra module. The choice of exponent and lift is immaterial. -/
def primeProjectorCard [Finite A] : ℕ := by
  let h := Submodule.exists_pow_nsmul_eq_zero_primePrimary (R := ℤ[G]) (A := A) p
  let hf := exists_primePowerMatrixIdempotentLift h.choose_spec.1 G J hp.ne_zero e he
  exact primeProjectorCardAt G h.choose_spec.2 hf.choose

theorem primeProjectorCard_eq_at [Finite A] {m : ℕ} (hm : 0 < m)
    (hA : ∀ a : Submodule.primePrimary p ℤ[G] A, (p ^ m) • a = 0)
    (f : Matrix J J ((ZMod (p ^ m))[G])) (hf : IsIdempotentElem f)
    (hred : (primePowerReduction hm G).mapMatrix f = e) :
    primeProjectorCard (A := A) G e he hp = primeProjectorCardAt G hA f := by
  let h := Submodule.exists_pow_nsmul_eq_zero_primePrimary (R := ℤ[G]) (A := A) p
  let H := exists_primePowerMatrixIdempotentLift h.choose_spec.1 G J hp.ne_zero e he
  change primeProjectorCardAt G h.choose_spec.2 H.choose = primeProjectorCardAt G hA f
  exact primeProjectorCardAt_eq G hm h.choose_spec.1 hp.ne_zero h.choose_spec.2 hA
    H.choose_spec.1 hf (H.choose_spec.2.trans hred.symm)

/-- For a module already killed by the prime, the weight is computed by
the original modular projector acting on the original module. -/
theorem primeProjectorCard_eq_modModule [Finite A] (hA : ∀ a : A, p • a = 0) :
    letI := modModule G p hA
    primeProjectorCard (A := A) G e he hp = Nat.card (Matrix.projectorFixed e A) := by
  let := modModule G p hA
  let P := Submodule.primePrimary p ℤ[G] A
  have hP (a : P) : p • a = 0 := Subtype.ext (hA a.val)
  have hin : Surjective P.subtype := by
    intro a
    exact ⟨⟨a, ⟨1, (pow_one p).symm ▸ hA a⟩⟩, rfl⟩
  obtain ⟨m, hm, hmP⟩ := Submodule.exists_pow_nsmul_eq_zero_primePrimary (R := ℤ[G]) (A := A) p
  obtain ⟨f, hf, hred⟩ := exists_primePowerMatrixIdempotentLift hm G J hp.ne_zero e he
  let := modModule G p hP
  let := modModule G (p ^ m) hmP
  have hact (x : J → P) : e • x = f • x := by
    rw [← hred]
    funext j
    apply Finset.sum_congr rfl
    intro i _
    exact modModule_smul_change G (p ^ m) (dvd_pow_self p hm.ne') hmP hP (f j i) (x i)
  have hcP : primeProjectorCardAt G hmP f = Nat.card (Matrix.projectorFixed e P) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => show f • x = x ↔ e • x = x by rw [hact]))
  let i := modModuleMap G p hP hA P.subtype
  let g := Matrix.projectorFixedMap e i
  have hg : Bijective g :=
    ⟨Matrix.projectorFixedMap_injective e i Subtype.val_injective,
      Matrix.projectorFixedMap_surjective e he i hin⟩
  exact (primeProjectorCard_eq_at G e he hp hm hmP f hf hred).trans
    (hcP.trans (Nat.card_congr (Equiv.ofBijective g hg)))

private theorem pow_nsmul_zero_of_bound {X : Type*} [AddCommGroup X] {x : X}
    {m n : ℕ} (h : m ≤ n) (hx : p ^ m • x = 0) : p ^ n • x = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, pow_add, ← smul_smul, hx, smul_zero]

variable {B C : Type*} [AddCommGroup B] [Module ℤ[G] B] [AddCommGroup C] [Module ℤ[G] C]

/-- The actual modular projector weight is multiplicative on every finite
short exact sequence of integral modules for the group algebra. -/
theorem primeProjectorCard_mul_of_exact [Finite A] [Finite B] [Finite C]
    (f : A →ₗ[ℤ[G]] B) (g : B →ₗ[ℤ[G]] C)
    (hf : Injective f) (hg : Surjective g) (hex : Exact f g) :
    primeProjectorCard (A := B) G e he hp =
      primeProjectorCard (A := A) G e he hp * primeProjectorCard (A := C) G e he hp := by
  obtain ⟨a, ha, hAa⟩ := Submodule.exists_pow_nsmul_eq_zero_primePrimary (R := ℤ[G]) (A := A) p
  obtain ⟨b, _, hBb⟩ := Submodule.exists_pow_nsmul_eq_zero_primePrimary (R := ℤ[G]) (A := B) p
  obtain ⟨c, _, hCc⟩ := Submodule.exists_pow_nsmul_eq_zero_primePrimary (R := ℤ[G]) (A := C) p
  let m := max a (max b c)
  have hm : 0 < m := ha.trans_le (le_max_left _ _)
  have hA (x : Submodule.primePrimary p ℤ[G] A) : p ^ m • x = 0 :=
    pow_nsmul_zero_of_bound (le_max_left a (max b c)) (hAa x)
  have hB (x : Submodule.primePrimary p ℤ[G] B) : p ^ m • x = 0 :=
    pow_nsmul_zero_of_bound ((le_max_left b c).trans (le_max_right a _)) (hBb x)
  have hC (x : Submodule.primePrimary p ℤ[G] C) : p ^ m • x = 0 :=
    pow_nsmul_zero_of_bound ((le_max_right b c).trans (le_max_right a _)) (hCc x)
  obtain ⟨E, hE, hE'⟩ := exists_primePowerMatrixIdempotentLift hm G J hp.ne_zero e he
  rw [primeProjectorCard_eq_at G e he hp hm hB E hE hE',
    primeProjectorCard_eq_at G e he hp hm hA E hE hE',
    primeProjectorCard_eq_at G e he hp hm hC E hE hE']
  let := modModule G (p ^ m) hA
  let := modModule G (p ^ m) hB
  let := modModule G (p ^ m) hC
  apply Matrix.card_projectorFixed_mul_of_exact E hE
    (modModuleMap G (p ^ m) hA hB (Submodule.primePrimaryMap p f))
    (modModuleMap G (p ^ m) hB hC (Submodule.primePrimaryMap p g))
  · exact Submodule.primePrimaryMap_injective f hf
  · exact Submodule.primePrimaryMap_surjective hp g hg
  · exact Submodule.primePrimaryMap_exact f g hf hex

end MonoidAlgebra
