/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.Idempotents

/-! # Lifting group-algebra matrix idempotents over prime power quotients -/

@[expose] public section

open scoped Ring

noncomputable section

namespace MonoidAlgebra

variable {p m : ℕ} (hm : 0 < m) (G : Type*) [Group G]

/-- Entrywise reduction from the actual prime power coefficient ring. -/
def primePowerReduction : (ZMod (p ^ m))[G] →+* (ZMod p)[G] :=
  mapRingHom G (ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p))

theorem primePowerReduction_apply (x : (ZMod (p ^ m))[G]) (g : G) :
    (primePowerReduction hm G x).coeff g =
      ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p) (x.coeff g) :=
  coeff_mapRingHom _ _ _

theorem primePowerReduction_surjective : Function.Surjective (primePowerReduction (p := p) hm G) :=
  MonoidAlgebra.map_surjective (ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p)).toAddMonoidHom
    (ZMod.castHom_surjective (dvd_pow_self p hm.ne'))

variable [Finite G]

private theorem exists_nsmul_of_primePowerReduction_eq_zero (hp : p ≠ 0)
    (x : (ZMod (p ^ m))[G]) (hx : primePowerReduction hm G x = 0) :
    ∃ y : (ZMod (p ^ m))[G], p • y = x := by
  let : NeZero (p ^ m) := ⟨pow_ne_zero m hp⟩
  have hc (g : G) : ∃ a : ZMod (p ^ m), p • a = x.coeff g := by
    have hzero : (((x.coeff g).val : ℕ) : ZMod p) = 0 := by
      have h := congrArg (fun z : (ZMod p)[G] => z.coeff g) hx
      rw [primePowerReduction_apply, ← (x.coeff g).natCast_zmod_val, map_natCast] at h
      exact h
    obtain ⟨a, ha⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    refine ⟨(a : ZMod (p ^ m)), ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← ha, ZMod.natCast_zmod_val]
  choose a ha using hc
  let y : (ZMod (p ^ m))[G] := ofCoeff (Finsupp.ofSupportFinite a (Set.toFinite _))
  refine ⟨y, ?_⟩
  ext g
  let ev : (ZMod (p ^ m))[G] →+ ZMod (p ^ m) :=
    { toFun := fun z => z.coeff g
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (p • y) = ev x
  rw [map_nsmul]
  exact ha g

variable (I : Type*) [Fintype I] [DecidableEq I]

/-- The kernel of matrix reduction consists of nilpotents. -/
theorem primePowerReduction_matrix_isNilpotent (hp : p ≠ 0)
    (A : Matrix I I ((ZMod (p ^ m))[G]))
    (hA : (primePowerReduction hm G).mapMatrix A = 0) : IsNilpotent A := by
  have hentry (i j : I) : ∃ b : (ZMod (p ^ m))[G], p • b = A i j := by
    apply exists_nsmul_of_primePowerReduction_eq_zero hm G hp
    exact congrArg (fun B : Matrix I I ((ZMod p)[G]) => B i j) hA
  choose b hb using hentry
  let B : Matrix I I ((ZMod (p ^ m))[G]) := Matrix.of b
  have hB : p • B = A := Matrix.ext hb
  refine ⟨m, ?_⟩
  rw [← hB, ← Nat.cast_smul_eq_nsmul (ZMod (p ^ m)), smul_pow, ← Nat.cast_pow,
    ZMod.natCast_self, zero_smul]

/-- A matrix projector for a modular representation lifts to each positive
prime power, without changing its reduction. -/
theorem exists_primePowerMatrixIdempotentLift (hp : p ≠ 0)
    (e : Matrix I I ((ZMod p)[G])) (he : IsIdempotentElem e) :
    ∃ e' : Matrix I I ((ZMod (p ^ m))[G]),
      IsIdempotentElem e' ∧ (primePowerReduction hm G).mapMatrix e' = e := by
  let f : Matrix I I ((ZMod (p ^ m))[G]) →+* Matrix I I ((ZMod p)[G]) :=
    (primePowerReduction hm G).mapMatrix
  have hker (x : Matrix I I ((ZMod (p ^ m))[G])) (hx : x ∈ RingHom.ker f) : IsNilpotent x :=
    primePowerReduction_matrix_isNilpotent hm G I hp x hx
  have hf : e ∈ f.range := by
    choose a ha using fun i j : I => primePowerReduction_surjective hm G (e i j)
    exact ⟨Matrix.of a, Matrix.ext ha⟩
  exact exists_isIdempotentElem_eq_of_ker_isNilpotent f hker e hf he

end MonoidAlgebra
