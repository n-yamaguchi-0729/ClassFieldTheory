/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.Kummer
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalInvariant

/-!
# The arithmetic trace on roots-of-unity cohomology

The Kummer inclusion into the Brauer group and the arithmetic invariant
fix the trace and its normalization.
-/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory LocalFieldTheory

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- The residue class of an integer (m) represents the Brauer class with
arithmetic invariant (m/n). -/
def zmodEquivLocalBrauerTorsion (n : ℕ+) : ZMod (n : ℕ) ≃+ brTorsion K n := by
  let e := localBrauerInvariantEquiv K
  let j := zmodToRationalCircle (n : ℕ) n.pos
  let f := (e.symm.toAddMonoidHom.comp j).codRestrict (brTorsion K n) (fun r => by
    change (n : ℕ) • e.symm (j r) = 0
    rw [← map_nsmul, (mem_range_zmodToRationalCircle_iff n n.pos _).mp ⟨r, rfl⟩, map_zero])
  apply AddEquiv.ofBijective f
  constructor
  · intro r s hrs
    have h : (f r).val = (f s).val := congrArg (fun x : brTorsion K n => x.val) hrs
    change e.symm (j r) = e.symm (j s) at h
    exact zmodToRationalCircle_injective n n.pos (e.symm.injective h)
  · intro x
    have hx : (n : ℕ) • e x.val = 0 := by
      rw [← map_nsmul, x.property, map_zero]
    obtain ⟨r, hr⟩ := (mem_range_zmodToRationalCircle_iff n n.pos _).mpr hx
    exact ⟨r, Subtype.ext ((congrArg e.symm hr).trans (e.symm_apply_apply x.val))⟩

theorem localBrauerInvariant_zmodEquivLocalBrauerTorsion (n : ℕ+) (r : ZMod (n : ℕ)) :
    localBrauerInvariant K (zmodEquivLocalBrauerTorsion K n r).val =
      zmodToRationalCircle n n.pos r :=
  (localBrauerInvariantEquiv K).apply_symm_apply _

/-- The canonical arithmetic trace for the actual étale Kummer coefficient. -/
def localKummerTrace (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    continuousCohomology 2 (separableMuTopRep K n) ≃+ ZMod (n : ℕ) :=
  (separableMuH2EquivBrTorsion K n hn).trans (zmodEquivLocalBrauerTorsion K n).symm

/-- The trace is characterized by the arithmetic invariant of the same
cohomology class under inclusion of roots of unity. -/
theorem zmodToRationalCircle_localKummerTrace (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0)
    (x : continuousCohomology 2 (separableMuTopRep K n)) :
    zmodToRationalCircle n n.pos (localKummerTrace K n hn x) =
      localBrauerInvariant K (separableMuH2ToBr K n x) := by
  let y := separableMuH2EquivBrTorsion K n hn x
  let e := zmodEquivLocalBrauerTorsion K n
  have h := localBrauerInvariant_zmodEquivLocalBrauerTorsion K n (e.symm y)
  change localBrauerInvariant K (e (e.symm y)).val = _ at h
  rw [e.apply_symm_apply] at h
  exact h.symm

end ClassFieldTheory.Brauer
