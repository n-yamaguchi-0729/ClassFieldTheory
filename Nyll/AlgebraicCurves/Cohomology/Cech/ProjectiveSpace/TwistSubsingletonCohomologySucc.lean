/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwist
public import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistFiniteCohomology

/-!
Vanishing of positive Čech cohomology of projective twists in the stated degree range.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le

universe u

noncomputable section

open Finset Function

namespace ProjSpaceCech
open _root_.ProjSpaceCech
open _root_.ProjSpaceCech

section Homotopy

variable {n : ℕ}

namespace Twist
open _root_.ProjSpaceCech.Twist
end Twist
open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.idx_canonical {i : ℕ} (s : Idx n i) :
    s.1 = (Idx.img n s).orderEmbOfFin (Idx.card_img n s) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.idx_canonical
    (n := n) s

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.idx_eq_of_img {i : ℕ} {s t : Idx n i}
    (h : Idx.img n s = Idx.img n t) : s = t :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.idx_eq_of_img
    (n := n) (s := s) (t := t) h

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.img_face {i : ℕ} (s : Idx n (i + 1))
    (j : Fin (i + 2)) :
    Idx.img n (Idx.face n s j)
      = (Idx.img n s).erase (s.1 j) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.img_face
    (n := n) s j

open scoped _root_.ProjSpaceCech.Twist in
/-- The increasing Cech index with a prescribed finite image. -/
def Twist.altOfFinset {i : ℕ} (T : Finset (Fin (n + 1))) (hT : T.card = i + 1) :
    Idx n i :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.altOfFinset
    (n := n) T hT

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.img_altOfFinset {i : ℕ} (T : Finset (Fin (n + 1)))
    (hT : T.card = i + 1) :
    Idx.img n (Twist.altOfFinset T hT) = T :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.img_altOfFinset
    (n := n) T hT

open scoped _root_.ProjSpaceCech.Twist in
/-- The position of a coordinate in an increasing Cech index. -/
def Twist.altPos {i : ℕ} (s : Idx n i) (j : Fin (n + 1))
    (hj : j ∈ Idx.img n s) : Fin (i + 1) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.altPos
    (n := n) s j hj

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.idx_val_altPos {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∈ Idx.img n s) :
    s.1 (Twist.altPos s j hj) = j :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.idx_val_altPos
    (n := n) s j hj

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.altPos_val {i : ℕ} (s : Idx n i) (p : Fin (i + 1)) :
    Twist.altPos s (s.1 p) (Finset.mem_image_of_mem _ (Finset.mem_univ p)) = p :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.altPos_val
    (n := n) s p

open scoped _root_.ProjSpaceCech.Twist in
/-- Insert a new coordinate into an increasing Cech index. -/
def Twist.altInsert {i : ℕ} (s : Idx n i) (j : Fin (n + 1))
    (hj : j ∉ Idx.img n s) : Idx n (i + 1) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.altInsert
    (n := n) s j hj

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.img_altInsert {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s) :
    Idx.img n (Twist.altInsert s j hj)
      = insert j (Idx.img n s) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.img_altInsert
    (n := n) s j hj

open scoped _root_.ProjSpaceCech.Twist in
/-- The position of the newly inserted coordinate. -/
def Twist.insPos {i : ℕ} (s : Idx n i) (j : Fin (n + 1))
    (hj : j ∉ Idx.img n s) : Fin (i + 2) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.insPos
    (n := n) s j hj

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.altInsert_val_insPos {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s) :
    (Twist.altInsert s j hj).1 (Twist.insPos s j hj) = j :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.altInsert_val_insPos
    (n := n) s j hj

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.face_altInsert_insPos {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s) :
    Idx.face n (Twist.altInsert s j hj)
      (Twist.insPos s j hj) = s :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.face_altInsert_insPos
    (n := n) s j hj

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.img_face_altInsert_ne {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s)
    (k : Fin (i + 2)) (hk : k ≠ Twist.insPos s j hj) :
    ∃ (m : Fin (n + 1)), m ∈ Idx.img n s ∧ m ≠ j ∧
      Idx.img n (Idx.face n (Twist.altInsert s j hj) k)
        = insert j ((Idx.img n s).erase m) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.img_face_altInsert_ne
    (n := n) s j hj k hk

variable (R : Type u) [CommRing R] (d : ℤ)

open scoped _root_.ProjSpaceCech.Twist in
/-- Extract a monomial coefficient, extending it by zero outside the chart. -/
def Twist.coeff {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n) : R :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff
    (n := n) (R := R) (d := d) f s a

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_eq {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.Mon n d (Idx.img n s)) :
    Twist.coeff R d f s a.1 = f s a :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_eq
    (n := n) (R := R) (d := d) f s a

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_of_not {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n)
    (h : ¬ Twist.negSupp n a ⊆ Idx.img n s) :
    Twist.coeff R d f s a = 0 :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_of_not
    (n := n) (R := R) (d := d) f s a h

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_add {i : ℕ} (f g : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n) :
    Twist.coeff R d (f + g) s a
      = Twist.coeff R d f s a + Twist.coeff R d g s a :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_add
    (n := n) (R := R) (d := d) f g s a

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_smul {i : ℕ} (r : R) (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n) :
    Twist.coeff R d (r • f) s a = r • Twist.coeff R d f s a :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_smul
    (n := n) (R := R) (d := d) r f s a

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.ext_coeff {i : ℕ} {f g : Twist.cochain R n d i}
    (h : ∀ s a, Twist.coeff R d f s a = Twist.coeff R d g s a) :
    f = g :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.ext_coeff
    (n := n) (R := R) (d := d) (f := f) (g := g) h

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_d {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n (i + 1)) (a : Twist.MonExp n) :
    Twist.coeff R d (Twist.d R n d i f) s a
      = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          Twist.coeff R d f (Idx.face n s j) a :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_d
    (n := n) (R := R) (d := d) f s a

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_piSingle {i : ℕ} (s₀ : Idx n i)
    (b₀ : Twist.Mon n d (Idx.img n s₀)) (r : R)
    (s : Idx n i) (a : Twist.MonExp n) :
    Twist.coeff R d (Pi.single s₀ (Finsupp.single b₀ r)) s a
      = if s = s₀ ∧ a = b₀.1 then r else 0 :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_piSingle
    (n := n) (R := R) (d := d) s₀ b₀ r s a

open scoped _root_.ProjSpaceCech.Twist in
/-- The smallest coordinate outside the negative support of a monomial. -/
def Twist.posMin (a : Twist.MonExp n)
    (ha : Twist.negSupp n a ≠ univ) : Fin (n + 1) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.posMin
    (n := n) a ha

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.posMin_notMem_negSupp (a : Twist.MonExp n)
    (ha : Twist.negSupp n a ≠ univ) :
    Twist.posMin a ha ∉ Twist.negSupp n a :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.posMin_notMem_negSupp
    (n := n) a ha

end Homotopy

section Rank

variable {n : ℕ}

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.altPos_eq_card {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∈ Idx.img n s) :
    (Twist.altPos s j hj : ℕ) = #((Idx.img n s).filter (· < j)) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.altPos_eq_card
    (n := n) s j hj

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.insPos_eq_card {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s) :
    (Twist.insPos s j hj : ℕ) = #((Idx.img n s).filter (· < j)) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.insPos_eq_card
    (n := n) s j hj

end Rank

section Hj

variable {n : ℕ} (R : Type u) [CommRing R] (d : ℤ)

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.img_subset_altInsert {i : ℕ} (s : Idx n i)
    (j₁ : Fin (n + 1)) (hj : j₁ ∉ Idx.img n s) :
    Idx.img n s ⊆ Idx.img n (Twist.altInsert s j₁ hj) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.img_subset_altInsert
    (n := n) s j₁ hj

open scoped _root_.ProjSpaceCech.Twist in
/-- The signed contraction obtained by inserting a fixed coordinate. -/
def Twist.hj (j₁ : Fin (n + 1)) (i : ℕ) :
    Twist.cochain R n d (i + 1) →ₗ[R] Twist.cochain R n d i :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.hj
    (n := n) (R := R) (d := d) j₁ i

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.hj_apply_of_mem (j₁ : Fin (n + 1)) {i : ℕ}
    (f : Twist.cochain R n d (i + 1)) (s : Idx n i)
    (hmem : j₁ ∈ Idx.img n s) :
    Twist.hj R d j₁ i f s = 0 :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.hj_apply_of_mem
    (n := n) (R := R) (d := d) j₁ f s hmem

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_hj_of_mem (j₁ : Fin (n + 1)) {i : ℕ}
    (f : Twist.cochain R n d (i + 1)) (s : Idx n i)
    (a : Twist.MonExp n) (hmem : j₁ ∈ Idx.img n s) :
    Twist.coeff R d (Twist.hj R d j₁ i f) s a = 0 :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_hj_of_mem
    (n := n) (R := R) (d := d) j₁ f s a hmem

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_hj (j₁ : Fin (n + 1)) {i : ℕ}
    (f : Twist.cochain R n d (i + 1)) (s : Idx n i)
    (a : Twist.MonExp n) (hjs : j₁ ∉ Idx.img n s)
    (ha : Twist.negSupp n a ⊆ Idx.img n s) :
    Twist.coeff R d (Twist.hj R d j₁ i f) s a
      = ((-1 : ℤ) ^ (Twist.insPos s j₁ hjs : ℕ)) •
          Twist.coeff R d f (Twist.altInsert s j₁ hjs) a :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_hj
    (n := n) (R := R) (d := d) j₁ f s a hjs ha

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_zero {i : ℕ} (s : Idx n i)
    (a : Twist.MonExp n) :
    Twist.coeff R d (0 : Twist.cochain R n d i) s a = 0 :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_zero
    (n := n) (R := R) (d := d) s a

end Hj

section DhHd

variable {n : ℕ} (R : Type u) [CommRing R] (d : ℤ)

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.dh_hd_coeff (j₁ : Fin (n + 1)) (i : ℕ)
    (s : Idx n (i + 1)) (a : Twist.MonExp n)
    (hsub : Twist.negSupp n a ⊆ Idx.img n s)
    (haj : j₁ ∉ Twist.negSupp n a)
    (f : Twist.cochain R n d (i + 1)) :
    Twist.coeff R d
        (Twist.d R n d i (Twist.hj R d j₁ i f)) s a
      + Twist.coeff R d
          (Twist.hj R d j₁ (i + 1) (Twist.d R n d (i + 1) f)) s a
      = Twist.coeff R d f s a :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.dh_hd_coeff
    (n := n) (R := R) (d := d) j₁ i s a hsub haj f

end DhHd

section Homot

variable {n : ℕ} (R : Type u) [CommRing R] (d : ℤ)

open scoped _root_.ProjSpaceCech.Twist in
/-- Monomial coefficient extraction as a linear map. -/
def Twist.coeffL {i : ℕ} (s : Idx n i)
    (a : Twist.MonExp n) : Twist.cochain R n d i →ₗ[R] R :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeffL
    (n := n) (R := R) (d := d) s a

open scoped _root_.ProjSpaceCech.Twist in
/-- The monomialwise contraction using the smallest coordinate outside negative support. -/
def Twist.homot (i : ℕ) :
    Twist.cochain R n d (i + 1) →ₗ[R] Twist.cochain R n d i :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.homot
    (n := n) (R := R) (d := d) i

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.homot_basis {i : ℕ} (s₀ : Idx n (i + 1))
    (b₀ : Twist.Mon n d (Idx.img n s₀)) (r : R) :
    Twist.homot R d i (Pi.single s₀ (Finsupp.single b₀ r))
      = if hb : Twist.negSupp n b₀.1 ≠ Finset.univ then
          Twist.hj R d (Twist.posMin b₀.1 hb) i
            (Pi.single s₀ (Finsupp.single b₀ r)) else 0 :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.homot_basis
    (n := n) (R := R) (d := d) s₀ b₀ r

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.coeff_homot {i : ℕ} (t : Idx n i)
    (a : Twist.MonExp n) (hsub : Twist.negSupp n a ⊆ Idx.img n t)
    (hne : Twist.negSupp n a ≠ Finset.univ)
    (f : Twist.cochain R n d (i + 1)) :
    Twist.coeff R d (Twist.homot R d i f) t a
      = Twist.coeff R d
          (Twist.hj R d (Twist.posMin a hne) i f) t a :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.coeff_homot
    (n := n) (R := R) (d := d) t a hsub hne f

open scoped _root_.ProjSpaceCech.Twist in
theorem Twist.subsingleton_cohomology_succ_of_le' {i : ℕ} (hi : i + 2 ≤ n) :
    Subsingleton (Twist.H R n d (i + 1)) :=
  ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le
    (n := n) (R := R) (d := d) (i := i) hi

end Homot

end ProjSpaceCech

theorem _root_.ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le (R : Type u) [CommRing R]
  (n : ℕ) (d : ℤ) {i : ℕ}
    (hi : i + 2 ≤ n) : Subsingleton (ProjSpaceCech.Twist.H R n d (i + 1)) :=
  ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le' (n := n) R d hi

end
end ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation
