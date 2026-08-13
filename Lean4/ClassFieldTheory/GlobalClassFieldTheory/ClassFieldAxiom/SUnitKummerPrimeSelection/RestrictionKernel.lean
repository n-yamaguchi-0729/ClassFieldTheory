import KummerTheory.Concrete.SUnitPreparation

/-!
# Restriction kernels of S-unit Kummer extensions

This file specializes the chosen restriction-kernel coordinates of an
enlarged S-unit Kummer extension to coordinate generators, their required
number, and their cyclic fixed fields.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section GeneralKummer

variable {K : Type*} [Field K]
    [NumberField K]

/-- The number `s-r` of finite places required to detect the restriction
kernel for the chosen source-produced enlargement of `S`. -/
def sUnitKummerPrimeCount
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (r : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  totalPlaceCard (K := K)
      (enlargeByFiniteKummerRadicalSupport
        (K := K) (L := E) n hmu S) - r

/-- The `i`-th standard generator of the actual restriction kernel
`Gal(N/E)`. -/
noncomputable def sUnitKummerKernelGenerator
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :=
  (chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod
    (K := K) (Omega := Omega) E n hmu
    p v hp hv hn r eG S).symm
      (Pi.mulSingle i
        (Multiplicative.ofAdd (1 : ZMod (n : ℕ))))

/-- The standard coordinate generators span the actual restriction kernel
`Gal(N / E)`. -/
theorem iSup_zpowers_sUnitKummerKernelGenerator_eq_top
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (⨆ i :
        Fin
          (sUnitKummerPrimeCount
            (K := K) E n hmu r S),
      Subgroup.zpowers
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)) =
      ⊤ := by
  let e :=
    chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  let P :
      Subgroup
        (enlargedSUnitKummerRestrictionHom
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod
            (K := K) E n r eG) S).ker :=
    ⨆ i,
      Subgroup.zpowers
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
  change P = ⊤
  apply top_unique
  intro sigma _
  have hsingle
      (i :
        Fin
          (sUnitKummerPrimeCount
            (K := K) E n hmu r S))
      (z : Multiplicative (ZMod (n : ℕ))) :
      e.symm (Pi.mulSingle i z) ∈ P := by
    obtain ⟨m, hm⟩ :=
      ZMod.natCast_zmod_surjective z.toAdd
    have hz :
        z =
          (Multiplicative.ofAdd
            (1 : ZMod (n : ℕ))) ^ m := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow]
      simpa using hm.symm
    rw [hz, Pi.mulSingle_pow, map_pow]
    exact
      P.pow_mem
        ((le_iSup
          (fun i =>
            Subgroup.zpowers
              (sUnitKummerKernelGenerator
                (K := K) (Omega := Omega) E n hmu
                p v hp hv hn r eG S i)) i)
          (Subgroup.mem_zpowers
            (sUnitKummerKernelGenerator
              (K := K) (Omega := Omega) E n hmu
              p v hp hv hn r eG S i)))
        m
  have hesigma :
      e sigma ∈ P.map e.toMonoidHom := by
    apply Subgroup.pi_mem_of_mulSingle_mem (e sigma)
    intro i
    refine
      ⟨e.symm (Pi.mulSingle i (e sigma i)),
        hsingle i (e sigma i), ?_⟩
    exact e.apply_symm_apply _
  obtain ⟨tau, htau, htauSigma⟩ := hesigma
  have htauEq : tau = sigma :=
    e.injective htauSigma
  exact show sigma ∈ (P : Set _) from htauEq ▸ htau

/-- Every standard restriction-kernel generator has exact order `n`. -/
theorem orderOf_sUnitKummerKernelGenerator
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    orderOf
        (sUnitKummerKernelGenerator
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i) =
      (n : ℕ) := by
  let e :=
    chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S
  change
    orderOf
        (e.symm
          (Pi.mulSingle i
            (Multiplicative.ofAdd
              (1 : ZMod (n : ℕ))))) =
      (n : ℕ)
  rw [← e.orderOf_eq
      (e.symm
        (Pi.mulSingle i
          (Multiplicative.ofAdd
            (1 : ZMod (n : ℕ))))),
    e.apply_symm_apply,
    orderOf_piMulSingle,
    orderOf_ofAdd_eq_addOrderOf,
    ZMod.addOrderOf_one]

/-- The cyclic fixed field attached to the `i`-th coordinate of the
actual relative Galois group `Gal(N/E)`. -/
noncomputable def sUnitKummerCoordinateFixedField
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :=
  enlargedSUnitKummerCyclicFixedField
    (K := K) (Omega := Omega) E n hmu
    (galois_pow_eq_one_of_equiv_pi_zmod
      (K := K) E n r eG) S
    (sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)

/-- Each coordinate fixed field has relative degree exactly `n` in
the full `S`-unit Kummer field. -/
theorem sUnitKummerCoordinateFixedField_finrank
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :
    Module.finrank
        (sUnitKummerCoordinateFixedField
          (K := K) (Omega := Omega) E n hmu
          p v hp hv hn r eG S i)
        (fullSUnitKummerExtension
          (K := K) (Omega := Omega) n
          (enlargeByFiniteKummerRadicalSupport
            (K := K) (L := E) n hmu S)) =
      (n : ℕ) := by
  unfold sUnitKummerCoordinateFixedField
  rw [enlargedSUnitKummerCyclicFixedField_finrank
      (K := K) (Omega := Omega) E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
        (K := K) E n r eG) S
      (sUnitKummerKernelGenerator
        (K := K) (Omega := Omega) E n hmu
        p v hp hv hn r eG S i),
    Subgroup.orderOf_coe,
    orderOf_sUnitKummerKernelGenerator
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i]

end GeneralKummer

end GlobalClassFieldTheory.ClassFieldAxiom
