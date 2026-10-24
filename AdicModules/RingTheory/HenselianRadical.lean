/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Operations

import AdicModules.RingTheory.HenselianCriterion
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Henselian pairs and radicals

Henselianity of a commutative ring at an ideal is invariant under replacing the ideal
by its radical. The proof compares idempotent lifts through the two extended-ideal
quotients of each finite commutative algebra. Their quotient factor has pointwise nil
kernel; no uniform nilpotence exponent is required.

## References

- The Stacks project authors, *The Stacks project*, Lemma 15.11.6 (3),
  [Tag 09XI](https://stacks.math.columbia.edu/tag/09XI), for the finite-algebra criterion.
- The finite-algebra criterion formalized by Formal Frontier Agents in
  `AdicModules.RingTheory.HenselianCriterion`.
- Mathlib's `Mathlib.RingTheory.Idempotents`, for unique lifting of idempotents through
  ring homomorphisms with pointwise nil kernel.
-/

@[expose] public section

universe u

namespace HenselianRing

private theorem isNilpotent_of_mem_ker_factor {A : Type*} [CommRing A]
    {J K : Ideal A} (hJK : J ≤ K) (hKJ : K ≤ J.radical)
    (x : A ⧸ J) (hx : x ∈ RingHom.ker (Ideal.Quotient.factor hJK)) :
    IsNilpotent x := by
  rw [Ideal.Quotient.factor_ker] at hx
  have hx' := Ideal.map_radical_le (Ideal.Quotient.mk J) (Ideal.map_mono hKJ hx)
  rw [Ideal.map_quotient_self] at hx'
  exact mem_nilradical.mp hx'

/-- A commutative ring is Henselian at an ideal if and only if it is Henselian at its
radical.

This follows from the finite-algebra idempotent criterion of The Stacks project,
Lemma 15.11.6 (3), [Tag 09XI](https://stacks.math.columbia.edu/tag/09XI), using Mathlib's
unique lifting of idempotents through ring homomorphisms with pointwise nil kernel. -/
theorem iff_radical {R : Type u} [CommRing R] (I : Ideal R) :
    HenselianRing R I ↔ HenselianRing R I.radical := by
  constructor
  · intro h
    apply (iff_existsUnique_isIdempotentElem_map.{u, u} I.radical).mpr
    intro B _ _ _ eK heK
    let J : Ideal B := I.map (algebraMap R B)
    let K : Ideal B := I.radical.map (algebraMap R B)
    have hJK : J ≤ K := Ideal.map_mono Ideal.le_radical
    have hKJ : K ≤ J.radical := Ideal.map_radical_le (algebraMap R B)
    let q : B ⧸ J →+* B ⧸ K := Ideal.Quotient.factor hJK
    have hqmk (x : B) : q (Ideal.Quotient.mk J x) = Ideal.Quotient.mk K x :=
      Ideal.Quotient.factor_mk hJK x
    obtain ⟨d, hd, hduniq⟩ :=
      existsUnique_isIdempotentElem_eq_of_ker_isNilpotent q
        (isNilpotent_of_mem_ker_factor hJK hKJ) eK
        (Ideal.Quotient.factor_surjective hJK eK) heK
    obtain ⟨e, ⟨he, heJmap⟩, huniq⟩ :=
      (iff_existsUnique_isIdempotentElem_map.{u, u} I).mp h B d hd.1
    refine ⟨e, ⟨he, ?_⟩, ?_⟩
    · calc
        Ideal.Quotient.mk K e = q (Ideal.Quotient.mk J e) := (hqmk e).symm
        _ = q d := congrArg q heJmap
        _ = eK := hd.2
    · intro x hx
      apply huniq x
      refine ⟨hx.1, ?_⟩
      exact hduniq (Ideal.Quotient.mk J x)
        ⟨hx.1.map (Ideal.Quotient.mk J), (hqmk x).trans hx.2⟩
  · intro h
    apply (iff_existsUnique_isIdempotentElem_map.{u, u} I).mpr
    intro B _ _ _ eJ heJ
    let J : Ideal B := I.map (algebraMap R B)
    let K : Ideal B := I.radical.map (algebraMap R B)
    have hJK : J ≤ K := Ideal.map_mono Ideal.le_radical
    have hKJ : K ≤ J.radical := Ideal.map_radical_le (algebraMap R B)
    let q : B ⧸ J →+* B ⧸ K := Ideal.Quotient.factor hJK
    have hqmk (x : B) : q (Ideal.Quotient.mk J x) = Ideal.Quotient.mk K x :=
      Ideal.Quotient.factor_mk hJK x
    obtain ⟨e, ⟨he, heKmap⟩, huniq⟩ :=
      (iff_existsUnique_isIdempotentElem_map.{u, u} I.radical).mp h B (q eJ) (heJ.map q)
    obtain ⟨d, hd, hduniq⟩ :=
      existsUnique_isIdempotentElem_eq_of_ker_isNilpotent q
        (isNilpotent_of_mem_ker_factor hJK hKJ) (q eJ) ⟨eJ, rfl⟩ (heJ.map q)
    have hJe : Ideal.Quotient.mk J e = eJ :=
      (hduniq (Ideal.Quotient.mk J e)
        ⟨he.map (Ideal.Quotient.mk J), (hqmk e).trans heKmap⟩).trans
          (hduniq eJ ⟨heJ, rfl⟩).symm
    refine ⟨e, ⟨he, hJe⟩, ?_⟩
    intro x hx
    apply huniq x
    refine ⟨hx.1, ?_⟩
    calc
      Ideal.Quotient.mk K x = q (Ideal.Quotient.mk J x) := (hqmk x).symm
      _ = q eJ := congrArg q hx.2

end HenselianRing
