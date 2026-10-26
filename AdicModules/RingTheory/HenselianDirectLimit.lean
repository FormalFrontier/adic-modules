/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Polynomial.Lifts

public import AdicModules.RingTheory.Ideal.DirectLimit
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Henselian

/-!
# Henselian pairs in directed direct limits

A nonempty directed system of Henselian pairs has a Henselian direct limit at the
supremum of the image ideals. The transition maps need only preserve ideal membership;
they need not be injective or surjective.

The proof first establishes Jacobson containment using the unit criterion. Polynomial
coefficients, approximate roots, ideal membership and inverses then descend to a common
stage, where the component Henselian property applies. This also allows zero rings.

## References

The proof uses Mathlib's `Ring.DirectLimit.exists_of`, `Ring.DirectLimit.of.zero_exact`
and polynomial lifting API. Monic lifts are supplied by
`Polynomial.lifts_and_natDegree_eq_and_monic`; unit reflection is used only for the
quotient by a Jacobson-contained ideal, via `isLocalHom_of_le_jacobson_bot`.
-/

@[expose] public section

universe u v

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type v) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j hij ↦ f i j hij)]

namespace Ring.DirectLimit

/-- A component element whose image is a unit becomes a unit at some later stage. -/
private theorem isUnit_eventually (i : ι) (x : R i)
    (hx : IsUnit (of R (fun i j hij ↦ f i j hij) i x)) :
    ∃ (j : ι) (hij : i ≤ j), IsUnit (f i j hij x) := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hx
  obtain ⟨j, y, hy⟩ := exists_of b
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hz : of R (fun i j hij ↦ f i j hij) k
      (f i k hik x * f j k hjk y - 1) = 0 := by
    simp only [map_sub, map_mul, map_one, of_f, hy, hb, sub_self]
  obtain ⟨l, hkl, hl⟩ := of.zero_exact (f' := f) hz
  refine ⟨l, hik.trans hkl, isUnit_iff_exists_inv.mpr
    ⟨f k l hkl (f j k hjk y), ?_⟩⟩
  apply sub_eq_zero.mp
  simpa only [map_sub, map_mul, map_one, DirectedSystem.map_map' f] using hl

end Ring.DirectLimit

namespace HenselianRing

/-- A nonempty directed direct limit of Henselian pairs is Henselian at the supremum
of the image ideals, provided the transition maps send each ideal into the next one. -/
theorem directLimit (I : ∀ i, Ideal (R i))
    (hI : ∀ (i j : ι) (hij : i ≤ j), (I i).map (f i j hij) ≤ I j)
    [∀ i, HenselianRing (R i) (I i)] :
    HenselianRing (Ring.DirectLimit R (fun i j hij ↦ f i j hij))
      (⨆ i, (I i).map (Ring.DirectLimit.of R (fun i j hij ↦ f i j hij) i)) := by
  let D := Ring.DirectLimit R (fun i j hij ↦ f i j hij)
  let φ (i : ι) : R i →+* D := Ring.DirectLimit.of R (fun i j hij ↦ f i j hij) i
  let J : Ideal D := ⨆ i, (I i).map (φ i)
  have hof (i j : ι) (hij : i ≤ j) (x : R i) : φ j (f i j hij x) = φ i x :=
    Ring.DirectLimit.of_f hij x
  have hcomp (i j : ι) (hij : i ≤ j) : (φ j).comp (f i j hij) = φ i := by
    ext x
    exact hof i j hij x
  -- Jacobson containment precedes the use of unit reflection along the quotient map.
  have hJac : J ≤ Ideal.jacobson ⊥ := by
    intro x hx
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of x
    obtain ⟨j, hij, ha⟩ :=
      (Ring.DirectLimit.of_mem_iSup_map_iff R f I hI i a).mp hx
    apply Ideal.mem_jacobson_bot.mpr
    intro y
    obtain ⟨k, b, rfl⟩ := Ring.DirectLimit.exists_of y
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    have hal : f j l hjl (f i j hij a) ∈ I l :=
      hI j l hjl (Ideal.mem_map_of_mem (f j l hjl) ha)
    have hu := Ideal.mem_jacobson_bot.mp
      (HenselianRing.jac (R := R l) (I := I l) hal) (f k l hkl b)
    simpa only [map_add, map_mul, map_one, hof] using
      (IsUnit.map (φ l) hu)
  refine { jac := hJac, is_henselian := ?_ }
  intro P hP a₀ hroot hunit
  let : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J hJac
  have hunit' : IsUnit (P.derivative.eval a₀) :=
    IsUnit.of_map (Ideal.Quotient.mk J) _ hunit
  obtain ⟨i, q₀, hq₀⟩ := Ring.DirectLimit.Polynomial.exists_of (f' := f) P
  have hlifts : P ∈ Polynomial.lifts (φ i) :=
    (Polynomial.mem_lifts P).mpr ⟨q₀, hq₀⟩
  obtain ⟨q, hq, -, hqmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hP
  obtain ⟨j, a, ha⟩ := Ring.DirectLimit.exists_of a₀
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let qk := q.map (f i k hik)
  let ak := f j k hjk a
  have hqk : qk.map (φ k) = P := by
    dsimp only [qk]
    rw [Polynomial.map_map, hcomp, hq]
  have hak : φ k ak = a₀ := by
    simpa only [ak, hof] using ha
  have heval : φ k (qk.eval ak) = P.eval a₀ := by
    rw [← Polynomial.eval_map_apply, hqk, hak]
  have hderiv : φ k (qk.derivative.eval ak) = P.derivative.eval a₀ := by
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hqk, hak]
  obtain ⟨m, hkm, hm⟩ :=
    (Ring.DirectLimit.of_mem_iSup_map_iff R f I hI k (qk.eval ak)).mp
      (by rwa [heval])
  obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.isUnit_eventually R f k
    (qk.derivative.eval ak) (by rwa [hderiv])
  obtain ⟨t, hmt, hlt⟩ := exists_ge_ge m l
  let hkt : k ≤ t := hkm.trans hmt
  have hmem_t : f k t hkt (qk.eval ak) ∈ I t := by
    have h := hI m t hmt (Ideal.mem_map_of_mem (f m t hmt) hm)
    simpa only [DirectedSystem.map_map' f] using h
  have hunit_t : IsUnit (f k t hkt (qk.derivative.eval ak)) := by
    simpa only [DirectedSystem.map_map' f] using (IsUnit.map (f l t hlt) hl)
  let qt := qk.map (f k t hkt)
  let a_t := f k t hkt ak
  have hqt : qt.map (φ t) = P := by
    dsimp only [qt]
    rw [Polynomial.map_map, hcomp, hqk]
  have hat : φ t a_t = a₀ := by
    simpa only [a_t, hof] using hak
  obtain ⟨b, hb, hba⟩ := HenselianRing.is_henselian (I := I t) qt
    (Polynomial.Monic.map (f k t hkt) (Polynomial.Monic.map (f i k hik) hqmonic)) a_t
    (by simpa only [qt, a_t, Polynomial.eval_map_apply] using hmem_t)
    (by
      apply IsUnit.map (Ideal.Quotient.mk (I t))
      simpa only [qt, a_t, Polynomial.derivative_map, Polynomial.eval_map_apply] using hunit_t)
  refine ⟨φ t b, Polynomial.IsRoot.def.mpr ?_, ?_⟩
  · have hb0 := Polynomial.IsRoot.def.mp hb
    calc
      P.eval (φ t b) = (qt.map (φ t)).eval (φ t b) := by rw [hqt]
      _ = φ t (qt.eval b) := Polynomial.eval_map_apply (φ t) b
      _ = 0 := by rw [hb0, map_zero]
  · have hbaJ : φ t (b - a_t) ∈ J :=
      (le_iSup (fun s ↦ (I s).map (φ s)) t) (Ideal.mem_map_of_mem (φ t) hba)
    simpa only [map_sub, hat] using hbaJ

end HenselianRing
