/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.RingTheory.WittVector.Domain
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing

import Mathlib.Algebra.Field.IsField
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Discrete valuation rings of Witt vectors

The discrete valuation ring condition on Witt vectors includes the domain property.
The corresponding condition on the coefficient ring is expressed through its field
property, characteristic, and perfectness, without choosing a field structure in advance.
The sufficient direction uses Mathlib's discrete valuation ring instance for Witt vectors.

## References

* Mathlib's Witt-vector formalization, in particular
  `Mathlib.RingTheory.WittVector.DiscreteValuationRing` by Robert Y. Lewis,
  Heather Macbeth, and Johan Commelin.
-/

@[expose] public section

universe u

namespace WittVector


private theorem verschiebung_mul_verschiebung_eq_p_mul
    {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    (x y : WittVector p R) :
    verschiebung x * verschiebung y = (p : WittVector p R) * verschiebung (x * y) := by
  calc
    verschiebung x * verschiebung y = verschiebung (x * frobenius (verschiebung y)) :=
      (verschiebung_mul_frobenius x (verschiebung y)).symm
    _ = verschiebung ((p : WittVector p R) * (x * y)) := by
      rw [frobenius_verschiebung]
      congr 1
      ac_rfl
    _ = verschiebung (p • (x * y)) := by rw [nsmul_eq_mul]
    -- Verschiebung preserves natural multiples by additivity, not Witt-vector linearity.
    _ = p • verschiebung (x * y) :=
      (verschiebung : WittVector p R →+ WittVector p R).map_nsmul p (x * y)
    _ = (p : WittVector p R) * verschiebung (x * y) := nsmul_eq_mul p _

private theorem ker_constantCoeff_eq_span_p_of_isDiscreteValuationRing
    {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [IsDomain R] [CharP R p]
    [IsDiscreteValuationRing (WittVector p R)] :
    RingHom.ker (constantCoeff : WittVector p R →+* R) =
      Ideal.span {(p : WittVector p R)} := by
  let M : Ideal (WittVector p R) := RingHom.ker constantCoeff
  have hp_mem : (p : WittVector p R) ∈ M := by
    apply RingHom.mem_ker.mpr
    simpa only [constantCoeff_apply] using coeff_p_zero p R
  have hM_ne : M ≠ ⊥ := by
    intro hM
    apply p_nonzero p R
    simpa only [hM, Submodule.mem_bot] using hp_mem
  let α : WittVector p R := Submodule.IsPrincipal.generator M
  have hspan : Ideal.span {α} = M := Ideal.span_singleton_generator M
  have hα_mem : α ∈ M := Submodule.IsPrincipal.generator_mem M
  have hα_ne : α ≠ 0 := by
    intro hα
    apply hM_ne
    rw [← hspan, Ideal.span_singleton_eq_bot]
    exact hα
  have hα_coeff : α.coeff 0 = 0 := by
    simpa only [M, RingHom.mem_ker, constantCoeff_apply] using hα_mem
  let x : WittVector p R := α.shift 1
  have hx : verschiebung x = α := by
    apply WittVector.ext
    intro n
    cases n with
    | zero => rw [verschiebung_coeff_zero, hα_coeff]
    | succ n =>
      rw [verschiebung_coeff_succ]
      change (α.shift 1).coeff n = α.coeff (n + 1)
      rw [shift_coeff, Nat.add_comm 1 n]
  have hVxx_mem : verschiebung (x * x) ∈ Ideal.span {α} := by
    rw [hspan]
    apply RingHom.mem_ker.mpr
    simpa only [constantCoeff_apply] using verschiebung_coeff_zero (x * x)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hVxx_mem
  -- Comparing the generator's square gives a multiple of `p` after cancellation.
  have hα_p : α = (p : WittVector p R) * b := by
    apply mul_left_cancel₀ hα_ne
    calc
      α * α = verschiebung x * verschiebung x := by rw [hx]
      _ = (p : WittVector p R) * verschiebung (x * x) :=
        verschiebung_mul_verschiebung_eq_p_mul x x
      _ = α * ((p : WittVector p R) * b) := by
        rw [hb]
        ac_rfl
  change M = Ideal.span {(p : WittVector p R)}
  apply le_antisymm
  · rw [← hspan, Ideal.span_singleton_le_span_singleton]
    exact ⟨b, hα_p⟩
  · exact (Ideal.span_singleton_le_iff_mem M).mpr hp_mem


/-- If the Witt vectors form a discrete valuation ring, the coefficient ring is a field. -/
private theorem isField_of_isDiscreteValuationRing
    {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [IsDomain R] [CharP R p]
    [IsDiscreteValuationRing (WittVector p R)] : IsField R := by
  let cc : WittVector p R →+* R := constantCoeff
  let M : Ideal (WittVector p R) := RingHom.ker cc
  have hM_prime : M.IsPrime := RingHom.ker_isPrime cc
  have hpM : (p : WittVector p R) ∈ M :=
    (RingHom.mem_ker (f := cc)).mpr (coeff_p_zero p R)
  have hM_ne_bot : M ≠ ⊥ := by
    intro hM
    apply p_nonzero p R
    simpa only [hM, Submodule.mem_bot] using hpM
  have hM_maximal : M.IsMaximal := Ideal.IsPrime.isMaximal hM_prime hM_ne_bot
  refine
    { exists_pair_ne := ⟨0, 1, zero_ne_one⟩
      mul_comm := fun x y => mul_comm x y
      mul_inv_cancel := ?_ }
  intro a ha
  obtain ⟨t, ht⟩ := (constantCoeff_surjective p : Function.Surjective cc) a
  have ht' : cc t = a := ht
  have htM : t ∉ M := by
    intro htM
    exact ha (ht.symm.trans ((RingHom.mem_ker (f := cc)).mp htM))
  have h1 : (1 : WittVector p R) ∈ M ⊔ Ideal.span {t} :=
    (Ideal.isMaximal_iff.mp hM_maximal).2 _ t le_sup_left htM
      (Submodule.mem_sup_right (Ideal.mem_span_singleton_self t))
  obtain ⟨m, hm, z, hz, hmz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hz
  refine ⟨cc b, ?_⟩
  have hm0 : cc m = 0 := (RingHom.mem_ker (f := cc)).mp hm
  simpa only [map_add, map_mul, map_one, hm0, ht', zero_add] using congrArg cc hmz


/-- Generation of the constant-coefficient kernel by `p` forces perfection of the
coefficient ring. -/
private theorem perfectRing_of_ker_constantCoeff_eq_span_p
    {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [IsDomain R] [CharP R p]
    (hker : RingHom.ker (constantCoeff : WittVector p R →+* R) =
      Ideal.span {(p : WittVector p R)}) : PerfectRing R p := by
  have hF : Function.Surjective (frobenius : WittVector p R → WittVector p R) := by
    intro z
    have hVz : verschiebung z ∈ RingHom.ker (constantCoeff : WittVector p R →+* R) := by
      apply RingHom.mem_ker.mpr
      simpa only [constantCoeff_apply] using verschiebung_coeff_zero z
    rw [hker, Ideal.mem_span_singleton] at hVz
    obtain ⟨y, hy⟩ := hVz
    refine ⟨y, verschiebung_injective p R ?_⟩
    calc
      verschiebung (frobenius y) = y * p := verschiebung_frobenius y
      _ = p * y := mul_comm _ _
      _ = verschiebung z := hy.symm
  have hpow : Function.Surjective (fun r : R => r ^ p) := by
    intro r
    obtain ⟨y, hy⟩ := hF (teichmuller p r)
    refine ⟨y.coeff 0, ?_⟩
    calc
      y.coeff 0 ^ p = (frobenius y).coeff 0 := (coeff_frobenius_charP p y 0).symm
      _ = (teichmuller p r).coeff 0 := congrArg (fun w : WittVector p R => w.coeff 0) hy
      _ = r := teichmuller_coeff_zero p r
  refine ⟨?_, hpow⟩
  intro a b hab
  apply _root_.frobenius_inj R p
  simpa only [_root_.frobenius_def] using hab


/-- The `p`-typical Witt vectors over a commutative ring form a discrete valuation ring
exactly when the coefficient ring is a perfect field of characteristic `p`.
The domain proof needed by the discrete valuation ring predicate belongs to its
left-hand condition, rather than being an assumption on the coefficient ring.
The sufficient direction uses Mathlib's Witt-vector discrete valuation ring instance
of Robert Y. Lewis, Heather Macbeth, and Johan Commelin. -/
theorem isDiscreteValuationRing_iff
    {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] :
    (∃ hD : IsDomain (WittVector p R),
      @IsDiscreteValuationRing (WittVector p R) inferInstance hD) ↔
      IsField R ∧ CharP R p ∧ PerfectRing R p := by
  constructor
  · rintro ⟨hDomain, hDVR⟩
    letI : IsDomain (WittVector p R) := hDomain
    letI : IsDiscreteValuationRing (WittVector p R) := hDVR
    obtain ⟨hDomainR, hChar⟩ := (WittVector.isDomain_iff p R).mp hDomain
    letI : IsDomain R := hDomainR
    letI : CharP R p := hChar
    have hKer :=
      ker_constantCoeff_eq_span_p_of_isDiscreteValuationRing (p := p) (R := R)
    exact ⟨isField_of_isDiscreteValuationRing (p := p) (R := R), hChar,
      perfectRing_of_ker_constantCoeff_eq_span_p (p := p) (R := R) hKer⟩
  · rintro ⟨hField, hChar, hPerfect⟩
    -- This adapter extends the given ring and preserves its operations.
    letI : Field R := hField.toField
    letI : CharP R p := hChar
    letI : PerfectRing R p := hPerfect
    exact ⟨inferInstance, WittVector.isDiscreteValuationRing⟩

end WittVector
