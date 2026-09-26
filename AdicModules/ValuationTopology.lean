/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/-!
# Principal-adic topology on a valuation ring

This file compares the topology defined by a valuation on a valuation ring with the adic
topology associated to a nonzero principal ideal. The Hausdorff hypothesis on the principal
adic filtration is exactly the cofinality input; no rank, discreteness, or Noetherianity
assumption is needed.
-/

@[expose] public section

noncomputable section

universe u v

namespace Valuation

/-- If a valuation detects membership in principal ideals and the powers of `(a)` are
separated, then the values of those powers are cofinal below every nonzero value-group
radius. -/
theorem exists_pow_restrict_lt_of_isHausdorff
    {R : Type u} {Γ₀ : Type v} [CommRing R]
    [LinearOrderedCommGroupWithZero Γ₀] (ν : Valuation R Γ₀)
    (hspan : ∀ x y : R, x ∈ Ideal.span {y} ↔ ν x ≤ ν y)
    {a : R} [IsHausdorff (Ideal.span {a}) R]
    (γ : (ValueGroup₀ (.ofClass ν))ˣ) :
    ∃ n : ℕ, ν.restrict a ^ n < γ.1 := by
  by_cases hγ : 1 < γ.1
  · exact ⟨0, by simpa using hγ⟩
  have hγle : γ.1 ≤ 1 := le_of_not_gt hγ
  obtain ⟨r, s, hr, hs, hrs⟩ := ν.exists_div_eq_of_unit γ
  have hrsle : ν.restrict r ≤ ν.restrict s := by
    rw [← div_le_one₀ ((ν.restrict_pos_iff s).2 hs), hrs]
    exact hγle
  have hrs_mem : r ∈ Ideal.span {s} :=
    (hspan r s).2 (ν.restrict_le_iff.mp hrsle)
  rw [Ideal.mem_span_singleton] at hrs_mem
  obtain ⟨c, hc⟩ := hrs_mem
  have hs0 : ν.restrict s ≠ 0 := ((ν.restrict_pos_iff s).2 hs).ne'
  have hcγ : ν.restrict c = γ.1 := by
    rw [hc, map_mul, mul_div_cancel_left₀ _ hs0] at hrs
    exact hrs
  by_contra hpow
  push Not at hpow
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0, map_zero] at hcγ
    exact (Units.ne_zero γ) hcγ.symm
  apply hc0
  apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) R)
  intro n
  rw [SModEq.zero]
  have hval : ν c ≤ ν (a ^ n) := by
    rw [← ν.restrict_le_iff]
    calc
      ν.restrict c = γ.1 := hcγ
      _ ≤ ν.restrict a ^ n := hpow n
      _ = ν.restrict (a ^ n) := by simp only [map_pow]
  have hmem : c ∈ Ideal.span {a ^ n} := (hspan c (a ^ n)).2 hval
  simpa only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] using hmem

end Valuation

namespace ValuationRing

/-- In a valuation domain separated for the powers of `(a)`, every nonzero prime ideal
contains the radical of `(a)`.

Indeed, if `a` were outside a nonzero prime `p`, choose a nonzero `x ∈ p`. Totality of
divisibility compares `x` with every power of `a`. The alternative `x ∣ a ^ n` would put
`a` in `p`, so every `a ^ n` divides `x`; separatedness then forces `x = 0`. -/
theorem radical_span_singleton_le_prime_of_isHausdorff
    {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    {a : V} [IsHausdorff (Ideal.span {a}) V]
    (p : Ideal V) [p.IsPrime] (hp : p ≠ ⊥) :
    (Ideal.span {a}).radical ≤ p := by
  apply (Ideal.IsPrime.radical_le_iff (inferInstance : p.IsPrime)).2
  rw [Ideal.span_singleton_le_iff_mem]
  by_contra ha
  obtain ⟨x, hx, hx0⟩ := p.ne_bot_iff.mp hp
  apply hx0
  apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) V)
  intro n
  rw [SModEq.zero]
  have hxn : x ∈ (Ideal.span {a}) ^ n := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rcases dvd_total (a ^ n) x with hanx | hxan
    · exact hanx
    · exact
        (ha ((inferInstance : p.IsPrime).mem_of_pow_mem n (p.mem_of_dvd hxan hx))).elim
  simpa only [smul_eq_mul, Ideal.mul_top] using hxn

/-- In a valuation ring separated for the powers of `(a)`, those powers are cofinal below
every nonzero radius for the valuation induced on the ring by its fraction-field valuation. -/
theorem exists_pow_valuation_lt_of_isHausdorff
    {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    {a : V} [IsHausdorff (Ideal.span {a}) V]
    (γ : (ValueGroup₀ (.ofClass
      ((valuation V K).comap (algebraMap V K))))ˣ) :
    ∃ n : ℕ,
      ((valuation V K).comap (algebraMap V K)).restrict a ^ n < γ.1 := by
  apply Valuation.exists_pow_restrict_lt_of_isHausdorff _ (fun x y ↦ ?_) γ
  change x ∈ (Ideal.span {y} : Set V) ↔ _
  rw [(integers V K).coe_span_singleton_eq_setOfPred_le_v_algebraMap]
  rfl

/-- For a nonzero `a` in a valuation ring, if the powers of `(a)` are separated, then the
topology induced by the fraction-field valuation is the `(a)`-adic topology. -/
theorem isAdic_valuationTopology_span_singleton
    {V : Type u} {K : Type v} [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    {a : V} (ha0 : a ≠ 0) [IsHausdorff (Ideal.span {a}) V] :
    @IsAdic V _
      (Valued.mk' ((valuation V K).comap
        (algebraMap V K))).toUniformSpace.toTopologicalSpace
      (Ideal.span {a}) := by
  let νV := (valuation V K).comap (algebraMap V K)
  let _ : Valued V (ValueGroup V K) := Valued.mk' νV
  have hmem (n : ℕ) (b : V) :
      b ∈ (Ideal.span {a}) ^ n ↔ νV.restrict b ≤ νV.restrict (a ^ n) := by
    rw [Ideal.span_singleton_pow]
    change b ∈ (Ideal.span {a ^ n} : Set V) ↔ _
    rw [(integers V K).coe_span_singleton_eq_setOfPred_le_v_algebraMap]
    change νV b ≤ νV (a ^ n) ↔ _
    exact νV.restrict_le_iff.symm
  rw [isAdic_iff]
  constructor
  · intro n
    have hr : νV.restrict (a ^ n) ≠ 0 := by
      rw [ne_eq, νV.restrict_eq_zero_iff]
      change (valuation V K) (algebraMap V K (a ^ n)) ≠ 0
      simp [ha0]
    have hopen := Valued.isOpen_closedBall V hr
    convert hopen using 1
    ext b
    exact hmem n b
  · intro s hs
    obtain ⟨γ, -, hγ⟩ :=
      (Valued.hasBasis_nhds_zero V (ValueGroup V K)).mem_iff.mp hs
    obtain ⟨n, hn⟩ :=
      exists_pow_valuation_lt_of_isHausdorff (V := V) (K := K) (a := a) γ
    refine ⟨n, fun b hb ↦ hγ ?_⟩
    exact (hmem n b).mp hb |>.trans_lt (by simpa only [map_pow] using hn)

end ValuationRing
