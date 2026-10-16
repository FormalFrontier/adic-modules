/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.Topology.Algebra.PrincipalUnits
import AdicModules.Topology.Algebra.PadicInt
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Principal units in mixed and equal characteristic

The standard norm topology on `ℤ_[p]` is `(p)`-adic, and `1 + p` is a
nonidentity unit in the reduction kernel. In `ℤ_[2]`, the same kernel contains
`-1`, a nonidentity element whose square is one.

For `PowerSeries (ZMod p)`, the stock `WithIdeal` topology for `(X)` is used,
together with Mathlib's adic completeness instance. The unit `1 + X` is not
one, and its `p`th power is `1 + X ^ p`, which is again not one. There is no
comparison here with the coefficientwise topology on power series.

The input hypotheses, membership and nonidentity assertions below are proved
using the ring and topology APIs. The final powering assertions use the
p-adic-power API; the first-power fixtures also instantiate joint continuity
under the proved adic topology hypotheses.

## References

* Fesenko–Vostokov, *Local Fields and Their Extensions*, Chapter I, (6.1).
* Mathlib's p-adic integers, power-series units, characteristic-p power
  identities, adic completeness and `WithIdeal` topology.
-/

-- The named mathematical fixtures are private, rather than a public test API.
set_option linter.privateModule false

open scoped Topology

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

local notation "J" => (Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p])
local notation "K" => MonoidHom.ker (Units.map (RingHom.toMonoidHom (Ideal.Quotient.mk J)))

private instance span_prime_adicComplete : IsAdicComplete J ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

private theorem span_prime_isAdic : IsAdic J := by
  apply IsTopologicalAddGroup.ext
  · infer_instance
  · exact (J).ringFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  · apply (PadicInt.hasBasis_nhds_zero_span_pow p).eq_of_same_basis
    simpa only [Ideal.span_singleton_pow] using (J).hasBasis_nhds_zero_adic

private theorem prime_mem_span : (p : ℤ_[p]) ∈ J :=
  Ideal.subset_span (Set.mem_singleton _)

private theorem one_add_prime_isUnit : IsUnit (1 + (p : ℤ_[p])) := by
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  apply IsAdicComplete.le_jacobson_bot (I := J)
  simp

private noncomputable def oneAddPrime : K :=
  ⟨(one_add_prime_isUnit p).unit, by
    rw [(J).mem_ker_unitsMap_quotient_iff]
    simp⟩

private theorem oneAddPrime_val : (((oneAddPrime p : K) : ℤ_[p]ˣ) : ℤ_[p]) =
    1 + (p : ℤ_[p]) := (one_add_prime_isUnit p).unit_spec

private theorem oneAddPrime_ne_one : oneAddPrime p ≠ 1 := by
  intro h
  have hv := congrArg (fun v : K => ((v : ℤ_[p]ˣ) : ℤ_[p])) h
  have hp0 : (p : ℤ_[p]) = 0 := by
    simpa only [oneAddPrime_val, OneMemClass.coe_one, Units.val_one,
      add_eq_left] using hv
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp0

private theorem oneAddPrime_topological_inputs :
    IsAdic J ∧ IsOpenUnits ℤ_[p] :=
  ⟨span_prime_isAdic p,
    IsOpenUnits.of_isAdic (span_prime_isAdic p) (IsAdicComplete.le_jacobson_bot (I := J))⟩

private theorem oneAddPrime_padicPow_one :
    (J).padicPow (p := p) (hpI := prime_mem_span p) 1 (oneAddPrime p) =
      oneAddPrime p ∧ oneAddPrime p ≠ 1 ∧
      Continuous (fun t : ℤ_[p] × K =>
        (J).padicPow (p := p) (hpI := prime_mem_span p) t.1 t.2) :=
  ⟨(J).padicPow_one (p := p) (hpI := prime_mem_span p) _, oneAddPrime_ne_one p,
    (J).continuous_padicPow (p := p) (hpI := prime_mem_span p) (hI := span_prime_isAdic p)⟩

private theorem oneAddPrime_power_congruence (n : ℕ) :
    (1 + (p : ℤ_[p])) ^ p ^ n - 1 ∈ J ^ (n + 1) := by
  simpa only [oneAddPrime_val] using (J).pow_pow_sub_one_mem (prime_mem_span p) (oneAddPrime p) n

end PadicInt

namespace PadicInt

private instance twoIdealComplete :
    IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] := span_prime_adicComplete 2

private noncomputable def minusOnePrincipal :
    (Units.map (Ideal.Quotient.mk (Ideal.span {(2 : ℤ_[2])})).toMonoidHom).ker :=
  ⟨-1, by
    rw [Ideal.mem_ker_unitsMap_quotient_iff]
    change (-1 : ℤ_[2]) - 1 ∈ (Ideal.span {(2 : ℤ_[2])} : Ideal ℤ_[2])
    convert (Ideal.span {(2 : ℤ_[2])}).neg_mem (prime_mem_span 2) using 1
    ring⟩

private theorem minusOnePrincipal_ne_one : minusOnePrincipal ≠ 1 := by
  intro h
  have hv := congrArg
    (fun v : (Units.map (Ideal.Quotient.mk
      (Ideal.span {(2 : ℤ_[2])})).toMonoidHom).ker => ((v : ℤ_[2]ˣ) : ℤ_[2])) h
  have hcast : ((-1 : ℤ) : ℤ_[2]) = ((1 : ℤ) : ℤ_[2]) := by
    simpa [minusOnePrincipal] using hv
  exact (by decide : (-1 : ℤ) ≠ 1) ((PadicInt.intCast_eq _ _).mp hcast)

private theorem minusOnePrincipal_sq : minusOnePrincipal ^ (2 : ℕ) = 1 := by
  apply Subtype.ext
  change (-1 : ℤ_[2]ˣ) ^ (2 : ℕ) = 1
  simp

private theorem minusOnePrincipal_padicPow_two :
    (Ideal.span {(2 : ℤ_[2])}).padicPow (p := 2) (hpI := prime_mem_span 2)
      2 minusOnePrincipal = 1 ∧ minusOnePrincipal ≠ 1 := by
  refine ⟨?_, minusOnePrincipal_ne_one⟩
  simpa only [Int.cast_ofNat, zpow_ofNat, minusOnePrincipal_sq] using
    (Ideal.span {(2 : ℤ_[2])}).padicPow_intCast
      (p := 2) (hpI := prime_mem_span 2) (2 : ℤ) minusOnePrincipal

end PadicInt

namespace PowerSeries

variable (p : ℕ) [Fact p.Prime]

local notation "R" => PowerSeries (ZMod p)
local notation "J" => (Ideal.span {(X : R)} : Ideal R)
local notation "K" => MonoidHom.ker (Units.map (RingHom.toMonoidHom (Ideal.Quotient.mk J)))

private noncomputable instance xIdeal : WithIdeal R := ⟨J⟩

private instance charPrime : CharP R p :=
  charP_of_injective_ringHom (f := C) C_injective p

private theorem xIdeal_isAdic : IsAdic J := rfl

private theorem prime_mem_xIdeal : (p : R) ∈ J := by
  rw [CharP.cast_eq_zero R p]
  exact (J).zero_mem

private theorem xIdeal_complete : IsAdicComplete J R := inferInstance

private theorem one_add_X_isUnit : IsUnit (1 + (X : R)) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)

private noncomputable def oneAddX : K :=
  ⟨(one_add_X_isUnit p).unit, by
    rw [(J).mem_ker_unitsMap_quotient_iff]
    simp⟩

private theorem oneAddX_val : (((oneAddX p : K) : Rˣ) : R) = 1 + (X : R) :=
  (one_add_X_isUnit p).unit_spec

private theorem oneAddX_ne_one : oneAddX p ≠ 1 := by
  intro h
  have hv := congrArg (fun v : K => coeff 1 ((v : Rˣ) : R)) h
  simp [oneAddX_val, coeff_one, coeff_X] at hv

private theorem one_add_X_pow_prime : (1 + (X : R)) ^ p = 1 + X ^ p := by
  simpa only [one_pow] using add_pow_char (1 : R) X p

private theorem one_add_X_pow_prime_ne_one : (1 + (X : R) ^ p) ≠ 1 := by
  intro h
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hc := congrArg (coeff p) h
  simp [coeff_one, coeff_X_pow, hp] at hc

private theorem oneAddX_padicPow_one :
    (J).padicPow (p := p) (hpI := prime_mem_xIdeal p) 1 (oneAddX p) = oneAddX p ∧
      oneAddX p ≠ 1 ∧ Continuous (fun t : ℤ_[p] × K =>
        (J).padicPow (p := p) (hpI := prime_mem_xIdeal p) t.1 t.2) :=
  ⟨(J).padicPow_one (p := p) (hpI := prime_mem_xIdeal p) _, oneAddX_ne_one p,
    (J).continuous_padicPow (p := p) (hpI := prime_mem_xIdeal p) (hI := xIdeal_isAdic p)⟩

private theorem oneAddX_padicPow_prime :
    ((((J).padicPow (p := p) (hpI := prime_mem_xIdeal p) (p : ℤ_[p])
      (oneAddX p) : K) : Rˣ) : R) = 1 + X ^ p ∧ (1 + (X : R) ^ p) ≠ 1 := by
  refine ⟨?_, one_add_X_pow_prime_ne_one p⟩
  have h := (J).padicPow_intCast (p := p) (hpI := prime_mem_xIdeal p)
    (p : ℤ) (oneAddX p)
  have hv := congrArg (fun v : K => ((v : Rˣ) : R)) h
  simpa only [Int.cast_natCast, zpow_natCast, Subgroup.coe_pow, Units.val_pow_eq_pow_val,
    oneAddX_val, one_add_X_pow_prime] using hv

end PowerSeries
