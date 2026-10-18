/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Domain criterion for Witt vectors

For prime `p`, Witt vectors over an arbitrary commutative ring `R` form a domain
exactly when `R` is a domain of characteristic `p`. In particular, characteristic
`p` is a conclusion of the forward implication, not an input to the criterion.
The reverse implication is already supplied by Mathlib's `WittVector.instIsDomain`.
The forward implication uses Mathlib's unconditional Frobenius–Verschiebung
identities and the multiplicativity of the Teichmüller lift.

## References

* Mathlib's `Mathlib.RingTheory.WittVector.Identities` and
  `Mathlib.RingTheory.WittVector.Teichmuller` for the operator and lift APIs.
* Mathlib's `Mathlib.RingTheory.WittVector.Domain` for the reverse implication.
-/

@[expose] public section

universe u

namespace WittVector

/-- Witt vectors over a commutative ring form a domain exactly when the coefficient
ring is a domain of characteristic `p`. No characteristic assumption is imposed
on the coefficient ring in the input. -/
theorem isDomain_iff (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] :
    IsDomain (WittVector p R) ↔ IsDomain R ∧ CharP R p := by
  constructor
  · intro hW
    letI : IsDomain (WittVector p R) := hW
    have hR : (0 : R) ≠ 1 := by
      intro h
      letI : Subsingleton R := subsingleton_of_zero_eq_one h
      exact (zero_ne_one : (0 : WittVector p R) ≠ 1)
        (WittVector.ext fun _ => Subsingleton.elim _ _)
    letI : Nontrivial R := ⟨⟨0, 1, hR⟩⟩
    have hV : verschiebung (1 : WittVector p R) ≠ 0 := by
      intro h
      apply (one_ne_zero : (1 : R) ≠ 0)
      simpa only [verschiebung_coeff_succ, one_coeff_zero, zero_coeff] using
        congrArg (fun x : WittVector p R => x.coeff 1) h
    -- These identities do not require characteristic `p` on the coefficient ring.
    have hVmul :
        verschiebung (1 : WittVector p R) * verschiebung 1 =
          verschiebung (1 : WittVector p R) * (p : WittVector p R) := by
      calc
        _ = verschiebung (frobenius (verschiebung (1 : WittVector p R))) := by
          simpa only [one_mul] using
            (verschiebung_mul_frobenius (1 : WittVector p R)
              (verschiebung (1 : WittVector p R))).symm
        _ = verschiebung (p : WittVector p R) := by
          rw [frobenius_verschiebung, one_mul]
        _ = (p : WittVector p R) * verschiebung (1 : WittVector p R) := by
          simpa only [nsmul_eq_mul, mul_one] using
            map_nsmul (verschiebung : WittVector p R →+ WittVector p R) p
              (1 : WittVector p R)
        _ = _ := mul_comm _ _
    have hVp : verschiebung (1 : WittVector p R) = (p : WittVector p R) :=
      mul_left_cancel₀ hV hVmul
    have hpR : (p : R) = 0 := by
      calc
        (p : R) = constantCoeff (p : WittVector p R) := (map_natCast _ _).symm
        _ = constantCoeff (verschiebung (1 : WittVector p R)) :=
          congrArg (constantCoeff : WittVector p R →+* R) hVp.symm
        _ = 0 := verschiebung_coeff_zero (1 : WittVector p R)
    have hChar : CharP R p :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpR
    have hNoZeroDivisors : NoZeroDivisors R := by
      refine ⟨fun {x y} hxy => ?_⟩
      have hLift : teichmuller p x * teichmuller p y = 0 := by
        rw [← map_mul, hxy, teichmuller_zero]
      rcases mul_eq_zero.mp hLift with hx | hy
      · left
        simpa only [teichmuller_coeff_zero, zero_coeff] using
          congrArg (fun x : WittVector p R => x.coeff 0) hx
      · right
        simpa only [teichmuller_coeff_zero, zero_coeff] using
          congrArg (fun x : WittVector p R => x.coeff 0) hy
    letI : NoZeroDivisors R := hNoZeroDivisors
    exact ⟨NoZeroDivisors.to_isDomain R, hChar⟩
  · rintro ⟨hR, hChar⟩
    letI : IsDomain R := hR
    letI : CharP R p := hChar
    exact WittVector.instIsDomain

end WittVector
