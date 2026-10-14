/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.Ideal.Quotient.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A prescribed class for powers of integer ideals

For the ideals spanned by `2`, `3`, and `5`, at precisions `2`, `2`, and `1`,
the powers-surjectivity theorem supplies a preimage of the residue classes
`0`, `1`, and `2`. Injectivity of the canonical map and elementary divisibility
identify this preimage with the class of `172`.
-/

namespace Ideal

private def primes : Fin 3 → ℤ := ![2, 3, 5]
private def precision : Fin 3 → ℕ := ![2, 2, 1]
private def residues : Fin 3 → ℤ := ![0, 1, 2]
private def primeIdeals (i : Fin 3) : Ideal ℤ := Ideal.span {primes i}
private def prescribedClasses (i : Fin 3) : ℤ ⧸ primeIdeals i ^ precision i :=
  Ideal.Quotient.mk (primeIdeals i ^ precision i) (residues i)

private theorem primeIdeals_pairwise_sup :
    Pairwise (fun i j => primeIdeals i ⊔ primeIdeals j = ⊤) := by
  intro i j hij
  apply Ideal.isCoprime_iff_sup_eq.mp
  apply (Ideal.isCoprime_span_singleton_iff (primes i) (primes j)).mpr
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ⟨-1, 1, by norm_num [primes]⟩
  · exact ⟨-2, 1, by norm_num [primes]⟩
  · exact ⟨1, -1, by norm_num [primes]⟩
  · exact (hij rfl).elim
  · exact ⟨2, -1, by norm_num [primes]⟩
  · exact ⟨1, -2, by norm_num [primes]⟩
  · exact ⟨-1, 2, by norm_num [primes]⟩
  · exact (hij rfl).elim

example :
    ∃ q : ℤ ⧸ ⨅ i, primeIdeals i ^ precision i,
      Ideal.quotientInfToPiQuotient (fun i => primeIdeals i ^ precision i) q =
          prescribedClasses ∧
        q = Ideal.Quotient.mk (⨅ i, primeIdeals i ^ precision i) 172 := by
  obtain ⟨q, hq⟩ :=
    Ideal.quotientInfToPiQuotient_pow_surj_of_pairwise_sup_eq_top
      primeIdeals_pairwise_sup precision prescribedClasses
  refine ⟨q, hq, ?_⟩
  apply Ideal.quotientInfToPiQuotient_inj (fun i => primeIdeals i ^ precision i)
  rw [hq, Ideal.quotientInfToPiQuotient_mk]
  funext i
  symm
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  change (172 : ℤ) - residues i ∈ Ideal.span {primes i} ^ precision i
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  fin_cases i
  · exact ⟨43, by norm_num [primes, precision, residues]⟩
  · exact ⟨19, by norm_num [primes, precision, residues]⟩
  · exact ⟨34, by norm_num [primes, precision, residues]⟩

end Ideal
