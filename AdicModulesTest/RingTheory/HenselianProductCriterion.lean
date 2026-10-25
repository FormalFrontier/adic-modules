/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import AdicModules.RingTheory.HenselianPi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# A nonrectangular Henselian ideal in an infinite product

The finitely supported functions valued in `(2)` form a Henselian ideal of
`ℕ → ℤ_[2]`, strictly smaller than the product of its images.
-/

@[expose] public section

namespace HenselianProductCriterion

private abbrev Z2 := PadicInt 2
private noncomputable abbrev twoIdeal : Ideal Z2 := IsLocalRing.maximalIdeal Z2

private theorem twoIdeal_eq_span : twoIdeal = Ideal.span {(2 : Z2)} :=
  PadicInt.maximalIdeal_eq_span_p (p := 2)

private theorem two_mem : (2 : Z2) ∈ twoIdeal :=
  twoIdeal_eq_span.symm ▸ Ideal.subset_span (Set.mem_singleton (2 : Z2))

private theorem two_ne_zero : (2 : Z2) ≠ 0 :=
  PadicInt.prime_p.ne_zero

/-- The ideal of functions with finite support. -/
private def finiteSupportIdeal : Ideal (ℕ → Z2) where
  carrier := {f | ∃ s : Finset ℕ, ∀ n ∉ s, f n = 0}
  zero_mem' := ⟨∅, by intro n hn; rfl⟩
  add_mem' := by
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, ?_⟩
    intro n hn
    have hn' : n ∉ s ∧ n ∉ t := by
      simpa only [Finset.mem_union, not_or] using hn
    change f n + g n = 0
    rw [hs n hn'.1, ht n hn'.2, add_zero]
  smul_mem' := by
    rintro a f ⟨s, hs⟩
    refine ⟨s, ?_⟩
    intro n hn
    change a n * f n = 0
    rw [hs n hn, mul_zero]

private theorem mem_finiteSupportIdeal (f : ℕ → Z2) :
    f ∈ finiteSupportIdeal ↔ ∃ s : Finset ℕ, ∀ n ∉ s, f n = 0 := Iff.rfl

private noncomputable abbrev K : Ideal (ℕ → Z2) :=
  finiteSupportIdeal ⊓ Ideal.pi (fun _ : ℕ => twoIdeal)

private theorem mem_K (f : ℕ → Z2) :
    f ∈ K ↔ (∃ s : Finset ℕ, ∀ n ∉ s, f n = 0) ∧ ∀ n, f n ∈ twoIdeal := by
  change (f ∈ finiteSupportIdeal ∧ f ∈ Ideal.pi (fun _ : ℕ => twoIdeal)) ↔ _
  rw [mem_finiteSupportIdeal, Ideal.mem_pi]

private theorem single_mem_K (i : ℕ) {x : Z2} (hx : x ∈ twoIdeal) :
    (fun n => if n = i then x else 0) ∈ K := by
  apply (mem_K _).mpr
  refine ⟨⟨{i}, ?_⟩, ?_⟩
  · intro n hn
    exact ite_eq_right (by simpa only [Finset.mem_singleton] using hn)
  · intro n
    by_cases hn : n = i
    · simpa [hn] using hx
    · simp [hn]

/-- Every coordinate image is exactly the principal ideal `(2)`. -/
private theorem map_eval_K (i : ℕ) :
    K.map (Pi.evalRingHom (fun _ : ℕ => Z2) i) = Ideal.span {(2 : Z2)} := by
  calc
    K.map (Pi.evalRingHom (fun _ : ℕ => Z2) i) = twoIdeal := by
      ext x
      rw [Ideal.mem_map_iff_of_surjective (Pi.evalRingHom (fun _ : ℕ => Z2) i)
        (Function.surjective_eval _)]
      constructor
      · rintro ⟨f, hf, rfl⟩
        exact ((mem_K f).mp hf).2 i
      · intro hx
        exact ⟨_, single_mem_K i hx, by simp⟩
    _ = Ideal.span {(2 : Z2)} := twoIdeal_eq_span

/-- The coordinate ideals are Henselian by 2-adic completeness. -/
private theorem map_eval_K_henselian (i : ℕ) :
    HenselianRing Z2 (K.map (Pi.evalRingHom (fun _ : ℕ => Z2) i)) := by
  rw [map_eval_K, ← twoIdeal_eq_span]
  infer_instance

/-- Downward closure from the componentwise product proves Henselianity of `K`. -/
private theorem K_henselian : HenselianRing (ℕ → Z2) K := by
  let : HenselianRing (ℕ → Z2) (Ideal.pi (fun _ : ℕ => twoIdeal)) :=
    HenselianRing.pi _
  exact HenselianRing.of_le (I := K) (J := Ideal.pi (fun _ : ℕ => twoIdeal))
    inf_le_right

private theorem K_ne_bot : K ≠ ⊥ := by
  intro h
  have hx := single_mem_K 0 two_mem
  rw [h, Ideal.mem_bot] at hx
  exact two_ne_zero (by simpa using congrFun hx 0)

private theorem K_ne_top : K ≠ ⊤ := by
  intro h
  have hm := map_eval_K 0
  rw [h, Ideal.map_top, ← twoIdeal_eq_span] at hm
  exact (Ideal.IsMaximal.ne_top (inferInstance : twoIdeal.IsMaximal)) hm.symm

private theorem K_not_isNilpotent : ¬ IsNilpotent K := by
  rintro ⟨n, hn⟩
  have hx := Ideal.pow_mem_pow (single_mem_K 0 two_mem) n
  rw [hn] at hx
  have hz := Ideal.mem_bot.mp hx
  have h2 : (2 : Z2) ^ n = 0 := by
    simpa using congrFun hz 0
  exact (pow_ne_zero n two_ne_zero) h2

/-- Constant `2` belongs to every coordinate ideal but is not finitely supported. -/
private theorem constant_two_not_mem : (fun _ : ℕ => (2 : Z2)) ∉ K := by
  intro h
  obtain ⟨s, hs⟩ := ((mem_K _).mp h).1
  have hn : s.sup id + 1 ∉ s := by
    intro hn
    exact Nat.not_succ_le_self _ (Finset.le_sup (f := id) hn)
  exact two_ne_zero (hs _ hn)

private theorem K_lt_pi_maps :
    K < Ideal.pi (fun i : ℕ => K.map (Pi.evalRingHom (fun _ : ℕ => Z2) i)) := by
  simp only [map_eval_K, ← twoIdeal_eq_span]
  refine lt_iff_le_not_ge.mpr ⟨inf_le_right, ?_⟩
  intro h
  exact constant_two_not_mem (h ((Ideal.mem_pi _ _).mpr (fun _ => two_mem)))

/-- A fixed infinite Henselian ideal, with nontrivial boundaries and strict
containment in the product of its actual coordinate images. -/
example :
    HenselianRing (ℕ → Z2) K ∧
    (∀ i : ℕ, K.map (Pi.evalRingHom (fun _ : ℕ => Z2) i) = Ideal.span {(2 : Z2)}) ∧
    (∀ i : ℕ, HenselianRing Z2 (K.map (Pi.evalRingHom (fun _ : ℕ => Z2) i))) ∧
    K ≠ ⊥ ∧ K ≠ ⊤ ∧ ¬ IsNilpotent K ∧
    K < Ideal.pi (fun i : ℕ => K.map (Pi.evalRingHom (fun _ : ℕ => Z2) i)) :=
  ⟨K_henselian, map_eval_K, map_eval_K_henselian, K_ne_bot, K_ne_top,
    K_not_isNilpotent, K_lt_pi_maps⟩

/-- The arbitrary-ideal criterion applies to the independently constructed ideal. -/
example : HenselianRing (ℕ → Z2) K :=
  (HenselianRing.pi_iff_map K).mpr map_eval_K_henselian

#print axioms K_henselian
#print axioms map_eval_K_henselian

end HenselianProductCriterion
