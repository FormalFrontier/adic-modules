/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Fixed points of ideal-adically contracting maps

An ideal-adically complete module admits a unique fixed point in `I • ⊤` for a
self-map preserving that submodule and gaining one ideal power on differences
between its elements.

The hypotheses use the given module action and do not require a choice of topology.
-/

@[expose] public section

universe u v

/-- A map preserving `I • ⊤` and gaining one ideal power on differences there has
a unique fixed point in `I • ⊤`, provided the module is `I`-adically complete. -/
theorem IsAdicComplete.existsUnique_fixedPoint
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M] [IsAdicComplete I M]
    (f : M → M)
    (hmap : Set.MapsTo f (I • ⊤ : Submodule R M) (I • ⊤ : Submodule R M))
    (hgain : ∀ (n : ℕ) (x y : M),
      x ∈ I • (⊤ : Submodule R M) →
      y ∈ I • (⊤ : Submodule R M) →
      x - y ∈ I ^ n • (⊤ : Submodule R M) →
      f x - f y ∈ I ^ (n + 1) • (⊤ : Submodule R M)) :
    ∃! x : M, x ∈ I • (⊤ : Submodule R M) ∧ f x = x := by
  -- Iteration from zero stays in the invariant submodule.
  have horbit (n : ℕ) : f^[n] 0 ∈ I • (⊤ : Submodule R M) :=
    Function.Iterate.rec (fun x : M => x ∈ I • (⊤ : Submodule R M))
      (Submodule.zero_mem _) (fun _ hx => hmap hx) n
  have hsucc (n : ℕ) : f^[n + 1] 0 = f (f^[n] 0) :=
    Function.iterate_succ_apply' f n 0
  -- A common initial iteration gains the corresponding ideal power.
  have hdiff (n k : ℕ) (hnk : n ≤ k) :
      f^[k] 0 - f^[n] 0 ∈ I ^ n • (⊤ : Submodule R M) := by
    induction n generalizing k with
    | zero =>
        simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul, Submodule.mem_top]
    | succ n ih =>
        cases k with
        | zero => exact (Nat.not_succ_le_zero _ hnk).elim
        | succ k =>
            simpa only [Function.iterate_succ_apply'] using
              hgain n (f^[k] 0) (f^[n] 0) (horbit k) (horbit n)
                (ih k (Nat.le_of_succ_le_succ hnk))
  have hcauchy :
      ∀ {m n : ℕ}, m ≤ n →
        f^[m] 0 ≡ f^[n] 0 [SMOD (I ^ m • (⊤ : Submodule R M))] := by
    intro m n hmn
    exact (SModEq.sub_mem.mpr (hdiff m n hmn)).symm
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (M := M)
    (fun n : ℕ => f^[n] 0) hcauchy
  have hLmem : L ∈ I • (⊤ : Submodule R M) := by
    have hdiff : L - f^[1] 0 ∈ I • (⊤ : Submodule R M) := by
      simpa only [pow_one] using (SModEq.sub_mem.mp ((hL 1).symm))
    simpa only [sub_add_cancel] using
      (I • (⊤ : Submodule R M)).add_mem hdiff (horbit 1)
  -- Compare the image of the limit with the next orbit term at each precision.
  have hfix : f L = L := by
    apply (IsHausdorff.eq_iff_smodEq (I := I)).2
    intro n
    cases n with
    | zero =>
        simpa only [pow_zero, Submodule.one_smul] using
          (SModEq.top (R := R) (x := f L) (y := L))
    | succ n =>
        have hstep : f L ≡ f (f^[n] 0)
            [SMOD (I ^ (n + 1) • (⊤ : Submodule R M))] := by
          apply SModEq.sub_mem.mpr
          exact hgain n L (f^[n] 0) hLmem (horbit n)
            (SModEq.sub_mem.mp ((hL n).symm))
        have hnext : f (f^[n] 0) ≡ L
            [SMOD (I ^ (n + 1) • (⊤ : Submodule R M))] := by
          simpa only [hsucc n] using (hL (n + 1))
        exact hstep.trans hnext
  have hunique (x y : M)
      (hx : x ∈ I • (⊤ : Submodule R M))
      (hy : y ∈ I • (⊤ : Submodule R M))
      (hfx : f x = x) (hfy : f y = y) : x = y := by
    have hmem : ∀ n : ℕ, x - y ∈ I ^ n • (⊤ : Submodule R M) := by
      intro n
      induction n with
      | zero =>
          simpa only [pow_zero, Submodule.one_smul] using
            (Submodule.mem_top : x - y ∈ (⊤ : Submodule R M))
      | succ n hn =>
          simpa only [hfx, hfy] using hgain n x y hx hy hn
    exact (IsHausdorff.eq_iff_smodEq (I := I) (x := x) (y := y)).2 fun n =>
      SModEq.sub_mem.mpr (hmem n)
  refine ⟨L, ⟨hLmem, hfix⟩, ?_⟩
  intro y hy
  exact hunique y L hy.1 hLmem hy.2 hfix
