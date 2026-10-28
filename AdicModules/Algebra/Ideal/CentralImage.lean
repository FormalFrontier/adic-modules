/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Extension of left ideals and right-stable images

The left ideal spanned by a set is closed under right multiplication by any fixed
element commuting with every generator. Consequently, extension of a left ideal
along a homomorphism whose image is central is a two-sided target ideal.

Extension preserves ordered products of left ideals when the extension of the
first factor is two-sided. In particular, it suffices that the image of that
factor commutes with the target semiring. For a homomorphism with central image,
extension also preserves every nonnegative power. Degree zero follows separately
from the fact that the image of the source unit is the target unit.

Both semirings may be noncommutative, and their universes are independent.
Neither source ideal is required to be two-sided. Products retain the order of
their generators; the proofs use no source right-unit law.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} {A : Type v} [Semiring R] [Semiring A]

/-- Right multiplication by an element commuting with every generator preserves
its left-ideal span. The elements of the span need not commute with that element. -/
theorem mul_mem_span_of_commute {s : Set A} {a x : A}
    (hcomm : ∀ y ∈ s, y * a = a * y) (hx : x ∈ span s) :
    x * a ∈ span s := by
  let K : Ideal A :=
    { carrier := {y | y * a ∈ span s}
      zero_mem' := by
        change (0 : A) * a ∈ span s
        simpa only [zero_mul] using (span s).zero_mem
      add_mem' := by
        intro y z hy hz
        change (y + z) * a ∈ span s
        rw [add_mul]
        exact (span s).add_mem hy hz
      smul_mem' := by
        intro c y hy
        change (c * y) * a ∈ span s
        rw [mul_assoc]
        exact (span s).mul_mem_left c hy }
  have hs : s ⊆ K := by
    intro y hy
    change y * a ∈ span s
    rw [hcomm y hy]
    exact (span s).mul_mem_left a (subset_span hy)
  have hle : span s ≤ K := span_le.mpr hs
  exact hle hx

/-- The image ideal is closed under right multiplication by a fixed element if
that element commutes with the homomorphic image of every element of the source
ideal. In particular, a homomorphism central on the source ideal gives closure
under every right multiplier, without a commutativity assumption on either semiring. -/
theorem mul_mem_map_of_commute (σ : R →+* A) (I : Ideal R) {a x : A}
    (hcomm : ∀ r ∈ I, σ r * a = a * σ r) (hx : x ∈ I.map σ) :
    x * a ∈ I.map σ := by
  change x ∈ span (σ '' (I : Set R)) at hx
  change x * a ∈ span (σ '' (I : Set R))
  apply mul_mem_span_of_commute (s := σ '' (I : Set R)) ?_ hx
  intro y hy
  obtain ⟨r, hr, rfl⟩ := hy
  exact hcomm r hr

/-- A homomorphic image of a left ideal is two-sided if the image of each element
of the source ideal commutes with every element of the target semiring. -/
theorem isTwoSided_map_of_commute (σ : R →+* A) (I : Ideal R)
    (hcomm : ∀ r ∈ I, ∀ a : A, Commute (σ r) a) :
    (I.map σ).IsTwoSided := by
  constructor
  intro x a hx
  apply mul_mem_map_of_commute σ I ?_ hx
  intro r hr
  exact (hcomm r hr _).eq

/-- Extension preserves ordered products of left ideals when the extension of
its first factor is two-sided. -/
theorem map_mul_of_isTwoSided (σ : R →+* A) (I J : Ideal R)
    [(I.map σ).IsTwoSided] :
    (I * J).map σ = I.map σ * J.map σ := by
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr (Ideal.mul_le.mpr ?_)
    intro i hi j hj
    change σ (i * j) ∈ I.map σ * J.map σ
    rw [σ.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem σ hi) (Ideal.mem_map_of_mem σ hj)
  · rcases (inferInstance : (I.map σ).IsTwoSided) with ⟨hright⟩
    refine Ideal.mul_le.mpr ?_
    intro x hx y hy
    change y ∈ Ideal.span (σ '' (J : Set R)) at hy
    -- Induct on the second span first, keeping the first factor arbitrary.
    suffices h : ∀ z ∈ I.map σ, z * y ∈ (I * J).map σ from h x hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨j, hj, rfl⟩
        intro z hz
        change z ∈ Ideal.span (σ '' (I : Set R)) at hz
        induction hz using Submodule.span_induction with
        | mem z hz =>
            rcases hz with ⟨i, hi, rfl⟩
            rw [← σ.map_mul]
            exact Ideal.mem_map_of_mem σ (Ideal.mul_mem_mul hi hj)
        | zero =>
            simpa only [zero_mul] using (Ideal.zero_mem ((I * J).map σ))
        | add z₁ z₂ hz₁ hz₂ ih₁ ih₂ =>
            rw [add_mul]
            exact Ideal.add_mem _ ih₁ ih₂
        | smul a z hz ih =>
            change (a * z) * σ j ∈ (I * J).map σ
            rw [mul_assoc]
            exact Ideal.mul_mem_left _ a ih
    | zero =>
        intro z hz
        simpa only [mul_zero] using (Ideal.zero_mem ((I * J).map σ))
    | add y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
        intro z hz
        rw [mul_add]
        exact Ideal.add_mem _ (ih₁ z hz) (ih₂ z hz)
    | smul b y hy ih =>
        intro z hz
        change z * (b * y) ∈ (I * J).map σ
        rw [← mul_assoc]
        apply ih (z * b)
        apply hright
        exact hz

/-- Extension preserves the ordered product of two left ideals if the images of
all elements of the first ideal commute with arbitrary target elements.

The centrality assumption is needed only on the first ideal, not on the whole
source semiring or on the second ideal. -/
theorem map_mul_of_commute (σ : R →+* A) (I J : Ideal R)
    (hσ : ∀ i ∈ I, ∀ a : A, Commute (σ i) a) :
    (I * J).map σ = I.map σ * J.map σ := by
  let : (I.map σ).IsTwoSided := isTwoSided_map_of_commute σ I hσ
  exact map_mul_of_isTwoSided σ I J

/-- A semiring homomorphism with central image preserves ordered products of
left ideals. No commutativity of either ambient semiring is required. -/
theorem map_mul_of_commute_all (σ : R →+* A)
    (hσ : ∀ r : R, ∀ a : A, Commute (σ r) a) (I J : Ideal R) :
    (I * J).map σ = I.map σ * J.map σ :=
  map_mul_of_commute σ I J (fun i _ a => hσ i a)

/-- Extension preserves every nonnegative power of a left ideal whose image
ideal is two-sided, including degree zero. -/
theorem map_pow_of_isTwoSided (σ : R →+* A) (I : Ideal R)
    [(I.map σ).IsTwoSided] (n : ℕ) :
    (I ^ n).map σ = I.map σ ^ n := by
  have h : ∀ n : ℕ,
      (I ^ n).map σ = I.map σ ^ n ∧ ((I ^ n).map σ).IsTwoSided := by
    intro n
    induction n with
    | zero =>
        have hzero : (I ^ 0).map σ = I.map σ ^ 0 := by
          rw [Submodule.pow_zero, Submodule.pow_zero]
          rw [Ideal.one_eq_top, Ideal.one_eq_top]
          apply top_unique
          intro a _
          have h1 : σ (1 : R) ∈ (⊤ : Ideal R).map σ :=
            mem_map_of_mem σ (by trivial)
          simpa only [σ.map_one, mul_one] using
            ((⊤ : Ideal R).map σ).mul_mem_left a h1
        refine ⟨hzero, ?_⟩
        rw [hzero, Submodule.pow_zero, Ideal.one_eq_top]
        constructor
        intro x a hx
        trivial
    | succ n ih =>
        rcases ih with ⟨heq, hstable⟩
        let : ((I ^ n).map σ).IsTwoSided := hstable
        let : (I.map σ ^ n).IsTwoSided := by
          rw [← heq]
          exact hstable
        have hsucc : (I ^ (n + 1)).map σ = I.map σ ^ (n + 1) := by
          rw [Submodule.pow_succ, Submodule.pow_succ]
          rw [map_mul_of_isTwoSided σ, heq]
        refine ⟨hsucc, ?_⟩
        rw [hsucc, Submodule.pow_succ]
        suffices hprod : ∀ U V : Ideal A, V.IsTwoSided → (U * V).IsTwoSided by
          exact hprod _ _ inferInstance
        intro U V hV
        rcases hV with ⟨hright⟩
        have hclosure : ∀ x a : A, x ∈ U * V → x * a ∈ U * V := by
          intro x a hx
          let K : Ideal A :=
            { carrier := {y | y * a ∈ U * V}
              zero_mem' := by
                change (0 : A) * a ∈ U * V
                simpa only [zero_mul] using (U * V).zero_mem
              add_mem' := by
                intro y z hy hz
                change (y + z) * a ∈ U * V
                rw [add_mul]
                exact (U * V).add_mem hy hz
              smul_mem' := by
                intro c y hy
                change (c * y) * a ∈ U * V
                rw [mul_assoc]
                exact (U * V).mul_mem_left c hy }
          have hle : U * V ≤ K := by
            refine Ideal.mul_le.mpr ?_
            intro u hu v hv
            change (u * v) * a ∈ U * V
            rw [mul_assoc]
            apply Ideal.mul_mem_mul hu
            apply hright
            exact hv
          exact hle hx
        constructor
        intro x a hx
        exact hclosure _ _ hx
  exact (h n).1

/-- A semiring homomorphism with central image preserves every nonnegative
power of a left ideal, including degree zero. -/
theorem map_pow_of_commute (σ : R →+* A)
    (hσ : ∀ r : R, ∀ a : A, Commute (σ r) a) (I : Ideal R) (n : ℕ) :
    (I ^ n).map σ = I.map σ ^ n := by
  let : (I.map σ).IsTwoSided :=
    isTwoSided_map_of_commute σ I (fun r _ a => hσ r a)
  exact map_pow_of_isTwoSided σ I n

/-- Extension preserves two given right-append multiplication recurrences when
 their seeds agree and every used source prefix has a two-sided image.

Stability is required only strictly below the horizon, and the seed may be any
left ideal. -/
theorem map_eq_of_mul_rec (σ : R →+* A) (N : ℕ)
    (P I : ℕ → Ideal R) (Q : ℕ → Ideal A)
    (h0 : (P 0).map σ = Q 0)
    (hP : ∀ k, k < N → P (k + 1) = P k * I k)
    (hQ : ∀ k, k < N → Q (k + 1) = Q k * (I k).map σ)
    (hstable : ∀ k, k < N → ((P k).map σ).IsTwoSided) :
    ∀ n, n ≤ N → (P n).map σ = Q n := by
  intro n
  induction n with
  | zero =>
      intro _
      exact h0
  | succ k ih =>
      intro hn
      have hk : k < N := Nat.lt_of_succ_le hn
      let : ((P k).map σ).IsTwoSided := hstable k hk
      calc
        (P (k + 1)).map σ = (P k * I k).map σ := by rw [hP k hk]
        _ = (P k).map σ * (I k).map σ := map_mul_of_isTwoSided σ (P k) (I k)
        _ = Q k * (I k).map σ := by rw [ih (Nat.le_of_lt hk)]
        _ = Q (k + 1) := (hQ k hk).symm

/-- Extension preserves two given multiplication recurrences when the target
factors agree with the images of the source factors below the horizon. -/
theorem map_eq_of_mul_rec_of_factor_maps (σ : R →+* A) (N : ℕ)
    (P I : ℕ → Ideal R) (Q J : ℕ → Ideal A)
    (h0 : (P 0).map σ = Q 0)
    (hP : ∀ k, k < N → P (k + 1) = P k * I k)
    (hQ : ∀ k, k < N → Q (k + 1) = Q k * J k)
    (hfactor : ∀ k, k < N → (I k).map σ = J k)
    (hstable : ∀ k, k < N → ((P k).map σ).IsTwoSided) :
    ∀ n, n ≤ N → (P n).map σ = Q n := by
  refine map_eq_of_mul_rec σ N P I Q h0 hP ?_ hstable
  intro k hk
  rw [hQ k hk, hfactor k hk]

/-- The left-associated product obtained by appending factors in increasing order,
starting from an arbitrary seed. -/
def leftProd (seed : Ideal R) (I : ℕ → Ideal R) : ℕ → Ideal R
  | 0 => seed
  | k + 1 => leftProd seed I k * I k

@[simp] theorem leftProd_zero (seed : Ideal R) (I : ℕ → Ideal R) :
    leftProd seed I 0 = seed := rfl

@[simp] theorem leftProd_succ (seed : Ideal R) (I : ℕ → Ideal R) (k : ℕ) :
    leftProd seed I (k + 1) = leftProd seed I k * I k := rfl

/-- Splitting a finite left-associated product after a prefix gives the product
of the remaining factors starting from that prefix. -/
theorem leftProd_add (S : Ideal R) (F : ℕ → Ideal R) (N M : ℕ) :
    leftProd S F (N + M) =
      leftProd (leftProd S F N) (fun k => F (N + k)) M := by
  induction M with
  | zero => rfl
  | succ M ih =>
      rw [Nat.add_succ, leftProd_succ, leftProd_succ, ih]

/-- A finite left-associated product depends only on its seed and the factors
strictly below its length. No closure assumptions are needed. -/
theorem leftProd_congr {S T : Ideal R} {I J : ℕ → Ideal R} (n : ℕ)
    (hseed : S = T) (hfactor : ∀ k, k < n → I k = J k) :
    leftProd S I n = leftProd T J n := by
  revert hfactor
  induction n with
  | zero =>
      intro _
      exact hseed
  | succ n ih =>
      intro hfactor
      have hprefix : ∀ k, k < n → I k = J k :=
        fun k hk => hfactor k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rw [leftProd_succ, leftProd_succ, ih hprefix, hfactor n (Nat.lt_succ_self n)]

/-- Ordered seeds and factor inclusions below the length give inclusion of
finite left-associated products. -/
theorem leftProd_mono {S T : Ideal R} {I J : ℕ → Ideal R} (n : ℕ)
    (hseed : S ≤ T) (hfactor : ∀ k, k < n → I k ≤ J k) :
    leftProd S I n ≤ leftProd T J n := by
  revert hfactor
  induction n with
  | zero =>
      intro _
      exact hseed
  | succ n ih =>
      intro hfactor
      have hprefix : ∀ k, k < n → I k ≤ J k :=
        fun k hk => hfactor k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rw [leftProd_succ, leftProd_succ]
      refine Ideal.mul_le.mpr ?_
      intro x hx y hy
      exact Ideal.mul_mem_mul (ih hprefix hx) (hfactor n (Nat.lt_succ_self n) hy)

/-- The image of a finite left-associated ideal product is contained in the
left-associated product of its mapped seed and factors. -/
theorem map_leftProd_le (σ : R →+* A) (N : ℕ) (S : Ideal R) (I : ℕ → Ideal R) :
    (leftProd S I N).map σ ≤ leftProd (S.map σ) (fun k => (I k).map σ) N := by
  induction N with
  | zero =>
      simpa only [leftProd_zero] using (le_refl (S.map σ))
  | succ n ih =>
      rw [leftProd_succ, leftProd_succ]
      refine Ideal.map_le_iff_le_comap.mpr (Ideal.mul_le.mpr ?_)
      intro x hx y hy
      change σ (x * y) ∈
        leftProd (S.map σ) (fun k => (I k).map σ) n * (I n).map σ
      rw [σ.map_mul]
      exact Ideal.mul_mem_mul (ih (Ideal.mem_map_of_mem σ hx))
        (Ideal.mem_map_of_mem σ hy)

/-- Extension preserves a finite left-associated product with independently
specified target seed and factors. Only source prefixes strictly below the length
need two-sided images; no stability of the terminal product is required. -/
theorem map_leftProd_of_factor_maps (σ : R →+* A) (N : ℕ)
    (S : Ideal R) (T : Ideal A) (I : ℕ → Ideal R) (J : ℕ → Ideal A)
    (hseed : S.map σ = T)
    (hfactor : ∀ k, k < N → (I k).map σ = J k)
    (hstable : ∀ k, k < N → ((leftProd S I k).map σ).IsTwoSided) :
    (leftProd S I N).map σ = leftProd T J N := by
  exact map_eq_of_mul_rec_of_factor_maps σ N
    (leftProd S I) I (leftProd T J) J hseed
    (fun _ _ => rfl) (fun _ _ => rfl) hfactor hstable N (Nat.le_refl N)

/- Two consecutive blocks with independently specified target factors have compatible
concatenated products. -/
example (σ : R →+* A) (N M : ℕ)
    (S S1 : Ideal R) (T T1 : Ideal A)
    (I K C : ℕ → Ideal R) (J L D : ℕ → Ideal A)
    (hseed : S.map σ = T)
    (hI : ∀ k, k < N → (I k).map σ = J k)
    (hstableI : ∀ k, k < N → ((leftProd S I k).map σ).IsTwoSided)
    (hS1 : S1 = leftProd S I N) (hT1 : T1 = leftProd T J N)
    (hK : ∀ k, k < M → (K k).map σ = L k)
    (hstableK : ∀ k, k < M → ((leftProd S1 K k).map σ).IsTwoSided)
    (hfront : ∀ k, k < N → C k = I k ∧ D k = J k)
    (htail : ∀ k, k < M → C (N + k) = K k ∧ D (N + k) = L k) :
    leftProd S C (N + M) = leftProd S1 K M ∧
      leftProd T D (N + M) = leftProd T1 L M ∧
      (leftProd S C (N + M)).map σ = leftProd T D (N + M) := by
  have hfirst : (leftProd S I N).map σ = leftProd T J N :=
    map_leftProd_of_factor_maps σ N S T I J hseed hI hstableI
  have hboundary : S1.map σ = T1 := by
    rw [hS1, hT1]
    exact hfirst
  have hsecond : (leftProd S1 K M).map σ = leftProd T1 L M :=
    map_leftProd_of_factor_maps σ M S1 T1 K L hboundary hK hstableK
  have hsource : leftProd S C (N + M) = leftProd S1 K M := by
    have hprefix : leftProd S C N = leftProd S I N :=
      leftProd_congr N rfl (fun k hk => (hfront k hk).1)
    rw [leftProd_add S C N M]
    exact leftProd_congr M (hprefix.trans hS1.symm)
      (fun k hk => (htail k hk).1)
  have htarget : leftProd T D (N + M) = leftProd T1 L M := by
    have hprefix : leftProd T D N = leftProd T J N :=
      leftProd_congr N rfl (fun k hk => (hfront k hk).2)
    rw [leftProd_add T D N M]
    exact leftProd_congr M (hprefix.trans hT1.symm)
      (fun k hk => (htail k hk).2)
  refine ⟨hsource, htarget, ?_⟩
  rw [hsource, htarget]
  exact hsecond

example (σ : R →+* A) (N : ℕ)
    (S S' : Ideal R) (T T' : Ideal A)
    (I K : ℕ → Ideal R) (J L : ℕ → Ideal A)
    (hseed₁ : S.map σ = T) (hseed₂ : S'.map σ = T')
    (hfactor₁ : ∀ k, k < N → (I k).map σ = J k)
    (hfactor₂ : ∀ k, k < N → (K k).map σ = L k)
    (hstable₁ : ∀ k, k < N → ((leftProd S I k).map σ).IsTwoSided)
    (hstable₂ : ∀ k, k < N → ((leftProd S' K k).map σ).IsTwoSided)
    (hseed_le : T ≤ T') (hfactor_le : ∀ k, k < N → J k ≤ L k) :
    (leftProd S I N).map σ ≤ (leftProd S' K N).map σ := by
  rw [map_leftProd_of_factor_maps σ N S T I J hseed₁ hfactor₁ hstable₁,
    map_leftProd_of_factor_maps σ N S' T' K L hseed₂ hfactor₂ hstable₂]
  exact leftProd_mono (R := A) N hseed_le hfactor_le

example (σ : R →+* A) (N : ℕ) (S : Ideal R) (T : Ideal A)
    (I : ℕ → Ideal R) (J : ℕ → Ideal A)
    (hseedLE : S.map σ ≤ T)
    (hfactorLE : ∀ k, k < N → (I k).map σ ≤ J k) :
    (leftProd S I N).map σ ≤ leftProd T J N := by
  exact (map_leftProd_le σ N S I).trans
    (leftProd_mono (R := A) N hseedLE hfactorLE)

end Ideal

namespace Ideal

/-- Appending a factor makes the left-associated product a subideal of that factor. -/
theorem leftProd_succ_le_factor {R : Type*} [Semiring R] (S : Ideal R) (I : ℕ → Ideal R) (n : ℕ) :
    leftProd S I (n + 1) ≤ I n := by
  rw [leftProd_succ]
  refine Ideal.mul_le.mpr ?_
  intro x _ y hy
  exact (I n).mul_mem_left x hy

example {R : Type*} {A : Type*} [Semiring R] [Semiring A]
    (σ : R →+* A) (n : ℕ) (S : Ideal R) (I : ℕ → Ideal R)
    (K : Ideal A) (hfactor : (I n).map σ ≤ K) :
    (leftProd S I (n + 1)).map σ ≤ K := by
  exact (map_leftProd_le σ (n + 1) S I).trans
    ((leftProd_succ_le_factor (R := A) (S.map σ) (fun k => (I k).map σ) n).trans
      hfactor)

end Ideal

namespace Ideal

/-- A left-associated product lies in a left ideal containing a used factor
if that ideal is closed under right multiplication by all later used factors. -/
theorem leftProd_le_of_factor_le {R : Type*} [Semiring R]
    {S T : Ideal R} {I : ℕ → Ideal R} {N j : ℕ}
    (hj : j < N) (hfactor : I j ≤ T)
    (hclosed : ∀ k, j < k → k < N → ∀ x ∈ T, ∀ y ∈ I k, x * y ∈ T) :
    leftProd S I N ≤ T := by
  revert hj hclosed
  induction N with
  | zero =>
      intro hj _
      exact (Nat.not_lt_zero j hj).elim
  | succ n ih =>
      intro hj hclosed
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjn | hlast
      · have hprefix : ∀ k, j < k → k < n → ∀ x ∈ T, ∀ y ∈ I k, x * y ∈ T :=
          fun k hjk hk => hclosed k hjk (Nat.lt_trans hk (Nat.lt_succ_self n))
        rw [leftProd_succ]
        refine Ideal.mul_le.mpr ?_
        intro x hx y hy
        exact hclosed n hjn (Nat.lt_succ_self n) x (ih hjn hprefix hx) y hy
      · subst j
        exact (leftProd_succ_le_factor S I n).trans hfactor

/-- A left-associated product lies in any two-sided ideal containing one of its
used factors. -/
theorem leftProd_le_of_factor_le_of_isTwoSided {R : Type*} [Semiring R]
    {S T : Ideal R} {I : ℕ → Ideal R} {N j : ℕ} [T.IsTwoSided]
    (hj : j < N) (hfactor : I j ≤ T) :
    leftProd S I N ≤ T := by
  rcases (inferInstance : T.IsTwoSided) with ⟨hright⟩
  apply leftProd_le_of_factor_le hj hfactor
  intro k _ _ x hx y _
  exact hright y hx

example {R : Type*} [Semiring R] (S T : Ideal R) (I : ℕ → Ideal R)
    (hfactor : I 0 ≤ T)
    (hclosed : ∀ x ∈ T, ∀ y ∈ I 1, x * y ∈ T) :
    leftProd S I 2 ≤ T := by
  refine leftProd_le_of_factor_le (j := 0) (by decide) hfactor ?_
  intro k hk hkN x hx y hy
  have hk1 : k = 1 := le_antisymm (Nat.le_of_lt_succ hkN) hk
  subst k
  exact hclosed x hx y hy

end Ideal

namespace Ideal

/-- At a positive length, a seeded left-associated product is its seed multiplied
by the left-associated product starting at the top ideal. -/
theorem leftProd_eq_mul_leftProd_top_of_pos {R : Type*} [Semiring R]
    (S : Ideal R) (L : ℕ → Ideal R) (n : ℕ) (hn : 0 < n) :
    leftProd S L n = S * leftProd (⊤ : Ideal R) L n := by
  have htop (I : Ideal R) : (⊤ : Ideal R) * I = I :=
    show (⊤ : Ideal R) * I = I from by
      apply le_antisymm
      · refine Ideal.mul_le.mpr ?_
        intro a _ b hb
        exact I.mul_mem_left a hb
      · intro x hx
        have h1 : (1 : R) ∈ (⊤ : Ideal R) := by trivial
        simpa only [one_mul] using (Ideal.mul_mem_mul h1 hx)
  have hassoc (I J K : Ideal R) : (I * J) * K = I * (J * K) :=
    show (I * J) * K = I * (J * K) from by
      have hspan (U V : Ideal R) :
          U * V = span {x : R | ∃ a ∈ U, ∃ b ∈ V, a * b = x} := by
        apply le_antisymm
        · refine Ideal.mul_le.mpr ?_
          intro a ha b hb
          exact subset_span ⟨a, ha, b, hb, rfl⟩
        · refine span_le.mpr ?_
          intro x hx
          obtain ⟨a, ha, b, hb, rfl⟩ := hx
          exact Ideal.mul_mem_mul ha hb
      apply le_antisymm
      · refine Ideal.mul_le.mpr ?_
        intro x hx z hz
        rw [hspan I J] at hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
            obtain ⟨i, hi, j, hj, rfl⟩ := hx
            rw [mul_assoc i j z]
            exact Ideal.mul_mem_mul hi (Ideal.mul_mem_mul hj hz)
        | zero =>
            simpa only [zero_mul] using (Ideal.zero_mem (I * (J * K)))
        | add x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
            rw [add_mul x₁ x₂ z]
            exact Ideal.add_mem _ ih₁ ih₂
        | smul a x hx ih =>
            change (a * x) * z ∈ I * (J * K)
            rw [mul_assoc a x z]
            exact Ideal.mul_mem_left _ a ih
      · refine Ideal.mul_le.mpr ?_
        intro i hi y hy
        have h : ∀ a : R, i * (a * y) ∈ (I * J) * K := by
          rw [hspan J K] at hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
              obtain ⟨j, hj, k, hk, rfl⟩ := hy
              intro a
              rw [← mul_assoc a j k, ← mul_assoc i (a * j) k]
              exact Ideal.mul_mem_mul (Ideal.mul_mem_mul hi (J.mul_mem_left a hj)) hk
          | zero =>
              intro a
              simpa only [mul_zero] using (Ideal.zero_mem ((I * J) * K))
          | add y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
              intro a
              rw [mul_add a y₁ y₂, mul_add i (a * y₁) (a * y₂)]
              exact Ideal.add_mem _ (ih₁ a) (ih₂ a)
          | smul b y hy ih =>
              intro a
              change i * (a * (b * y)) ∈ (I * J) * K
              rw [← mul_assoc a b y]
              exact ih (a * b)
        simpa only [one_mul] using h (1 : R)
  have hsucc (k : ℕ) :
      leftProd S L (k + 1) = S * leftProd (⊤ : Ideal R) L (k + 1) := by
    induction k with
    | zero =>
        calc
          leftProd S L (0 + 1) = S * L 0 := by
            rw [leftProd_succ, leftProd_zero]
          _ = S * leftProd (⊤ : Ideal R) L (0 + 1) := by
            rw [leftProd_succ, leftProd_zero, htop]
    | succ k ih =>
        calc
          leftProd S L (k + 1 + 1) = leftProd S L (k + 1) * L (k + 1) :=
            leftProd_succ S L (k + 1)
          _ = (S * leftProd (⊤ : Ideal R) L (k + 1)) * L (k + 1) := by
            rw [ih]
          _ = S * (leftProd (⊤ : Ideal R) L (k + 1) * L (k + 1)) :=
            hassoc S (leftProd (⊤ : Ideal R) L (k + 1)) (L (k + 1))
          _ = S * leftProd (⊤ : Ideal R) L (k + 1 + 1) :=
            congrArg (fun B : Ideal R => S * B)
              (leftProd_succ (⊤ : Ideal R) L (k + 1)).symm
  cases n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n => exact hsucc n

/- A computed block of the first two factors determines the seeded product of
length two for every seed ideal. -/
example {R : Type*} [Semiring R]
    (S B : Ideal R) (L : ℕ → Ideal R)
    (hblock : leftProd (⊤ : Ideal R) L 2 = B) :
    leftProd S L 2 = S * B := by
  calc
    leftProd S L 2 = S * leftProd (⊤ : Ideal R) L 2 :=
      leftProd_eq_mul_leftProd_top_of_pos S L 2 (by decide)
    _ = S * B := by rw [hblock]

end Ideal
