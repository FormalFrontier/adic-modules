# Using adic-modules

This library builds on mathlib's ideals, modules, canonical integer actions,
inverse-limit adic completion, valuations, localization and uniform-space
completion. Import `AdicModules` for the public library API, or import a narrower
module below. The files under `AdicModulesTest` contain downstream uses; some
also expose separately importable named concrete results. The four left-ideal
model files keep their declarations private and do not expose a new general
theorem API. These models are not re-exported by `AdicModules`.
The root exports `Ideal.sup_pow_eq_top_of_sup_eq_top` for comaximal powers of
arbitrary semiring left ideals and `Ideal.dense_iff_sup_eq_top_of_hasBasis` for
density in a supplied ring ideal-power topology, both with written proofs.
The dense-subsemiring span-closure comparison uses additive closure, continuous
dense images at selected generators and span induction. Its five model files
retain original span and closure calculations independent of the comparison;
the real model also applies it privately to the rational axis.
The aggregate `AdicModulesTest.Axioms` imports only `AdicModules`: it imports
none of the model files and performs no axiom census. Proof checking requires
a transitive audit of all declarations, including private, generated, test and
imported declarations. The application guides and complete current module map
(**50 production sources including root + 64 tests/models/audit imports**) follow.
The [results reference](Results.md) preserves the expanded mathematical catalogue,
including completion–tensor alternatives, Hensel statements and
Frobenius/Teichmüller interfaces.

## Characteristic zero of Witt vectors

Import [`AdicModules.RingTheory.WittVector`](../AdicModules/RingTheory/WittVector.lean)
(or the public root). For `p : ℕ` with `[Fact p.Prime]` and `R : Type u` with
`[CommRing R]` and `[CharP R p]`, `WittVector.charZero.{u} p R` supplies
`CharZero (WittVector p R)`, with no restriction on `u`. No field, perfectness,
finiteness, domain, reducedness or extra `Nontrivial` premise is needed.
Use the standard `CharZero` API, such as `Nat.cast_ne_zero` and `Int.cast_injective`.

The proof embeds `ℤ_[p]` into `WittVector p (ZMod p)` via Mathlib's inverse
comparison, then uses `ZMod.castHom` and injective coefficientwise `WittVector.map`.
The separately imported [examples](../AdicModulesTest/RingTheory/WittVector.lean)
prove `(3 : WittVector 3 (ZMod 3)) ≠ 0` and
`(3 : WittVector 3 ((ZMod 3)[X])) ≠ 0`. The second coefficient ring is
nonperfect and not a field.

## Uniform bounded torsion

`Module.IsKilledByIdealPower R M I` means that **one exponent works for the
whole module**: some power of `I` annihilates every element. This is stronger
than choosing an exponent separately for each element. The finite-module bridge
identifies the uniform condition with `Ideal.primaryComponent M I = ⊤` under
`Module.Finite R M`; do not drop that hypothesis.

The [bounded-torsion module](../AdicModules/BoundedIdealPowerTorsion.lean)
provides monotonicity, submodule, surjection, quotient and extension lemmas.
Submodule and surjective-image results work over a commutative semiring and an
additive commutative monoid with a module structure. Quotient and extension
results retain their commutative-ring/additive-group hypotheses. The
finite-module primary-component comparison is over a commutative ring;
`Module.Finite` means finite generation, not a finite underlying set.
For a submodule killed by `I ^ n` and quotient killed by `I ^ m`, the explicit
extension lemma uses exponent `n + m`. The
[ordinary-import client](../AdicModulesTest/BoundedIdealPowerTorsion.lean)
shows both the specified-exponent and existential-bounded interfaces.

The [primary-component module](../AdicModules/PrimaryComponent.lean) instead
works with element-dependent ideal powers. For an exact pair of modules over a
Dedekind domain, its height-one component maps are exact if the **source** is
torsion; no other torsion, finiteness or uniform exponent premise is present.
For abelian groups, the integer prime `(p)` has the ordinary `p`-primary
subgroup as its component, and maps restricted to these ordinary subgroups
are exact when the source group is torsion. Read the
[manual reference](PrimaryComponent.md) and its
[ordinary-import client](../AdicModulesTest/PrimaryComponent.lean) for signatures.

## Finite-power completion kernels

Import [`AdicModules.AdicCompletion.Kernel`](../AdicModules/AdicCompletion/Kernel.lean)
or the public root for `AdicCompletion.pow_smul_top_eq_ker_eval_of_fg_pow`:

```lean
{R : Type u} [CommRing R] {I : Ideal R}
{M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
(h : (I ^ n).FG) :
  (I ^ n) • (⊤ : Submodule R (AdicCompletion I M)) =
    (AdicCompletion.eval I M n).ker
```

Use `AdicCompletion.pow_smul_top_eq_ker_eval_of_fg_pow (I := I) (M := M) h`
for the selected exponent. Only that ideal power must be finitely generated;
there is no separate `I.FG`, finite-module, Noetherian, completeness,
separatedness or kernel-equality premise. The universes `u` and `v` are
independent. The completion, scalar action and evaluation are Mathlib's existing
ones. At degree zero the quotient is trivial and the evaluation kernel is top.

The proof adapts Mathlib's `AdicCompletion.pow_smul_top_eq_ker_eval` argument.
Given `hI : I.FG`, use `Ideal.FG.pow (n := n) hI` for the power hypothesis to
recover its conclusion. The separately imported
[private client](../AdicModulesTest/AdicCompletionKernel.lean) includes this
recovery and a separate fixed-power theorem use. Its independent integer `(2)`
calibration uses Mathlib's kernel theorem and `Int.quotientSpanNatEquivZMod 2`
directly: evaluation of the canonical image of `1` at degree one is nonzero.
For the same inputs at degree zero, the kernel is top and the ideal quotient
has characteristic one. These residue calculations assert no characteristic
of the completion.

## Restricting scalars in adic completions

Import [`AdicModules.AdicCompletion.RestrictScalars`](../AdicModules/AdicCompletion/RestrictScalars.lean)
alone or the `AdicModules` public root. For commutative rings `R` and `S`, an
`Algebra R S`, an additive commutative group `M` carrying compatible `R`- and
`S`-module structures with `IsScalarTower R S M`, and any `I : Ideal R`, the
native inverse-limit completions are equivalent as `R`-modules:

```lean
AdicCompletion.restrictScalarsEquiv I M :
  AdicCompletion (I.map (algebraMap R S)) M ≃ₗ[R] AdicCompletion I M
```

The forward direction goes **from the extended ideal over `S` to the original
ideal over `R`**; `.symm` reverses it. The `R`-module structure on the source
completion is the restriction of its `S`-module structure. This comparison
requires no finite generation, Noetherianity, flatness, separatedness,
completeness, nontriviality or injectivity/surjectivity of `algebraMap R S`.
It is neither a module base-change equivalence nor a claim that an arbitrary
adic completion satisfies a separate completeness predicate.

At level `n`, `map_pow_smul_top_restrictScalars I n` identifies the extended
ideal's power-filtration submodule after restriction of scalars with
`I ^ n • ⊤`. The `R`-linear `restrictScalarsLevelEquiv I M n` compares the
quotients in the same orientation as the completion equivalence.
`restrictScalarsLevelEquiv_mk` and `restrictScalarsLevelEquiv_symm_mk` preserve
representatives in both directions;
`restrictScalarsLevelEquiv_transitionMap` and
`restrictScalarsLevelEquiv_symm_transitionMap` commute with the native
`AdicCompletion.transitionMap` for every `m ≤ n`. Pointwise level comparison
therefore yields the forward and inverse maps on compatible families, and
their inverse laws follow at every level. The `@[simp]` laws
`restrictScalarsEquiv_eval` and `restrictScalarsEquiv_symm_eval` give both
evaluation formulas; `restrictScalarsEquiv_of` and
`restrictScalarsEquiv_symm_of` transport the two native `AdicCompletion.of`
maps.

Level zero works without a special assumption: `I ^ 0 = ⊤`, so its quotient
is trivial. The same equivalence covers the identity algebra and both `⊥`
and `⊤` ideals: for `⊥` positive-degree filtration terms vanish, and for
`⊤` all quotients and completions are trivial, even if `M` is not. For a
nonidentity algebra, import `Mathlib.RingTheory.Polynomial.Basic` and use:

```lean
example (I : Ideal ℤ) :
    AdicCompletion (I.map (algebraMap ℤ (Polynomial ℤ))) (Polynomial ℤ) ≃ₗ[ℤ]
      AdicCompletion I (Polynomial ℤ) :=
  AdicCompletion.restrictScalarsEquiv I (Polynomial ℤ)
```

The [ordinary-import client](../AdicModulesTest/AdicCompletion/RestrictScalars.lean)
exercises these directions and boundary cases. The 103-display-site native
`docs/API.md` snapshot predates this module and remains historical; this guide
and the Lean source describe the current scalar-restriction API.

## Integer singleton spans in unital rings

Import [`AdicModules.Algebra.Module.Int`](../AdicModules/Algebra/Module/Int.lean)
alone or the `AdicModules` public root. For `R : Type u` with `NonAssocRing R`,
the integer action is the canonical `AddCommGroup.toIntModule` action induced
by the additive group. No separately chosen `Module ℤ R` structure is needed.
The span `Submodule.span ℤ ({x} : Set R)` consists of the integer multiples
of `x`; it is not a span for a separately chosen self-scalar action of `R`.

`IsAddCyclic.intCast_surjective` says that the integer cast `ℤ → R` is
surjective when the additive group of `R` is cyclic.
`Submodule.intCast_surjective_of_span_singleton_eq_top` gives the same
conclusion if one element has top integer span. Its contrapositive,
`Submodule.int_span_singleton_ne_top_of_not_surjective_intCast`, makes
**every** singleton integer span proper when integer casts are not surjective.
Multiplication need not be associative or commutative. No `CharZero`,
`Nontrivial`, topology or special-generator hypothesis is added.

The proof uses mathlib's `AddMonoidHom.map_addCyclic`: every additive endomorphism
of a cyclic additive group is an integer scalar map. Apply this to the existing
right-multiplication homomorphism `AddMonoidHom.mulRight a`, and evaluate at
`1`. The identities `1 * a = a` and `m • 1 = (m : R)` put each `a` in the
integer-cast image. This uses no reassociation of ring multiplication or self
`Module R R` structure. Mathlib's `Submodule.span_singleton_eq_top_iff`
provides the cyclic additive-group witness from the top-span premise.

The [ordinary-import clients](../AdicModulesTest/Algebra/Module/Int.lean) show
that `1` generates `ℤ` and every `ZMod n` as an integer module. This includes
`ZMod 0` and the zero ring `ZMod 1`. In a subsingleton ring, every singleton
span is both top and bottom and integer casts are onto. Nonsurjectivity is not
necessary for one particular span to be proper: `ℤ` has surjective casts, yet
its integer span of `2` does not contain `1`.

For `Matrix (Fin 2) (Fin 2) ℤ`, every integer cast is a scalar diagonal matrix.
The matrix unit `E₀₁ = Matrix.single 0 1 1` is not a cast, because its `(0,1)`
entry is `1` rather than `0`. Hence every singleton integer span in this ring
is proper. The span of `E₀₁` contains `E₀₁` itself but not the identity matrix.
The identities `E₀₁ * E₁₀ = E₀₀` and `E₁₀ * E₀₁ = E₁₁` exhibit genuine
noncommutativity, so a commutative-ring restriction would omit this client.

## Submodule closure from a neighborhood basis

Import [`AdicModules.Topology.Algebra.Submodule`](../AdicModules/Topology/Algebra/Submodule.lean)
or the public root. `Submodule.topologicalClosure_eq_iInf_sup` identifies

```text
N.topologicalClosure = ⨅ i, ⨅ (_ : p i), N ⊔ U i
```

when the active submodules `U i` form a basis of neighborhoods of zero. The
scalar ring is only a semiring; the module is an additive commutative group
with an `R`-module structure, a **given compatible topological additive-group
structure**, and continuous multiplication by each fixed scalar. Scalar,
module and `Sort`-valued index universes are independent. There is no scalar
topology, joint scalar continuity, Hausdorffness, countability or closedness
premise. This theorem does not construct a topology from arbitrary semiring
submodule filtrations.

The proof packages Mathlib's set-level neighborhood-basis closure formula
through canonical submodule carriers; it does not replace that closure
construction. The [examples](../AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean)
compute discrete and indiscrete closures and specialize to canonical `(2)`-adic
powers on the integers, including proposition indices and an active `Bool`
predicate. The [p-adic application](#p-adic-neighborhood-bases-and-integer-spans)
uses the same formula with ideals restricted to integer scalars.

## Closure of spans over a dense subsemiring

Import [`AdicModules.Topology.Algebra.Module.Span`](../AdicModules/Topology/Algebra/Module/Span.lean)
or the public root for `Submodule.closure_span_eq_of_dense_subsemiring`.
The theorem has the following hypotheses and conclusion, with independent
universe parameters `u` and `v`. The original span and closure calculations in
its five model sources are independent of this theorem; `Real` also includes an
additional private rational-axis application.

```lean
{R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]
[TopologicalSpace R] [TopologicalSpace M] [SeparatelyContinuousAdd M]
(A : Subsemiring R) (hA : Dense (A : Set R)) (E : Set M)
(hE : ∀ m ∈ E, Continuous (fun r : R => r • m)) :
closure (Submodule.span A E : Set M) = closure (Submodule.span R E : Set M)
```

Both spans live in the same module `M`; Mathlib's `Subsemiring.module` and
`Subsemiring.smul_def` restrict the given action to `A`. These are **set-level
closures**, not an equality of bundled submodules with different scalar types.
The scalar topology is independent of the module topology. Separate continuity
of addition is weaker than joint continuity, and the coefficient map
`R → M`, `r ↦ r • m`, is required to be continuous only at each selected
generator `m ∈ E`. Continuity of `M → M`, `x ↦ r • x`, for fixed `r` is a
different condition and is not a premise. Neither continuity at every `m` nor
`ContinuousSMul R M` is assumed. The statement needs no ring, commutativity,
additive inverses, separation, finiteness, countability, nonzero-generator or
nonempty-generator hypothesis.

If `E = ∅` or `E = {0}`, both spans have carrier `{0}` and their closures equal
`closure {0}`. Without `T1`, that closure need not be `{0}`: in a nontrivial
indiscrete module it is the whole module. A subsingleton module is a degenerate
boundary, not evidence of a nontrivial span comparison.

For the closed `A`-span, the proof uses only its additive-submonoid structure:

1. Let `S` be `(Submodule.span A E).toAddSubmonoid.topologicalClosure`.
   Mathlib's `AddSubmonoid.coe_topologicalClosure` and
   `Submodule.coe_toAddSubmonoid` identify its carrier with
   `closure (Submodule.span A E : Set M)`. Separate continuity of addition
   supplies its zero and addition closure; no `R`-submodule structure on `S`
   is assumed.
2. For each `m ∈ E`, apply
   `Continuous.range_subset_closure_image_dense` to `r ↦ r • m` and the
   density of `A`. Every `A`-multiple of `m` belongs to the `A`-span, so
   every `R`-multiple of `m` belongs to `S`.
3. Apply `Submodule.span_induction` with the strengthened assertion
   `∀ r : R, r • x ∈ S`. Zero and addition use `smul_zero`, `smul_add`
   and the additive closure of `S`. The scalar step uses
   `r • (a • x) = (r * a) • x`, with no commutation of scalars.
   Taking `r = 1` puts the entire `R`-span in `S`; closedness then puts
   its set closure in `S` as well.
4. For the other inclusion, `Submodule.span_subset_span A R E` embeds the
   `A`-span into the `R`-span, and closure is monotone.

The strengthened induction assertion avoids any need for coefficient continuity
at elements outside `E` or fixed-scalar continuity on the closure.

### Real and discrete-module calculations

The two model sources provide four original calculations independent of the
comparison theorem. The real source also imports the comparison and includes an
additional private application of
`Submodule.closure_span_eq_of_dense_subsemiring` to the rational axis, identifying
its proper closure and excluding the second coordinate unit. All their model
constructions and controls, including this application, are private.

| Model | Scalars, module and generators | Closure calculation and separating controls |
| --- | --- | --- |
| Rational first axis | Usual `ℝ`, `A = (Rat.castHom ℝ).rangeS`, `M = Fin 2 → ℝ`, `E = {Pi.single 0 1}` | Dense proper `A`; both closures are `{x \| x 1 = 0}`, excluding the second coordinate unit. `√2` times the first unit is in the closure but not the rational span. Addition and the selected coefficient map are continuous. |
| Integer real line | Usual `R = M = ℝ`, `A = (Int.castRingHom ℝ).rangeS`, `E = {1}` | The integer span is closed and proper, whereas the real span and its closure are the whole line. `1 / 2` separates the closures. The coefficient map is continuous, but `A` is not dense. |
| Discrete real module | Usual scalar `ℝ`, dense proper rational `A`, canonical `D = Fin 1 → ℝ` with local discrete topology, `E = {constantVector 1}` | Rational constant vectors form a closed proper span; the real span is top. The constant `√2` vector separates the closures. Addition and each fixed-scalar map are continuous, but the coefficient map is not: the preimage of the open zero singleton is the nonopen singleton `{0}` in usual `ℝ`. |
| Mixed real module | Usual scalar `ℝ`, the same rational `A`, canonical `M = ℝ × D`, `E = {(1, 0)}` | Both closures are `{x \| x.2 = 0}`, excluding `(0, constantVector 1)`. `(√2, 0)` enlarges the rational span after closure. The selected coefficient map is continuous, but the coefficient map at the second unit is not; global coefficient continuity and `ContinuousSMul` both fail. |

The discrete topology is installed **only on `D`**, not on the scalar real
field. Its three local topology/addition instances leave the canonical Pi
module action unchanged. The mixed model uses Mathlib's canonical product
module and product topology. These ring-specific examples do not narrow the
generic semiring statement.

### Full model-source map

All five model files below retain original span and closure calculations and
controls independent of the comparison theorem. The real file also contains the
additional private rational-axis application; its original calculations do not
invoke the comparison.

| Source under `AdicModulesTest.Topology.Algebra.Module.Span` | Mathematical role |
| --- | --- |
| [Real](../AdicModulesTest/Topology/Algebra/Module/Span/Real.lean) | Rational first-axis comparison and integer-line missing-density boundary, with `√2` and `1 / 2` separating controls. |
| [Discrete](../AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean) | Discrete missing-coefficient-continuity boundary and mixed first-axis comparison without global coefficient continuity; only the independent module factor is discrete. |
| [PadicInt](../AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean) | Canonical `ℤ_[p]` with `Fact p.Prime`, its norm topology and self-action. Direct stock continuous-image closure calculations compare integer, integer-range-subsemiring and self-scalar singleton spans for arbitrary `x`. Units and `1` give whole closures; the nonzero nonunit `p` gives the closed proper ideal `p ℤ_[p] = {z \| ‖z‖ ≤ p⁻¹}`, excluding `1`, with a `p = 2` control; `0` gives `{0}`. Existing ideal-power neighborhoods include degree zero and zero membership; shifted norm balls test neighborhoods away from zero. No rational action is used. |
| [Boundary](../AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean) | Unnamed calculations for empty generators, the zero generator and arbitrary generating sets in a subsingleton module, over a semiring and additive commutative monoid with independent universes. A nontrivial canonical rational self-module with indiscrete topology has `closure {0} = univ`, a nonclosed zero singleton and no `T1Space`; nonzero `1` is outside the empty and zero spans but inside their closures. |
| [Indiscrete](../AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) | Indiscrete scalar `ℚ` and independent discrete `ULift.{v} ℚ`, using Mathlib's canonical module action. The integer-cast range subsemiring is dense and proper, addition is separately continuous and all fixed-scalar maps are continuous. The integer and restricted-subsemiring spans of transported `1` coincide, are closed and proper, and exclude transported `1 / 2`; the rational span and its closure are whole. The selected coefficient map is not continuous, so the span closures differ. |

For singleton spans, Mathlib already supplies `Submodule.span_singleton_eq_range`,
`closure_image_closure` and `DenseRange.closure_range`, together with
`Set.image_univ` and `Set.range_comp`. The existing model calculations use
`Submodule.mem_span_singleton` and
`Continuous.range_subset_closure_image_dense` directly. Integer coefficients
are related to ring coefficients by `Int.cast_smul_eq_zsmul` for the canonical
`AddCommGroup.toIntModule` action. The p-adic model applies those stock
continuous-image closure identities directly, retaining the canonical norm
topology and ideal carriers. The independent rational module uses the stock
`ULift.module'` action and transport described by `ULift.moduleEquiv`, not a
new action or a replacement of the scalar topology. These interfaces do not
require a new singleton closure construction or a duplicate of the library's
integer-span properness theorem. A singleton comparison only uses continuity
of its one coefficient map, not the separate-addition premise of the
arbitrary-set statement.

## P-adic neighborhood bases and integer spans

Import [`AdicModules.Topology.Algebra.PadicInt`](../AdicModules/Topology/Algebra/PadicInt.lean)
or the public root. For a prime `p`, the existing norm topology on `ℤ_[p]`
has the zero-neighborhood basis

```lean
(𝓝 (0 : ℤ_[p])).HasBasis (fun _n : ℕ ↦ True)
  (fun n ↦ ((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) : Set ℤ_[p]))
```

`PadicInt.hasBasis_nhds_zero_span_pow` obtains this basis from geometric closed
balls with radii `((p : ℝ)⁻¹) ^ n`. Mathlib's
`PadicInt.norm_le_pow_iff_mem_span_pow` identifies the ideal carrier with the
norm bound `‖x‖ ≤ (p : ℝ) ^ (-n : ℤ)`, including `x = 0`. For nonzero `x`,
Mathlib also gives the equivalent valuation bound `n ≤ x.valuation`; at zero
one must retain a zero disjunct because `PadicInt.valuation_zero = 0`.
At `n = 0` the ideal is top. At positive degrees the positive-radius closed
balls are also open by the ultrametric topology.

`PadicInt.hasBasis_nhds_zero_int_submodule_pow` restricts each whole ideal to
integer scalars:

```lean
((Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]).restrictScalars ℤ : Set ℤ_[p])
```

Restriction preserves the carrier and **all p-adic multiples**, not only
integer multiples of `p ^ n`. `PadicInt.isLinearTopology_self` and
`PadicInt.isLinearTopology_int` characterize the existing topology as linear
for the two scalar actions. They are ordinary theorems rather than global
instances; a user can install the desired result locally.

The [Submodule module](../AdicModules/Topology/Algebra/Submodule.lean) also gives
`Submodule.dense_int_span_of_isUnit_of_denseRange_intCast`. Its hypotheses are
`[Ring R]`, `[TopologicalSpace R]`, `[ContinuousConstSMul R R]`, dense range
of `Int.cast : ℤ → R`, and `IsUnit x`. Then `Submodule.span ℤ {x}` is dense.
The ring need not be commutative: multiplication by the unit is a homeomorphism,
and central integer casts identify its transported range with the integer
span. No topology on `ℤ`, characteristic-zero hypothesis, joint multiplication
continuity or separation hypothesis is added.

`PadicInt.dense_int_span_of_isUnit` uses Mathlib's density of integer casts;
`PadicInt.dense_int_span_intCast` specializes to an integer `a` with
`¬ (p : ℤ) ∣ a`. Independently, `PadicInt.int_span_intCast_ne_top` says that
every integer generator has a proper integer span, even `0`, `1` and `-1`.
`PadicInt.inv_succ_notMem_int_span_intCast` supplies the uniform witness
`PadicInt.inv ((p + 1 : ℕ) : ℤ_[p])`, which cannot lie in any such span:
membership would force an integer multiple of `p + 1` to equal one.

In particular, `PadicInt.int_span_three_two_proper_dense` gives a proper dense
integer submodule `Submodule.span ℤ {(3 : ℤ_[2])}`, and
`PadicInt.one_notMem_int_span_three_two` excludes `1`. The self-scalar ideal
generated by the p-adic unit `3` would instead be top.
`PadicInt.int_span_three_two_proper_sup_pow` retains properness and gives

```lean
∀ n : ℕ, Submodule.span ℤ {(3 : ℤ_[2])} ⊔
  (Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]).restrictScalars ℤ = ⊤
```

This consumes `Submodule.topologicalClosure_eq_iInf_sup` with the restricted
ideal-power basis. Density gives top closure, `iInf_const` removes the inner
infimum over `True`, and `iInf_le` shows that every individual supremum is top.
It does not reprove the closure formula or replace the ideal carrier by an
integer span. Together, the generic density result and the eleven p-adic
results form this twelve-result API.

The [ordinary-import clients](../AdicModulesTest/Topology/Algebra/PadicInt.lean)
show that closure adds `1`, exercise the uniform witness and small integer
generators, check degree zero and the zero-element valuation boundary, and
refine zero-neighborhoods to submodule neighborhoods for each scalar action.
The positive-degree supremum client adds `1` with the degree-one restricted
ideal and `PadicInt.inv (3 : ℤ_[2])` with the degree-two restricted ideal;
both elements remain excluded from the original integer span of `3`.

## Comaximal powers of left ideals

Import [`AdicModules.RingTheory.Ideal.Operations`](../AdicModules/RingTheory/Ideal/Operations.lean)
or the public root. The public theorem has the universe-polymorphic signature

```lean
Ideal.sup_pow_eq_top_of_sup_eq_top
  {R : Type u} [Semiring R] {J I : Ideal R} {n : ℕ}
  (h : J ⊔ I = ⊤) : J ⊔ I ^ n = ⊤
```

For a comaximality hypothesis `h`, use
`Ideal.sup_pow_eq_top_of_sup_eq_top (J := J) (I := I) (n := n) h`.
Here `J` is the unpowered ideal and `I` the powered ideal. Both are arbitrary
left ideals of the original semiring. There is no commutativity, additive-inverse,
domain, cancellation, nontriviality or two-sidedness hypothesis. Every natural
exponent is covered: at `n = 0`, `I ^ 0 = ⊤`, so the conclusion is automatic.
All coefficients and powers are those of the original semiring; `I ^ n` is
not replaced by a span of powers of generators or by a restricted-scalar power.
No topology is involved.

The written proof is a subtraction-free geometric-sum recurrence. Decompose
`1 = j + i` with `j ∈ J` and `i ∈ I`. Starting from `x = 0` at degree zero,
maintain `x ∈ J` and `x + i ^ n = 1`. The successor certificate is
`x + i ^ n * j ∈ J`, using only closure under **left** multiplication, and

```text
(x + i ^ n * j) + i ^ (n + 1) = x + i ^ n * (j + i) = 1.
```

Membership `i ^ n ∈ I ^ n` then puts `1` in `J ⊔ I ^ n`. The module credits
Mathlib's ideal operations and Neil Strickland's geometric-sum formalization
for the underlying APIs and proof idea; the recurrence requires neither
subtraction nor a commutation premise.

The companion theorem `Ideal.pairwise_sup_eq_top_pow` has signature

```lean
{R : Type u} {ι : Type v} [Semiring R]
(I : ι → Ideal R) (hI : Pairwise (fun i j => I i ⊔ I j = ⊤)) (n : ι → ℕ) :
Pairwise (fun i j => I i ^ n i ⊔ I j ^ n j = ⊤)
```

It applies the preceding theorem twice, interchanging the ideals, so each
coordinate may have its own exponent, including zero. The index type is
arbitrary and independent of the ring universe: no finiteness or two-sidedness
is needed. This is a pairwise comaximality statement about ideal powers, not a
finite CRT for arbitrary left ideals; see the
[finite-quotient boundary](FiniteQuotient.md#arbitrary-left-ideal-boundary).

Mathlib's `Ideal.sup_pow_eq_top` and `Ideal.sup_pow_eq_top'` give the same
conclusion with the unpowered or powered ideal, respectively, two-sided.
Two private recovery lemmas apply the public theorem under those respective
hypotheses. They are implementation details, not additional public entry points;
use `Ideal.sup_pow_eq_top_of_sup_eq_top` directly. The independent semiring
matrix calculations below show why two-sidedness and stronger semiring
hypotheses would exclude useful examples. The density criterion uses this
algebraic implication together with direct additive-group neighborhood
arguments, as described next.

## Left-ideal density and integer powers topologies

Import [`AdicModules.Topology.Algebra.Ideal`](../AdicModules/Topology/Algebra/Ideal.lean)
or the public root. `Ideal.dense_iff_sup_eq_top_of_hasBasis` has the signature

```lean
{R : Type u} [Ring R] [TopologicalSpace R] [IsTopologicalAddGroup R]
{I J : Ideal R}
(hI : (𝓝 (0 : R)).HasBasis (fun _n : ℕ ↦ True)
  (fun n ↦ ((I ^ n : Ideal R) : Set R))) :
Dense (J : Set R) ↔ J ⊔ I = ⊤
```

The ideals are left ideals in a possibly noncommutative ring. The topology is
supplied, not constructed from an arbitrary filtration. No two-sidedness,
separation, closedness, joint multiplication continuity or continuous ring
scalar action is added. The powers and sums are formed as ideals over the
original ring, with their whole coefficients and carriers.

The written proof works directly in the given additive-group topology; it
needs neither restriction to integer scalars nor the submodule closure formula.
Mathlib's `Filter.HasBasis.nhds_of_zero` translates the basis to each `r : R`,
with neighborhoods `{x | x - r ∈ I ^ n}`.
`mem_closure_iff_nhds_basis` characterizes membership in the closure of `J`
by whether each such neighborhood meets `J`.

For the forward implication, density at `1` and degree one provide `j ∈ J`
with `j - 1 ∈ I`. Then `j - (j - 1) = 1` belongs to `J ⊔ I`, so this
supremum is top. Conversely, the
[comaximal-powers theorem](#comaximal-powers-of-left-ideals) puts every
`r : R` in `J ⊔ I ^ n`. Decompose `r = j + i` with `j ∈ J`, `i ∈ I ^ n`;
then `j - r = -i ∈ I ^ n`, so each translated neighborhood meets `J`.
The column models below compute particular cases independently of this
criterion. No continuous ring scalar action or continuity of ring
multiplication is used in the direct additive proof.

The [integer model](../AdicModulesTest/Topology/Algebra/Ideal/Int.lean) contains
four private proofs independent of the general density criterion. They use the
whole ideal `Ideal.span {(3 : ℤ)}`, not the numeral `(3 : Ideal ℤ)`. Membership
of `3` and nonmembership of `1` witness nonzero properness. Mathlib's
comaximal-power result gives `J ⊔ I ^ n = ⊤` for every natural `n` with
`I = Ideal.span {(2 : ℤ)}`; decomposing each integer in this supremum gives a
member of `J` in each residue modulo `2 ^ n`. The final proof explicitly
installs `I.adicTopology` and its additive-group structure on the original
integers, uses `I.hasBasis_nhds_zero_adic`, and computes top closure via
`Submodule.topologicalClosure_eq_iInf_sup` after scalar restriction. It does
not use the default discrete topology on `ℤ`, a completion, or density as a
hypothesis. These four private proofs compute the integer example directly,
without applying the general density criterion. The same file additionally
contains a private application of `Ideal.dense_iff_sup_eq_top_of_hasBasis` to
`(3)` with the supplied `(2)`-adic powers basis; that application does not
replace any of the four direct proofs.

## Matrix left-ideal models

The [integer-matrix model](../AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean)
uses the canonical ring `M₂(ℤ)` and its whole-ring scalar action. Write
`I = Ideal.span {E00}` and `J = Ideal.span {E11}` with zero-based matrix
indices. Its membership contracts identify `I` with matrices whose second
column vanishes and `J` with matrices whose first column vanishes. Both ideals
are nonzero, proper and not two-sided. The file calculates `I * I = I` and
`I ^ (n + 1) = I`; splitting the columns gives `J ⊔ I = ⊤`. Together these
give `J ⊔ I ^ n = ⊤` for every natural `n`, including degree zero.

Let `π : M₂(ℤ) →+ ℤ²` take the second column. The topology is exactly
`TopologicalSpace.induced π ⊥`, with the discrete topology on `ℤ²`; four
local canonical instances supply these topologies, discreteness and the
compatible topological additive-group structure. The zero-neighborhood filter
is principal on the whole carrier of `I`, and all its ideal powers, including
degree zero, form a basis. Every second-column fiber meets `J`, so its density
is computed independently of the general density criterion. In this **same induced
topology**, `J` is not closed and the space is not Hausdorff. Right
multiplication by the column-swap matrix is discontinuous, so the topology is
not a topological-ring structure. The model neither assumes continuity of
multiplication nor replaces whole-matrix coefficients by integer multiples.

The [natural-matrix model](../AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean)
uses the canonical semiring `M₂(ℕ)`. Its auxiliary membership and idempotency
contracts work over any coefficient semiring and any finite square-matrix
index type with decidable equality. For `M₂(ℕ)`, the two column ideals again
have both membership iff contracts, are nonzero and proper, are not two-sided,
are comaximal, and are idempotent. Each positive power is the original ideal;
each zeroth power is top. The file computes both `J ⊔ I ^ n = ⊤` and
`I ⊔ J ^ n = ⊤` for every natural `n`. It also contrasts the automatic
zeroth-power supremum with the failure at degree one for a proper column
ideal summed with powers of bottom.

Here an elementary **matrix unit** `Eij` is not an invertible element.
The file proves `E01 * E10 = E00` and `E10 * E01 = E11`, with unequal
products; none of the four elementary matrices is invertible. These are
noncommutativity witnesses, not substitute examples involving invertible
units. The nonzero diagonal matrix units have zero products, yielding explicit
failures of left and right multiplication cancellation at nonzero factors.
There is no additive inverse of `E00` for the canonical addition, hence no
negation making that addition into a ring addition. This says nothing about
unrelated operations transported onto the underlying type.

The same semiring file includes the generator-power warning. Although
`E01 ^ 2 = 0`, left multiplication by `E10` puts `E11` in
`K = Ideal.span {E01}`. Thus `E11 ∈ K ^ 2`, so `K ^ 2 ≠ ⊥` and
`K ^ 2 ≠ Ideal.span {E01 ^ 2}`; `K` is also not two-sided. Powers must be
formed as ideals in the original semiring, not by powering a chosen generator
or changing the coefficient action. These calculations require no commutative,
domain, ring or multiplication-cancellation structure. The two matrix files
retain independent algebraic and topological calculations without invoking the
general density criterion. The natural-matrix file also contains an additional
private application of `Ideal.sup_pow_eq_top_of_sup_eq_top` to its comaximal
column ideals; it does not replace the original all-power calculations.

## Ideal-power boundary models

The [boundary file](../AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean)
contains the following seven groups of calculations, independent of the
general density criterion. Here `(m)` denotes `Ideal.span {(m : ℤ)}`,
not the numeral `(m : Ideal ℤ)`.

| Boundary | Mathematical scope |
| --- | --- |
| Zeroth and first powers | Over any semiring, `J ⊔ I ^ 0 = ⊤` automatically, while `J ⊔ I ^ 1 = ⊤ ↔ J ⊔ I = ⊤`. For `(2)` in `ℤ`, its sum with its zeroth power is top but its sum with its first power is not. |
| Discrete integers | `(3)` is proper and not dense despite `(3) ⊔ (2) = ⊤`; powers of `(2)` are not a zero-neighborhood basis for the discrete topology. |
| Actual `(2)`-adic integers | On the original `ℤ` with `I.adicTopology` for `I = Ideal.span {(2 : ℤ)}`, `I` has its powers basis, is closed and proper, is not dense and is not comaximal with itself. This is not a completion. |
| Top and indiscrete bases | A top-ideal powers basis forces the given compatible additive-group topology to be indiscrete. Every ideal is dense because it contains zero; the empty set is not dense in the indiscrete integers, and that space is not T1. |
| Bottom and discrete bases | A bottom-ideal powers basis forces the given compatible additive-group topology to be discrete. An ideal is then dense iff it is top. The canonical top- and bottom-adic topology equalities are also calculated over commutative rings. |
| Extreme target ideals | The top ideal is dense over any semiring with any topology, and its supremum with every ideal power is top. Under the stated powers-basis hypothesis `hI`, in a ring with a compatible additive-group topology, the bottom ideal is dense iff `I = ⊤`. |
| Subsingleton models | Over a subsingleton semiring every ideal and every natural power is both bottom and top. The one-element ring `PUnit` additionally realizes every ideal-power basis and density assertion, including all-power suprema. |

The general basis computations use `[Ring R]`, `[TopologicalSpace R]` and
`[IsTopologicalAddGroup R]`, with the displayed `hI` when a powers basis is
needed; they add no T1 or Hausdorff assumption. The purely algebraic boundaries
use only a semiring, and density of the top ideal uses only a semiring and a
topology. Canonical integer scalar continuity in the bottom-density proof
comes from the topological additive group, not from an assumed continuous
`R`-action. These boundary calculations are independent of the general
density criterion.

## Finite Chinese remainders

Import [`AdicModules.RingTheory.Ideal.Quotient.Finite`](../AdicModules/RingTheory/Ideal/Quotient/Finite.lean)
or the public root. For a possibly noncommutative ring `R`, a finite index type
`ι` in an independent universe, full `[∀ i, (I i).IsTwoSided]` and
`Pairwise (fun i j => I i ⊔ I j = ⊤)`, the canonical ring map gives

```lean
Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI :
  (R ⧸ ⨅ i, I i) ≃+* ((i : ι) → R ⧸ I i)
```

The [finite-quotient guide](FiniteQuotient.md) develops its canonical forward
formulas, inverse class and complete representative coset, equality with
Mathlib's commutative equivalence and inverse, independent powers including
zero, common-ring scalar action, the linear equivalence and its characteristic
API, and forward/inverse precision-reduction squares. It also gives the integer
examples and the boundary separating two-sided ring CRT from arbitrary-left-ideal
module diagonals. Finiteness is of the index type, not of `R`; no topology,
completion or general module CRT is asserted.

## Finite sets of adic generators

The [completeness API](../AdicModules/AdicCompletion/Completeness.lean) lets one
work with a chosen `s : Finset R` over any commutative ring and any `R`-module
with an additive commutative group structure. Use `IsPrecomplete.span_finset`
to pass from precompleteness for each `Ideal.span {a}`, `a ∈ s`, to
precompleteness for `Ideal.span (s : Set R)`. With Hausdorffness for this whole
generated ideal, `isAdicComplete_span_finset_iff` gives the corresponding
completeness equivalence. Hausdorffness for the principal ideals alone is not
the premise of the reverse implication.

For a finite subset `t : Set R`, use `ht.toFinset` and the stock membership and
coercion equalities to apply the finite-generator result. Principal completeness
then yields precompleteness for `Ideal.span t`; the existing Hausdorffification
instance gives completeness of `Hausdorffification (Ideal.span t) M` without
Hausdorffness of `M`. The
[examples](../AdicModulesTest/AdicCompletion/CompletenessTheorems.lean) include
this general finite-subset use, the generators `{2, 4}` on the completion of
`ℤ` at `(2)`, and the empty finite set. No Noetherianity or finite generation
of the module is required by the two finite-generator theorems.

## Completion and valuation hypotheses

[`AdicCompletion.abstractCompletion`](../AdicModules/AdicCompletion.lean)
packages the adic inverse limit as a uniform-space completion. It requires a
commutative ring with compatible uniform additive-group structure, `IsAdic I`
for that structure, and a finitely generated ideal `I`. It does not require a
valuation ring. Its canonical map is definitionally the algebra map, with the
public `abstractCompletion_coe` equation.

The [valuation-integers completeness equivalence](Results.md#principal-adic-completeness-and-the-valued-fraction-field)
identifies principal-adic completeness at a **nonzero separated generator**
with completeness for the **given field valuation uniformity**. Its integer-ring
identification supplies the domain, valuation-ring and fraction-field properties;
no topology on the integer ring is assumed. The linked reference gives the
natural signature, zero-generator limitation and 3-adic and series models.

For valuation-ring results, keep the ring `V` and fraction field `K` explicit.
Their universes are independent. `ValuationRing.CompletionIntegers V K` is the
valuation-integer subring in the uniform completion of `K`, with the canonical
valuation induced by `V`.

`principalAdicCompletionEquiv` compares `AdicCompletion (Ideal.span {a}) V`
with those integers as `V`-algebras. It assumes `a ≠ 0` and
`IsHausdorff (Ideal.span {a}) V`. It does not assume discreteness, rank one,
finite height or Noetherianity. Statements about a non-field local completion,
faithful flatness and the prime-spectrum order isomorphism additionally retain
the hypothesis that `a` belongs to the maximal ideal where stated. The ordinary
[completed-integer](../AdicModulesTest/CompletedIntegers.lean),
[local-structure](../AdicModulesTest/CompletedLocalStructure.lean) and
[spectrum](../AdicModulesTest/PrincipalAdicSpectrum.lean) clients show the needed
local typeclass installations rather than silently adding global instances.

## Localization and literal composites

Keep the valuation domain `V`, fraction field `K` and element `a : V` above.
For denominators disjoint from the radical of `(a)`,
[`localizedPowerImage`](../AdicModules/LocalizedFiltration.lean) consists of the
literal images of the base-ring powers as `V`-submodules of the localization.
The comparison sandwiches these submodules between successive powers of the
extended principal ideal; it is **not** an unconditional equality with those
powers. The filtration defines the localized topology, and principal-adic
separatedness supplies its separation.

For a nonzero generator, radical-disjoint denominators and separatedness, the
[localized-completion map](../AdicModules/LocalizedCompletion.lean) embeds into
the same completed fraction field used for the base ring. The
[valuation-subring equivalence](../AdicModules/LocalizedValuationSubring.lean)
and [residue-field comparison](../AdicModules/LocalizedResidueField.lean)
describe that completion and its residue field. At a nonzero prime,
separatedness supplies radical-disjointness. The
[quotient valuation subring](../AdicModules/LocalizedQuotientValuationSubring.lean)
retains those prime-specific hypotheses; this is not arbitrary-denominator
localization without assumptions.

[`ValuationSubring.composite`](../AdicModules/CompositeValuationSubring.lean)
is the literal residue preimage of a valuation subring of the residue field.
Localization at its distinguished prime recovers the first factor, and
quotient by that prime recovers the second. The
[completed-composite equality](../AdicModules/CompletedValuationComposite.lean)
identifies the completed valuation integers literally with the composite of
the completed localization and its transported residue factor. It uses the
completion and residue maps above, not a new kind of completion.

### Separately importable concrete results

The completion and valuation leaves expose characteristic criteria for inverse
comparisons, residue congruence and equality in completed-field realizations.
Their canonical maps are available from `AdicModules` or the narrower library
leaf. Some related example modules also expose named concrete results: the
ideal generated by `2` remains proper in its integer adic completion; the
bottom-adic polynomial comparison distinguishes `X` from `1`; and a composite
with the whole field as first factor localizes back to that field. Import the
corresponding model module to use those results.
These examples are not re-exported by `AdicModules`.

## Module map

The library module names in the first table have prefix `AdicModules.`.
The first table lists all 49 production source leaves re-exported by the public
root, including the completion-exactness and finite-presentation comparisons,
Frobenius/Teichmüller interfaces, comaximal-powers theorems, finite Chinese
remainder equivalence, left-ideal density criterion and dense-subsemiring span
comparison. There are **50 production sources including the root and 64
test/model/audit sources, hence 114 Lean source modules**. These are source-file
counts, not
counts of mathematical models, compiled modules, kernel declarations or audited
axioms. All four left-ideal
and all five span-model files retain independent original calculations; `Int`,
`MatrixNat` and `Real` additionally contain private applications of their
respective library theorems. The tables describe all current library leaves and
test/model/audit sources; [`AdicModules`](../AdicModules.lean) is the additional
public root. Neither these counts nor mathematical proof descriptions certify
complete transitive standard-axiom assurance for private, generated, model or
imported declarations.

See the [public root](../AdicModules.lean) for its direct public imports. Among the
listed leaves, `AdicCompletion.Topology` and `Topology.Algebra.AdicTopology` are
re-exported through `AdicCompletion.PadicIntTopology`.

| Module | Main role |
| --- | --- |
| [BoundedIdealPowerTorsion](../AdicModules/BoundedIdealPowerTorsion.lean) | Uniform torsion and finite-module bridge |
| [Polynomial.Hensel](../AdicModules/Polynomial/Hensel.lean) | Coprime monic factor lifting and irreducible reduction from a global monic factor-lifting property |
| [Polynomial.Evaluation](../AdicModules/Polynomial/Evaluation.lean) | Association of nearby polynomial values for a Jacobson-contained ideal, including nonunit derivatives |
| [PrimaryComponent](../AdicModules/PrimaryComponent.lean) | Height-one primary exactness and integer-subgroup restricted maps |
| [AdicCompletion](../AdicModules/AdicCompletion.lean) | Finitely generated adic inverse limit as an abstract completion |
| [AdicCompletion.Completeness](../AdicModules/AdicCompletion/Completeness.lean) | Finite ideal sums and spans, surjective images of precomplete modules, complete Hausdorffification and principal-ideal completeness |
| [AdicCompletion.Exactness](../AdicModules/AdicCompletion/Exactness.lean) | Middle exactness under induced/intrinsic range cofinality; no injectivity assumption |
| [AdicCompletion.FinitePresentation](../AdicModules/AdicCompletion/FinitePresentation.lean) | Canonical completion–tensor equivalence for finitely presented modules under finite-free cofinality |
| [AdicCompletion.Kernel](../AdicModules/AdicCompletion/Kernel.lean) | Evaluation kernel at any degree whose ideal power is finitely generated, with independent ring/module universes |
| [AdicCompletion.LocalRing](../AdicModules/AdicCompletion/LocalRing.lean) | Unit detection, Jacobson kernel and locality from the residue quotient |
| [AdicCompletion.PadicInt](../AdicModules/AdicCompletion/PadicInt.lean) | Integer prime-adic completion and p-adic integers with residue normalization |
| [AdicCompletion.PadicIntTopology](../AdicModules/AdicCompletion/PadicIntTopology.lean) | Topology of the integer completion comparison |
| [AdicCompletion.QuotientTorsion](../AdicModules/AdicCompletion/QuotientTorsion.lean) | Scalar-power torsion sections and subgroup adic completion with signed coordinates |
| [AdicCompletion.RestrictScalars](../AdicModules/AdicCompletion/RestrictScalars.lean) | Native adic completion and quotient comparison under scalar restriction |
| [AdicCompletion.TensorProduct](../AdicModules/AdicCompletion/TensorProduct.lean) | Completion-ring-linear tensor comparison for finite projective modules |
| [AdicCompletion.Topology](../AdicModules/AdicCompletion/Topology.lean) | Evaluation neighborhoods in an adic completion |
| [Algebra.Module.Int](../AdicModules/Algebra/Module/Int.lean) | Cyclic additive rings, integer casts and singleton-span properness |
| [LinearAlgebra.Descent](../AdicModules/LinearAlgebra/Descent.lean) | Descent along surjective semilinear maps with additive-monoid targets |
| [LinearAlgebra.Span.Basic](../AdicModules/LinearAlgebra/Span/Basic.lean) | Kernel pullbacks of submodule images for semilinear maps with additive-monoid targets |
| [LinearAlgebra.SModEq.Pow](../AdicModules/LinearAlgebra/SModEq/Pow.lean) | Iterated ideal-power congruences from arbitrary positive starting depth |
| [LinearAlgebra.Correspondence](../AdicModules/LinearAlgebra/Correspondence.lean) | Kernel–range order correspondence for submodules under semilinear maps |
| [LinearAlgebra.TensorProduct.Quotient](../AdicModules/LinearAlgebra/TensorProduct/Quotient.lean) | Quotient–tensor naturality for ideal inclusions and module maps |
| [RingTheory.Teichmuller](../AdicModules/RingTheory/Teichmuller.lean) | Teichmüller sections of surjective residue maps and images of the perfection |
| [RingTheory.FrobeniusCore](../AdicModules/RingTheory/FrobeniusCore.lean) | Perfect intersections of iterated Frobenius ranges and their prime-characteristic universal property |
| [RingTheory.Perfection](../AdicModules/RingTheory/Perfection.lean) | Field structure on the inverse-Frobenius limit without perfectness of the original field |
| [RingTheory.WittVector](../AdicModules/RingTheory/WittVector.lean) | Characteristic zero over any commutative ring of prime characteristic; [nonzero-cast uses](../AdicModulesTest/RingTheory/WittVector.lean) |
| [RingTheory.TeichmullerFractionField](../AdicModules/RingTheory/TeichmullerFractionField.lean) | Teichmüller image in any fraction field of a complete valuation domain with maximal ideal and prime-characteristic residue |
| [RingTheory.Ideal.IsPrincipalPowQuotient](../AdicModules/RingTheory/Ideal/IsPrincipalPowQuotient.lean) | Representatives for quotients of powers of a principal ideal |
| [RingTheory.Ideal.Operations](../AdicModules/RingTheory/Ideal/Operations.lean) | All-exponent semiring left-ideal comaximal powers and independent pairwise power guards, with no two-sidedness requirement |
| [RingTheory.Ideal.Quotient.Finite](../AdicModules/RingTheory/Ideal/Quotient/Finite.lean) | Finite two-sided ring CRT, inverse representatives, independent powers, common-ring linear equivalence with characteristic API and precision-reduction squares |
| [Topology.Algebra.AdicTopology](../AdicModules/Topology/Algebra/AdicTopology.lean) | Adic module and algebra topologies |
| [Topology.Algebra.Submodule](../AdicModules/Topology/Algebra/Submodule.lean) | Bundled closure from a submodule zero-neighborhood basis and dense integer spans of units |
| [Topology.Algebra.Ideal](../AdicModules/Topology/Algebra/Ideal.lean) | Left-ideal density criterion for a supplied additive-group topology, with a written translated-neighborhood proof |
| [Topology.Algebra.Module.Span](../AdicModules/Topology/Algebra/Module/Span.lean) | Set-closure comparison for arbitrary generators over a dense subsemiring with generatorwise coefficient continuity |
| [Topology.Algebra.Module.AdicTopology](../AdicModules/Topology/Algebra/Module/AdicTopology.lean) | Functoriality of adic module topologies |
| [Topology.Algebra.PadicInt](../AdicModules/Topology/Algebra/PadicInt.lean) | P-adic ideal-power bases, linear topology, proper dense integer spans and top neighborhood suprema |
| [Topology.Algebra.PrincipalUnits](../AdicModules/Topology/Algebra/PrincipalUnits.lean) | Continuous p-adic powers of principal units |
| [Valuation.Completeness](../AdicModules/Valuation/Completeness.lean) | Valuation-integer principal-adic completeness; equivalence with valued-field completeness for a nonzero separated generator |
| [ValuationTopology](../AdicModules/ValuationTopology.lean) | Principal-adic versus valuation topology; radical containment |
| [CompletedIntegers](../AdicModules/CompletedIntegers.lean) | Comparison with completed valuation integers |
| [CompletedLocalStructure](../AdicModules/CompletedLocalStructure.lean) | Domain, valuation-ring, fraction-field, local and residue properties |
| [PrincipalAdicSpectrum](../AdicModules/PrincipalAdicSpectrum.lean) | Associated elements, ideal map/comap, faithful flatness, spectra and heights |
| [LocalizedFiltration](../AdicModules/LocalizedFiltration.lean) | Literal base-power images, topology and separatedness after localization |
| [LocalizedCompletion](../AdicModules/LocalizedCompletion.lean) | Embedding the localized completion into the common completed field |
| [LocalizedValuationSubring](../AdicModules/LocalizedValuationSubring.lean) | Realizing that completion as a valuation subring |
| [LocalizedResidueField](../AdicModules/LocalizedResidueField.lean) | Residue-field comparison with the original localization |
| [LocalizedQuotientValuationSubring](../AdicModules/LocalizedQuotientValuationSubring.lean) | Transport of the quotient factor at a nonzero prime |
| [CompositeValuationSubring](../AdicModules/CompositeValuationSubring.lean) | Residue-preimage composite, localization and quotient factors |
| [CompletedValuationComposite](../AdicModules/CompletedValuationComposite.lean) | Composite description of completed valuation integers |

### Test and audit source roster

All names in this table have prefix `AdicModulesTest.`. These are separate
files, not imports of an `AdicModulesTest.lean` aggregate root (which does not
exist). The four left-ideal and five `Span` model files retain original
calculations independent of the corresponding library proofs, with additional
private applications in `Int`, `MatrixNat` and `Real`. They are not re-exported
by the public root.

| Module | Main role |
| --- | --- |
| [BoundedIdealPowerTorsion](../AdicModulesTest/BoundedIdealPowerTorsion.lean) | Specified-exponent and existential uniform-torsion clients |
| [Polynomial.Hensel](../AdicModulesTest/Polynomial/Hensel.lean) | 5-adic factor lifting, independent `X² - 5` irreducibility and reduction, criterion applications and zero-ring boundary |
| [Polynomial.Evaluation](../AdicModulesTest/Polynomial/Evaluation.lean) | Independent 3-adic proximity and nonunit derivative inputs, association consumer and zero boundary |
| [PrimaryComponent](../AdicModulesTest/PrimaryComponent.lean) | Primary exactness and ordinary integer-prime subgroup clients |
| [AdicCompletion](../AdicModulesTest/AdicCompletion.lean) | Abstract-completion import client and concrete ideal boundary |
| [AdicCompletion.CompletenessTheorems](../AdicModulesTest/AdicCompletion/CompletenessTheorems.lean) | Suprema, finite spans, Hausdorffification and principal-ideal completeness examples |
| [AdicCompletionKernel](../AdicModulesTest/AdicCompletionKernel.lean) | Private integer `(2)` degree-one nonzero evaluation, independent kernel and degree-zero calibration, finite-generation recovery and separate fixed-power use |
| [AdicCompletion.FiniteNoetherian](../AdicModulesTest/AdicCompletion/FiniteNoetherian.lean) | Higher-universe `ULift (ZMod 2)` finite nonprojective tensor-comparison client |
| [AdicCompletion.FinitePresentation](../AdicModulesTest/AdicCompletion/FinitePresentation.lean) | Finitely presented nonprojective integer residue module, independent cofinality and completed-exactness inputs |
| [AdicCompletion.LocalRing](../AdicModulesTest/AdicCompletion/LocalRing.lean) | Unit detection and locality in the maximal-ideal completion of ℤ localized at `(2)` |
| [AdicCompletion.PadicInt](../AdicModulesTest/AdicCompletion/PadicInt.lean) | Nonzero integer-completion and p-adic inputs, comparison laws and trivial-residue boundaries |
| [AdicCompletion.RestrictScalars](../AdicModulesTest/AdicCompletion/RestrictScalars.lean) | Identity and polynomial algebras, both map directions, level zero and bottom/top ideals |
| [AdicCompletion.TensorProduct](../AdicModulesTest/AdicCompletion/TensorProduct.lean) | Integer rank-two tensor comparison, pure-tensor and inverse identities, and rank-zero boundary |
| [ScalarTorsionSections](../AdicModulesTest/ScalarTorsionSections.lean) | Nonzero rational `-2` torsion sections and independent finite-level sign calibration |
| [Algebra.Module.Int](../AdicModulesTest/Algebra/Module/Int.lean) | Integer, all `ZMod n`, subsingleton and noncommutative matrix singleton-span clients |
| [KernelPullback](../AdicModulesTest/KernelPullback.lean) | Kernel pullbacks of cones, monoid-target descent and source-inverse boundary |
| [Correspondence](../AdicModulesTest/Correspondence.lean) | Natural-number-linear half-plane and ray correspondence with proper range |
| [LinearAlgebra.SModEq.Pow](../AdicModulesTest/LinearAlgebra/SModEq/Pow.lean) | Independent exact-depth-two 3-adic inputs, positive-depth iteration and depth-one agreement |
| [ValuationPower](../AdicModulesTest/ValuationPower.lean) | Private finite power estimates for normalized additive valuations on canonical integer rings |
| [ValuationPowerModel](../AdicModulesTest/ValuationPowerModel.lean) | Independent 3-adic canonical-integer inputs and exact one-step and zero-depth bounds |
| [LinearAlgebra.TensorProduct.Quotient](../AdicModulesTest/LinearAlgebra/TensorProduct/Quotient.lean) | Nonzero integer coefficient reduction from `(4)` to `(2)` and zero-map boundary |
| [RingTheory.Teichmuller](../AdicModulesTest/RingTheory/Teichmuller.lean) | Standard p-adic and perfect-coefficient power-series models of Teichmüller sections |
| [RingTheory.TeichmullerCore](../AdicModulesTest/RingTheory/TeichmullerCore.lean) | Teichmüller image with imperfect Laurent-series residue |
| [RingTheory.WittVector](../AdicModulesTest/RingTheory/WittVector.lean) | Nonzero cast of `3` over `ZMod 3` and the nonperfect nonfield `(ZMod 3)[X]` |
| [RingTheory.FrobeniusCore](../AdicModulesTest/RingTheory/FrobeniusCore.lean) | Imperfect Laurent-series noncube and constant-root inputs, inclusion universal property and reduced-product boundary |
| [RingTheory.TeichmullerFractionFieldModel](../AdicModulesTest/RingTheory/TeichmullerFractionFieldModel.lean) | Independent usual 3-adic and imperfect-residue power-series fraction-field inputs; final image-law consumers |
| [RingTheory.Ideal.IsPrincipalPowQuotient](../AdicModulesTest/RingTheory/Ideal/IsPrincipalPowQuotient.lean) | A nonzero class in the first principal-power quotient |
| [RingTheory.Ideal.ScalarIntersection](../AdicModulesTest/RingTheory/Ideal/ScalarIntersection.lean) | Scalar images and intersections of comaximal ideals on integer, `ZMod 6` and natural-product modules |
| [RingTheory.Ideal.Quotient.Finite](../AdicModulesTest/RingTheory/Ideal/Quotient/Finite.lean) | Integer quotient and boundary calculations |
| [RingTheory.Ideal.Quotient.FiniteEquivalence](../AdicModulesTest/RingTheory/Ideal/Quotient/FiniteEquivalence.lean) | Canonical equivalence sending `[8]` to `([0], [2])` modulo `(2)` and `(3)` |
| [RingTheory.Ideal.Quotient.FinitePowers](../AdicModulesTest/RingTheory/Ideal/Quotient/FinitePowers.lean) | Independent powers-surjectivity example `[172]` modulo `(4)`, `(9)` and `(5)` |
| [RingTheory.Ideal.Quotient.FiniteInverse](../AdicModulesTest/RingTheory/Ideal/Quotient/FiniteInverse.lean) | Inverse class `[8]`, uniqueness in the quotient, all representatives modulo `(6)` and commutative inverse agreement |
| [RingTheory.Ideal.Quotient.FiniteLinear](../AdicModulesTest/RingTheory/Ideal/Quotient/FiniteLinear.lean) | Generic uses of the seven linear characteristic identities and the inverse-class bridge; canonical `ℤ`-linear equivalence, `[8]` and `2 • [8]` |
| [RingTheory.Ideal.Quotient.FiniteReduction](../AdicModulesTest/RingTheory/Ideal/Quotient/FiniteReduction.lean) | Forward/inverse precision `2` to `1` squares for `[8]`, including mixed zero precision |
| [RingTheory.Ideal.Quotient.Matrix](../AdicModulesTest/RingTheory/Ideal/Quotient/Matrix.lean) | Two-sided matrix quotient examples |
| [RingTheory.Ideal.Quotient.LeftIdeal](../AdicModulesTest/RingTheory/Ideal/Quotient/LeftIdeal.lean) | Surjective binary left-module diagonal and nonsurjective pairwise comaximal ternary diagonal |
| [Topology.Algebra.SubmoduleClosure](../AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean) | Discrete, indiscrete and adic integer closures, proposition indices and active predicates |
| [Topology.Algebra.PadicInt](../AdicModulesTest/Topology/Algebra/PadicInt.lean) | Proper dense integer spans, excluded elements, positive-degree neighborhood suprema and basis boundaries |
| [Topology.Algebra.PrincipalUnits](../AdicModulesTest/Topology/Algebra/PrincipalUnits.lean) | Principal units in mixed and equal characteristic |
| [Topology.Algebra.Ideal.Int](../AdicModulesTest/Topology/Algebra/Ideal/Int.lean) | Four original private `(3)`/`(2)` calculations on integers, including proper density; additional private density-criterion application |
| [Topology.Algebra.Ideal.Matrix](../AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean) | Non-two-sided `M₂(ℤ)` columns, induced powers topology, nonclosed proper dense ideal, non-Hausdorffness and discontinuous right multiplication |
| [RingTheory.Ideal.Operations.MatrixNat](../AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean) | `M₂(ℕ)` columns, original all-power calculations, noncommuting noninvertible matrix units and generator-power warning; additional private comaximal-powers application |
| [Topology.Algebra.Ideal.Boundary](../AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean) | All seven ideal-power algebraic and topological boundary groups |
| [Topology.Algebra.Module.Span.Real](../AdicModulesTest/Topology/Algebra/Module/Span/Real.lean) | Rational real axis and integer real line controls |
| [Topology.Algebra.Module.Span.Discrete](../AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean) | Discrete and mixed real-module controls |
| [Topology.Algebra.Module.Span.PadicInt](../AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean) | Arbitrary singleton comparison, unit/nonunit/zero and norm-neighborhood controls |
| [Topology.Algebra.Module.Span.Boundary](../AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean) | Empty, zero, subsingleton and non-T1 indiscrete self-module controls |
| [Topology.Algebra.Module.Span.Indiscrete](../AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) | Dense integer casts with failed coefficient continuity on an independent discrete rational module |
| [Topology.Algebra.Module.AdicTopology](../AdicModulesTest/Topology/Algebra/Module/AdicTopology.lean) | The integer-pair projection and adic module neighborhoods |
| [Valuation.Completeness](../AdicModulesTest/Valuation/Completeness.lean) | 5-adic and complete discrete-valuation integer examples, including the zero generator |
| [FractionFieldCompletenessPadicClient](../AdicModulesTest/FractionFieldCompletenessPadicClient.lean) | Private 3-adic maximal-ideal valuation, independent norm-uniformity comparison and adic completeness, and converse application |
| [FractionFieldCompletenessSeriesClient](../AdicModulesTest/FractionFieldCompletenessSeriesClient.lean) | Private power/Laurent-series valuation identification and coefficientwise completeness over any field, adic applications and negative-degree obstruction |
| [ValuationTopology](../AdicModulesTest/ValuationTopology.lean) | Principal-adic and valuation topology import client |
| [CompletedIntegers](../AdicModulesTest/CompletedIntegers.lean) | Completed-valuation-integer equivalence and canonical-map client |
| [CompletedLocalStructure](../AdicModulesTest/CompletedLocalStructure.lean) | Local domain, fraction-field and residue interfaces |
| [PrincipalAdicSpectrum](../AdicModulesTest/PrincipalAdicSpectrum.lean) | Ideal and spectrum comparison clients with their hypotheses |
| [LocalizedFiltration](../AdicModulesTest/LocalizedFiltration.lean) | Base-power images, localized topology and separation clients |
| [LocalizedCompletion](../AdicModulesTest/LocalizedCompletion.lean) | Localized completion embedding client |
| [LocalizedValuationSubring](../AdicModulesTest/LocalizedValuationSubring.lean) | Common completed-field realization client |
| [LocalizedResidueField](../AdicModulesTest/LocalizedResidueField.lean) | Localization/completion residue comparison client |
| [LocalizedQuotientValuationSubring](../AdicModulesTest/LocalizedQuotientValuationSubring.lean) | Nonzero-prime quotient-factor client |
| [CompositeValuationSubring](../AdicModulesTest/CompositeValuationSubring.lean) | Residue-preimage composite and whole-field boundary client |
| [CompletedValuationComposite](../AdicModulesTest/CompletedValuationComposite.lean) | Completed-composite identification client |
| [Axioms](../AdicModulesTest/Axioms.lean) | Aggregate public-root import only; no axiom census |

General nonseparated reduction, height/rational-rank additivity, isolated-subgroup
classification and value-group exact sequences are outside the asserted scope.
Source-level correspondence and whole-source coverage are separate research
decisions, not consequences of these APIs or this guide.

## Reproduction and resources

Use the checked-in Lean v4.34.0-rc2 and mathlib revision
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, including all transitive manifest
pins. Fetch `lake exe cache get` successfully before a build; an absent cache is
not permission to silently rebuild all of mathlib. On smaller machines, avoid
other concurrent builds. `LEAN_NUM_THREADS=2` sets each Lean runtime's worker
count; it does not cap the number of concurrent Lake jobs or processes, or total
build memory. No verified whole-build process or RAM cap is supplied here.
Leave space for several gigabytes of dependency sources and artifacts.

The default library targets are `AdicModules` and `AdicModulesTest`, with the
`AdicModulesTest.+` glob including all 64 current independent test/model/audit
files. The normal reproduction command is
`lake build AdicModules AdicModulesTest` (or `lake build` for both default targets).
This covers the 50 production sources (including the root) and 64 test/model/audit
sources in the complete current map. The four left-ideal models and five span
models are source files, not measures of test throughput or proof coverage.
Private verification fixtures may emit private-module advisories by design.
Complete library proof-integrity assurance is not claimed by these descriptions
or model calculations. A complete transitive
audit must cover private, generated, test and imported declarations and permit
only `propext`, `Classical.choice` and `Quot.sound`.

### Build options and the historical API

At `⊤`, scalar-restriction completions are trivial even for nonzero `M`; the
identity and polynomial algebra examples also include `⊥` and level zero.
These boundaries are part of the same comparison, not extra nontriviality
premises.

The normal build recipe does not make warnings fatal. Private example modules
may emit private-module advisories. An optional stricter individual command is
`lake env lean -DwarningAsError=true AdicModulesTest/AdicCompletion/RestrictScalars.lean`
after fetching the matching cache. This is a command example, not a statement
that such a check has been performed. The import-only
[`Axioms.lean`](../AdicModulesTest/Axioms.lean) is not an axiom census. A relevant
build and a complete transitive standard-axiom audit are distinct requirements;
the latter includes private, generated, test and imported declarations and
permits only `propext`, `Classical.choice` and `Quot.sound`. Historical results,
generated documentation and selected audits do not replace checks of the
particular revision. No separate stored-proof replay is required.

The [historical API](API.md) and [generation notes](README.md) describe 13
mathematical leaves, 28 modules and 103 display sites at their recorded revision.
They predate the primary-component, scalar-restriction, integer-singleton-span,
submodule-closure, p-adic, left-ideal, finite-quotient and span-comparison leaves
and related examples. They are not a current whole-library or complete
kernel-declaration inventory. Use this guide, the
[primary-component supplement](PrimaryComponent.md), the
[finite-quotient guide](FiniteQuotient.md) and current Lean signatures instead.

### Build and documentation limits

Allow more time and memory on a cold or different machine; the thread setting
above is not a whole-build memory or process cap. Build success and selected
`#print axioms` output are distinct from a complete transitive standard-axiom
audit, including private/generated and test declarations. Native API documentation
has its own source/pin binding and reproduction requirements; documentation output
is not proof-integrity or source-coverage evidence.
