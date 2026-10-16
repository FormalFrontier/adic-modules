# adic-modules

Authors: Formal Frontier Agents

Lean results on ideal-power torsion, adic completions, finite Chinese remainders,
integer spans, submodule closure, ideal-power density and valuation rings.
Import `AdicModules` for the public library, or an individual module for narrower
dependencies. The library reuses Lean and mathlib's ideals, modules, topologies
and inverse limits.

## Headline results

- **Scalar-power torsion and completion coordinates.** For an
  additive commutative group `V`, subgroup `L`, and integer `ℓ` acting bijectively
  on `V`, the [comparison](AdicModules/AdicCompletion/QuotientTorsion.lean)
  constructs a linear equivalence from stock compatible sections of the kernels
  of `ℓ ^ n` on `V / L` to `AdicCompletion (Ideal.span {ℓ}) L`. Its coordinate
  statements send `[v]` to `[ℓ ^ n • v]`; negative scalars require a degreewise
  sign twist of the natural-scalar quotient-torsion equivalence. The independent
  [rational model](AdicModulesTest/ScalarTorsionSections.lean)
  constructs the nonzero family `[1 / (-2) ^ n]` and proves that its untwisted
  natural coordinates fail ordinary reduction from degree three to degree two,
  whereas the sign-normalized coordinates agree.

- **Coprime Hensel factor lifting.**
  For any commutative ring `R`, any ideal `I` and `[IsAdicComplete I R]`,
  a monic `f : R[X]` whose reduction is a product of **coprime monic**
  `g₀, h₀ : (R ⧸ I)[X]` has monic coprime factors `g, h : R[X]` with
  `f = g * h` and reductions exactly `g₀, h₀`.
  `Polynomial.exists_monic_factorization_of_isAdicComplete` needs no
  nontriviality, proper-ideal, local-ring, Noetherian or finite-generation
  assumption. It does not assert uniqueness or supply a chosen factorization.
  See the [factor-lifting module](AdicModules/Polynomial/Hensel.lean) and the
  [5-adic `X² - 6` example](AdicModulesTest/Polynomial/Hensel.lean).

- **Irreducible reduction from global factor lifting.**
  `Polynomial.exists_monic_irreducible_pow_of_monic_factorization` takes a
  commutative ring `R`, a maximal ideal `I` and an explicit **global** property:
  every monic polynomial, including reducible ones, admits monic lifts of each
  coprime monic factorization modulo `I`, with both prescribed reductions.
  Every monic irreducible `f : R[X]` then reduces to `q ^ e`, with `q` monic
  irreducible and `e > 0`. No domain, local-ring, completeness, Noetherian or
  finite-residue-field hypothesis is imposed. The proof separates one irreducible
  power from its coprime complement; lifting and irreducibility force the complement to be 1.
  `Polynomial.exists_monic_irreducible_pow_of_isAdicComplete` is the corollary
  with `[IsAdicComplete I R]`, using the coprime factor theorem above.
  The [5-adic examples](AdicModulesTest/Polynomial/Hensel.lean) independently prove
  that `X² - 5` is monic irreducible over `ℤ₅` and `ℚ₅` and reduces to the
  nonirreducible `X²`; they supply the global property, apply both criteria and exhibit exponent 1.
  Compare Fesenko–Vostokov, *Local Fields and Their Extensions*, II, §1,
  Exercise 4, p. 38. Monic integral representatives relate the source's global
  factor-lifting property to this quotient formulation. For a valuation domain
  and its fraction field, Mathlib's `Polynomial.Monic.irreducible_of_irreducible_map`
  supplies integer-polynomial irreducibility from field irreducibility. No new
  Henselian class, equivalence with Mathlib's simple-root Henselian classes or
  whole-source coverage is asserted.

- **Bounded torsion and primary components.**
  `Module.IsKilledByIdealPower R M I` means one exponent annihilates the whole
  module. Submodule and surjective-image results work over a commutative semiring
  and additive commutative monoid; quotient and extension results retain their
  commutative-ring/additive-group hypotheses. Over a commutative ring, equivalence
  with `Ideal.primaryComponent M I = ⊤` requires **`Module.Finite R M`**
  (finite generation). Separately, height-one primary components preserve an exact
  pair over a Dedekind domain when its **source is torsion**, without finiteness,
  a uniform exponent or torsion of the other modules. The abelian-group version
  concerns the actual restricted maps on ordinary `p`-primary subgroups,
  also with a torsion source.
  See [bounded torsion](docs/Guide.md#uniform-bounded-torsion) and
  [primary-component exactness](docs/PrimaryComponent.md).

- **Adic completions and restricting scalars.**
  `AdicCompletion.abstractCompletion` requires a commutative ring, a compatible
  uniform additive-group structure, `IsAdic I` and `I.FG`.
  In contrast, for commutative rings `R`, `S`, an `R`-algebra `S` and an additive
  commutative group `M` with compatible module actions and `IsScalarTower R S M`,
  `AdicCompletion.restrictScalarsEquiv I M` is an **`R`-linear** equivalence
  from the completion for `I.map (algebraMap R S)` to that for any `I : Ideal R`.
  Its quotient, transition, evaluation and canonical-map identities work in both
  directions, including level zero and `⊥`/`⊤`. This is not tensor base change;
  it needs no finite generation, flatness, separatedness or completeness premise.
  See [completion hypotheses](docs/Guide.md#completion-and-valuation-hypotheses)
  and [scalar restriction](docs/Guide.md#restricting-scalars-in-adic-completions).

- **Unit detection and local adic completions.**
  For a commutative ring `R` in any universe and any `I : Ideal R`, write
  `C = AdicCompletion I R` and `q = AdicCompletion.evalOneₐ I`. The canonical
  projection `q : C →ₐ[R] R ⧸ I` is reduction at **level one**. For every `x : C`,
  `AdicCompletion.isUnit_evalOne_iff I x` gives `IsUnit (q x) ↔ IsUnit x`.
  `AdicCompletion.isLocalHom_evalOne I` supplies an `IsLocalHom q.toRingHom`
  instance, and `AdicCompletion.ker_evalOne_le_jacobson I` gives
  `RingHom.ker q.toRingHom ≤ Ideal.jacobson (⊥ : Ideal C)`.
  With **only `[IsLocalRing (R ⧸ I)]`**,
  `AdicCompletion.isLocalRing_of_quotient I` gives `IsLocalRing C`.
  No finite generation, Noetherianity or locality of `R` is required. The unit,
  local-homomorphism and kernel results cover `I = ⊥`, `I = ⊤` and trivial
  rings; the final premise includes nontriviality of `R ⧸ I`. See the
  [unit detection and local-completion module](AdicModules/AdicCompletion/LocalRing.lean).

- **Adic completion of finite projective modules.**
  For a commutative ring `R`, an additive commutative group `M` with `Module R M`,
  `Module.Finite R M` and `Module.Projective R M`, and any ideal `I`,
  `AdicCompletion.ofTensorProduct_bijective_of_finite_of_projective I M` proves
  bijectivity of Mathlib's canonical comparison. The constructed
  `AdicCompletion.ofTensorProductEquivOfFiniteProjective I M` is an
  **`AdicCompletion I R`-linear** equivalence
  `AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M`.
  Its underlying linear map is `AdicCompletion.ofTensorProduct I M`; its
  characteristic lemmas give `a ⊗ₜ m ↦ a • AdicCompletion.of I M m` and
  `AdicCompletion.of I M m ↦ 1 ⊗ₜ m` for the inverse. Ring and module universes
  are independent; no Noetherian or finitely generated ideal hypothesis is needed.
  The separate `ofTensorProductEquivOfFiniteProjective_eq_ofFiniteNoetherian`
  lemma identifies it with Mathlib's Noetherian equivalence where both apply:
  over a Noetherian ring, with the ring and module in the same universe.
  See the [tensor comparison module](AdicModules/AdicCompletion/TensorProduct.lean)
  and its [integer models](AdicModulesTest/AdicCompletion/TensorProduct.lean).

- **Integer singleton spans in unital rings.**
  For a `NonAssocRing R`, additive cyclicity or a top singleton integer span
  implies surjectivity of `ℤ → R`. Nonsurjective casts therefore make **every**
  singleton integer span proper, using the canonical additive-group integer
  action. No multiplication associativity, commutativity, characteristic-zero,
  nontriviality or topology premise is needed. Properness of one span does not
  imply nonsurjective casts: `(2)` is proper in `ℤ`. See the
  [integer-span guide](docs/Guide.md#integer-singleton-spans-in-unital-rings),
  including all `ZMod n` and noncommutative integer-matrix examples.

- **Kernel pullbacks with monoid targets.**
  `Submodule.comap_map_eq_sup_ker` proves
  `Submodule.comap f (Submodule.map f N) = N ⊔ LinearMap.ker f` for
  semilinear maps from additive commutative groups to additive commutative
  monoids along surjective scalar homomorphisms. The submodule need not be
  closed under negation, and the target need not have additive cancellation.

- **Submodule closure from a neighborhood basis.**
  `Submodule.topologicalClosure_eq_iInf_sup` gives
  `N.topologicalClosure = ⨅ i, ⨅ (_ : p i), N ⊔ U i` when the active `U i`
  form a zero-neighborhood basis. It works over a semiring on an additive
  commutative group with a module structure, a **given compatible topological
  additive-group structure** and continuous fixed-scalar maps. Scalar, module
  and `Sort`-valued index universes are independent. No scalar topology, joint
  scalar continuity, Hausdorffness, countability or closedness is assumed; it
  does not construct a topology. See the [closure guide](docs/Guide.md#submodule-closure-from-a-neighborhood-basis).

- **Scalar images of comaximal ideals.**
  Over a commutative semiring `R`, an additive commutative monoid `M` with its
  `R`-module structure and any submodule `N`,
  `Submodule.ideal_smul_inf_of_sup_eq_top` gives
  `I ⊔ J = ⊤ → (I ⊓ J) • N = (I • N) ⊓ (J • N)`.
  For `I : ι → Ideal R`, any `s : Finset ι` and pairwise comaximality only on
  `(s : Set ι)`, `Submodule.ideal_smul_iInf_of_pairwise_sup_eq_top` gives
  `(⨅ i ∈ s, I i) • N = N ⊓ (⨅ i ∈ s, I i • N)`.
  The cap with `N` is essential for the empty selection: both indexed
  intersections are top, while the left side is `N`, which may be proper.
  These use the canonical ideal action generated by finite sums of scalar
  multiples, with independent scalar, module and index universes. No additive
  inverses, multiplication on `M`, finite ambient index type, finite generation
  or flatness is assumed. See the
  [ideal operations module](AdicModules/RingTheory/Ideal/Operations.lean).

- **Comaximal powers of left ideals and density in powers topologies.**
  `Ideal.sup_pow_eq_top_of_sup_eq_top` gives `J ⊔ I = ⊤ → J ⊔ I ^ n = ⊤`
  for arbitrary left ideals in any semiring and every natural `n`, including zero.
  `Ideal.pairwise_sup_eq_top_pow` allows independent powers of a pairwise
  comaximal family, without finite-index or two-sidedness assumptions. Powers
  are **whole ideal powers**, not spans of generator powers; neither additive
  inverses, commutativity nor multiplication cancellation is needed.
  Separately, `Ideal.dense_iff_sup_eq_top_of_hasBasis` gives
  `Dense (J : Set R) ↔ J ⊔ I = ⊤` for a ring with a **supplied compatible
  additive-group topology** whose zero neighborhoods have basis `I ^ n`.
  Neither ideal needs two-sidedness; no ring-multiplication or ring-scalar
  continuity is assumed. See [comaximal powers](docs/Guide.md#comaximal-powers-of-left-ideals),
  [density](docs/Guide.md#left-ideal-density-and-integer-powers-topologies),
  [integer/matrix models](docs/Guide.md#matrix-left-ideal-models) and
  [boundary models](docs/Guide.md#ideal-power-boundary-models).

- **Finite Chinese remainder equivalence for two-sided ideals.**
  For a possibly noncommutative `[Ring R]`, independent ring/index universes,
  a finite **index type** `[Finite ι]`, `I : ι → Ideal R`, full
  `[∀ i, (I i).IsTwoSided]` and `Pairwise (fun i j => I i ⊔ I j = ⊤)`,
  `Ideal.quotientInfRingEquivPiQuotientOfPairwiseSupEqTop I hI` gives
  `(R ⧸ ⨅ i, I i) ≃+* ((i : ι) → R ⧸ I i)` with Mathlib's **same canonical**
  `Ideal.quotientInfToPiQuotient` as its forward map. Prescribed residues give
  a unique quotient class, simultaneous ring representatives and their full
  additive coset modulo the intersection, not a unique ring element.
  Independent natural powers, including zero, use the original-family guard;
  forward/inverse reduction squares commute for inclusions and power precisions.
  The canonical map preserves the common left `R`-action; the linear-equivalence
  definition uses this ring equivalence's existing additive data. In a `CommRing`,
  the ring-equivalence value and its inverse agree with Mathlib's versions.
  No finiteness of `R`, domain, cancellation, finite-generation, Noetherian or
  flatness premise is imposed. This is algebraic ring CRT, not a topology,
  completion or general module CRT. See the [finite-quotient guide](docs/FiniteQuotient.md)
  for formulas, API names, integer examples and the arbitrary-left-ideal boundary.

- **P-adic neighborhood bases and proper dense integer spans.**
  For prime `p`, powers generated by `p ^ n` form a zero-neighborhood basis in
  the usual norm topology on `ℤ_[p]`, including `n = 0`. Restriction to `ℤ`
  retains **all p-adic multiples**; linearity for self/integer scalars uses no
  new global instances. In any ring with dense integer casts and continuous
  fixed-ring-scalar multiplication, the integer span of a unit is dense.
  Thus p-adic units and integer generators not divisible by `p` give dense
  spans, while every integer generator, even `0` and `±1`, has proper span.
  In `ℤ_[2]`, the integer span of `3` is proper and dense, excludes `1`, and
  sums to top with every restricted ideal generated by `2 ^ n`; it is not the
  self-scalar ideal of the unit `3`. See the [p-adic guide](docs/Guide.md#p-adic-neighborhood-bases-and-integer-spans).

- **Adic completeness of valuation integers.**
  If `V` is the integer ring of a field `K` complete for its **valuation
  uniformity**, then `Valuation.Integers.isAdicComplete_span_singleton` gives
  `IsAdicComplete (Ideal.span {a}) V` whenever the powers of `(a)` are separated.
  This includes `a = 0`, with no rank, discreteness, Noetherianity, finite-residue
  or local-compactness hypothesis. No topology on `V` is assumed. See the
  [completeness module](AdicModules/Valuation/Completeness.lean) and its
  [5-adic and discrete-valuation examples](AdicModulesTest/Valuation/Completeness.lean).

- **Valuation topology, completed integers and spectra.**
  For a valuation domain `V`, fraction field `K`, nonzero `a : V` and separated
  `(a)`-adic topology, principal-adic and induced valuation topologies agree.
  `ValuationRing.principalAdicCompletionEquiv` compares the inverse limit with
  the valuation integers of the completed fraction field as `V`-algebras,
  compatibly with canonical maps and with independent universes for `V`, `K`.
  That ring is a valuation domain with the completed field as fraction field.
  Ideal extension-after-contraction and extended-valuation comparisons are
  included; nonfield, faithful-flatness and prime-spectrum order-isomorphism
  results additionally require **`a` in the maximal ideal**. No rank-one,
  discreteness or Noetherian premise is added. See [valuation hypotheses](docs/Guide.md#completion-and-valuation-hypotheses).

- **Localization in one completed fraction field.**
  Denominators disjoint from the radical of `(a)` give literal base-power images
  as `V`-submodules, sandwiched between successive extended-ideal powers, not
  unconditionally equal to those powers. This filtration defines the localized
  topology; principal-adic separatedness gives separation. With `a ≠ 0`, those
  denominator and separatedness hypotheses give an embedding of the localized
  completion into the common completed field, a valuation-subring description
  and a residue-field comparison. At a nonzero prime, separatedness supplies
  radical-disjointness; the quotient valuation subring retains these premises.
  See the [localization guide](docs/Guide.md#localization-and-literal-composites).

- **Literal composite valuations.**
  `ValuationSubring.composite` is a residue preimage; localization at its
  distinguished prime and quotient recover the factors. The completed valuation
  integers above equal the composite of the completed localization and the
  transported residue factor **literally**, not by a new notion of completion.
  See [composites](docs/Guide.md#localization-and-literal-composites).

- **Closure of spans over a dense subsemiring.**
  For a semiring `R`, additive commutative monoid `M` with `Module R M`,
  independent universes/topologies, dense `A : Subsemiring R`, separately
  continuous addition on `M` and continuity of `r ↦ r • m` **only for `m ∈ E`**,
  `Submodule.closure_span_eq_of_dense_subsemiring` equates the set closures of
  `Submodule.span A E` and `Submodule.span R E` for the same canonical action.
  No additive group, joint addition, global coefficient continuity,
  `ContinuousSMul`, `T1`, nonempty or finite generating set is required.
  For empty/zero generators the closure is `closure {0}`, not necessarily `{0}`.
  See the [span-comparison guide](docs/Guide.md#closure-of-spans-over-a-dense-subsemiring)
  for real, discrete, mixed, p-adic and indiscrete examples and counterexamples.

## Imports and module map

Use `import AdicModules` or a narrower library leaf from the table. Related
`AdicModulesTest` modules require separate imports and are not re-exported by
that root; some expose named concrete results, while the left-ideal and span
models keep their calculations private. The [mathematical guide](docs/Guide.md)
provides detailed hypotheses, formulas, examples and the full source roster.

| Library leaf (prefix `AdicModules.`) | Related modules (prefix `AdicModulesTest.`) |
| --- | --- |
| [BoundedIdealPowerTorsion](AdicModules/BoundedIdealPowerTorsion.lean) | [BoundedIdealPowerTorsion](AdicModulesTest/BoundedIdealPowerTorsion.lean) |
| [Polynomial.Hensel](AdicModules/Polynomial/Hensel.lean) | [Polynomial.Hensel](AdicModulesTest/Polynomial/Hensel.lean) |
| [PrimaryComponent](AdicModules/PrimaryComponent.lean) | [PrimaryComponent](AdicModulesTest/PrimaryComponent.lean) |
| [AdicCompletion](AdicModules/AdicCompletion.lean) | [AdicCompletion](AdicModulesTest/AdicCompletion.lean) |
| [AdicCompletion.RestrictScalars](AdicModules/AdicCompletion/RestrictScalars.lean) | [AdicCompletion.RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| [AdicCompletion.LocalRing](AdicModules/AdicCompletion/LocalRing.lean) | [AdicCompletion.LocalRing](AdicModulesTest/AdicCompletion/LocalRing.lean) |
| [AdicCompletion.QuotientTorsion](AdicModules/AdicCompletion/QuotientTorsion.lean) | [ScalarTorsionSections](AdicModulesTest/ScalarTorsionSections.lean) |
| [AdicCompletion.TensorProduct](AdicModules/AdicCompletion/TensorProduct.lean) | [AdicCompletion.TensorProduct](AdicModulesTest/AdicCompletion/TensorProduct.lean) |
| [Algebra.Module.Int](AdicModules/Algebra/Module/Int.lean) | [Algebra.Module.Int](AdicModulesTest/Algebra/Module/Int.lean) |
| [LinearAlgebra.Span.Basic](AdicModules/LinearAlgebra/Span/Basic.lean) | [KernelPullback](AdicModulesTest/KernelPullback.lean) |
| [RingTheory.Ideal.Operations](AdicModules/RingTheory/Ideal/Operations.lean) | [RingTheory.Ideal.Operations.MatrixNat](AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean) (independent original calculations; additional private comaximal-powers application) |
| [RingTheory.Ideal.Quotient.Finite](AdicModules/RingTheory/Ideal/Quotient/Finite.lean) | [RingTheory.Ideal.Quotient.Finite](AdicModulesTest/RingTheory/Ideal/Quotient/Finite.lean) (integer quotient and boundary calculations), [RingTheory.Ideal.Quotient.FiniteEquivalence](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteEquivalence.lean) (equivalence client), [RingTheory.Ideal.Quotient.FinitePowers](AdicModulesTest/RingTheory/Ideal/Quotient/FinitePowers.lean) (powers-surjectivity client), [RingTheory.Ideal.Quotient.FiniteInverse](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteInverse.lean) (inverse and representatives client), [RingTheory.Ideal.Quotient.FiniteLinear](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteLinear.lean) (linear definition and integer client), [RingTheory.Ideal.Quotient.FiniteReduction](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteReduction.lean) (precision-reduction client), [RingTheory.Ideal.Quotient.Matrix](AdicModulesTest/RingTheory/Ideal/Quotient/Matrix.lean) (two-sided matrix examples), [RingTheory.Ideal.Quotient.LeftIdeal](AdicModulesTest/RingTheory/Ideal/Quotient/LeftIdeal.lean) (left-ideal counterexample) |
| [Topology.Algebra.Ideal](AdicModules/Topology/Algebra/Ideal.lean) | [Topology.Algebra.Ideal.Int](AdicModulesTest/Topology/Algebra/Ideal/Int.lean), [Topology.Algebra.Ideal.Matrix](AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean), [Topology.Algebra.Ideal.Boundary](AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean) (independent original calculations; additional private density application in Int) |
| [Topology.Algebra.Submodule](AdicModules/Topology/Algebra/Submodule.lean) | [Topology.Algebra.SubmoduleClosure](AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean) |
| [Topology.Algebra.PadicInt](AdicModules/Topology/Algebra/PadicInt.lean) | [Topology.Algebra.PadicInt](AdicModulesTest/Topology/Algebra/PadicInt.lean) |
| [Topology.Algebra.Module.Span](AdicModules/Topology/Algebra/Module/Span.lean) | [Topology.Algebra.Module.Span.Real](AdicModulesTest/Topology/Algebra/Module/Span/Real.lean), [Topology.Algebra.Module.Span.Discrete](AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean), [Topology.Algebra.Module.Span.PadicInt](AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean), [Topology.Algebra.Module.Span.Boundary](AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean), [Topology.Algebra.Module.Span.Indiscrete](AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) (independent original calculations; additional private comparison application in Real) |
| [Valuation.Completeness](AdicModules/Valuation/Completeness.lean) | [Valuation.Completeness](AdicModulesTest/Valuation/Completeness.lean) |
| [ValuationTopology](AdicModules/ValuationTopology.lean) | [ValuationTopology](AdicModulesTest/ValuationTopology.lean) |
| [CompletedIntegers](AdicModules/CompletedIntegers.lean) | [CompletedIntegers](AdicModulesTest/CompletedIntegers.lean) |
| [CompletedLocalStructure](AdicModules/CompletedLocalStructure.lean) | [CompletedLocalStructure](AdicModulesTest/CompletedLocalStructure.lean) |
| [PrincipalAdicSpectrum](AdicModules/PrincipalAdicSpectrum.lean) | [PrincipalAdicSpectrum](AdicModulesTest/PrincipalAdicSpectrum.lean) |
| [LocalizedFiltration](AdicModules/LocalizedFiltration.lean) | [LocalizedFiltration](AdicModulesTest/LocalizedFiltration.lean) |
| [LocalizedCompletion](AdicModules/LocalizedCompletion.lean) | [LocalizedCompletion](AdicModulesTest/LocalizedCompletion.lean) |
| [LocalizedValuationSubring](AdicModules/LocalizedValuationSubring.lean) | [LocalizedValuationSubring](AdicModulesTest/LocalizedValuationSubring.lean) |
| [LocalizedResidueField](AdicModules/LocalizedResidueField.lean) | [LocalizedResidueField](AdicModulesTest/LocalizedResidueField.lean) |
| [LocalizedQuotientValuationSubring](AdicModules/LocalizedQuotientValuationSubring.lean) | [LocalizedQuotientValuationSubring](AdicModulesTest/LocalizedQuotientValuationSubring.lean) |
| [CompositeValuationSubring](AdicModules/CompositeValuationSubring.lean) | [CompositeValuationSubring](AdicModulesTest/CompositeValuationSubring.lean) |
| [CompletedValuationComposite](AdicModules/CompletedValuationComposite.lean) | [CompletedValuationComposite](AdicModulesTest/CompletedValuationComposite.lean) |
| No library leaf; aggregate root import | [Axioms](AdicModulesTest/Axioms.lean) (import-only, not an axiom census) |

## Build and reference

Install the Lean version pinned in [`lean-toolchain`](lean-toolchain) with elan,
retain [`lake-manifest.json`](lake-manifest.json) and fetch the matching cache
successfully before building; do not silently rebuild mathlib if it is unavailable:

```sh
lake exe cache get
lake build AdicModules AdicModulesTest
```

Both libraries are default targets. `AdicModulesTest.+` includes the separate
example files; there is no `AdicModulesTest.lean` aggregate root. See
[reproduction and resources](docs/Guide.md#reproduction-and-resources) for build
options and historical resource observations, not machine-size guarantees.
The [historical API snapshot](docs/API.md) and [generation notes](docs/README.md)
cover 13 leaves, 28 modules and 103 display sites, not the current whole library.
Use this guide, [primary components](docs/PrimaryComponent.md), the
[finite-quotient guide](docs/FiniteQuotient.md) and current Lean signatures.

## Credits, references and scope

Developed and reviewed by Formal Frontier AI agents; this is not human peer
review, source-author endorsement or complete formalization of a selected source.
The project uses [Apache-2.0](LICENSE). [Credits and provenance](docs/CREDITS.md)
retain project authorship, upstream author notices, stock-API reuse and the full
mathematical bibliography, including Kenny Lau and Patrick Massot's CRT credit.
The tensor comparison reuses Mathlib's adic-completion API by Judith Ludwig and
Christian Merten, including finite-product bijectivity and the Noetherian comparison.

The coprime Hensel theorem follows the factor-lifting form in I. B. Fesenko and
S. V. Vostokov, *Local Fields and Their Extensions*, second edition (2002), II, §1,
Corollary 1, generalized to adically complete rings. Its proof assembles Andrew Yang's
Mathlib universal coprime factorization ring and the formally smooth adic lifting
API of Judith Ludwig and Christian Merten.

The local-completion results use Mathlib's canonical completion and algebraic
projections (Judith Ludwig and Christian Merten), positive-power quotient-unit
lifting, `IsLocalHom`/`isUnit_map_iff`, `Ideal.mem_jacobson_bot` and
`RingHom.domain_isLocalRing`. The
[local-completion module](AdicModules/AdicCompletion/LocalRing.lean) records
the corresponding upstream author credits.

- I. Fesenko and S. Vostokov, *Local Fields and Their Extensions*, second edition
  (2002), II §1 (motivation for the valuation-integers completeness bridge).
- K. Fujiwara and F. Kato, *Foundations of Rigid Geometry I* (2017),
  [arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5).
- [Lean](https://lean-lang.org/) and [mathlib4](https://github.com/leanprover-community/mathlib4).

General nonseparated reduction, arbitrary-denominator localization, value-group
exact sequences, height/rational-rank additivity and whole-source coverage or
correspondence are outside the asserted scope of this source-independent library.

The scalar-torsion comparison reuses the quotient-torsion equivalence and its
representative formula from [Group Theory](https://github.com/FormalFrontier/group-theory),
together with Mathlib's sequence functors, sections and adic completion. Its
signed successor proof follows the scalar-transition calculation with the sign
unit inserted degreewise. The rational nonvanishing argument follows Group
Theory's rational half-class test.
