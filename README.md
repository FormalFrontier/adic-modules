# adic-modules

Authors: Formal Frontier Agents

Lean results on ideal-power torsion, adic completions, finite Chinese remainders,
integer spans, submodule closure, ideal-power density and valuation rings.
The library reuses Lean and Mathlib's ideals, modules, topologies and inverse limits.
The [results reference](docs/Results.md) retains detailed statements, API names,
models and mathematical credits; the [Guide](docs/Guide.md) develops usage.

## Using the library

Add a dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "adic-modules"
git = "https://github.com/FormalFrontier/adic-modules.git"
rev = "main"
```

GitHub `main` contains only reviewed releases. Lake resolves it when you first add
or update the dependency; your project's `lake-manifest.json` records that commit.
For an explicit version, replace `main` with a full release commit from its history.
Use the Lean toolchain of the selected release; libraries used together must share
a Mathlib revision.

Then `import AdicModules`, or choose an individual module from the table below.

## Headline results

- **Adic completion as a functor.** For any ideal `I` of a commutative ring
  `R`, `AdicCompletion.functor I` maps `R`-modules to modules over
  `AdicCompletion I R`, preserving the carrier universe independently of the ring.
  It is additive and `R`-linear, and its action on module isomorphisms agrees with
  `AdicCompletion.congr`. The relative `R`-linear API uses
  `open scoped ModuleCat.Algebra`. Import the
  [functor module](AdicModules/AdicCompletion/Functor.lean) directly; its
  [product-inclusion example](AdicModulesTest/AdicCompletion/Functor.lean) uses
  a specified splitting and includes a nonzero integer-completion boundary.

- **Precompleteness and adic completeness.** Precompleteness for arbitrary
  ideals `I` and `J` implies precompleteness for `I ⊔ J`, without finite
  generation, Noetherianity or Hausdorffness. Finite families, surjective images,
  the separated quotient and principal-ideal completeness fit the same theory.
  See [completeness results](docs/Results.md#precompleteness-and-adic-completeness).

- **Endomorphisms congruent to the identity.** For a module `M` over a
  commutative ring `R` and any ideal `I`, an endomorphism `f : Module.End R M`
  is a unit if `IsAdicComplete I M` and
  `∀ m, f m - m ∈ I • (⊤ : Submodule R M)`. Completeness is required of `M`,
  not of the endomorphism space. See the
  [endomorphism criterion](AdicModules/AdicCompletion/Endomorphism.lean).

- **Adic completion of arbitrary products.** For `I.FG` in a commutative ring `R`,
  `AdicCompletion.piEquivOfFG` is an algebraic `AdicCompletion I R`-linear
  equivalence between completion of a dependent product and the product of
  completions, with no finiteness assumption on the index type or modules.
  The ring, index and module universes are independent, and the original module
  instances are retained. Its forward map is the canonical `AdicCompletion.pi`,
  natural in componentwise linear maps for every ideal. Mathlib's finite-product
  equivalence needs no finite generation; the two agree on their overlap.
  See [product completion](AdicModules/AdicCompletion/Pi.lean).

- **Congruences and polynomial values.** In a commutative ring, `(q : R) ∈ I`
  and `x ≡ y [SMOD I ^ m]` with **positive `m`** imply
  `x^(q^n) ≡ y^(q^n) [SMOD I^(m+n)]` for every natural `n`.
  For `I ≤ Ideal.jacobson ⊥`, any polynomial `g` satisfies
  `b-a ∈ Ideal.span {g.eval a} * I → Associated (g.eval b) (g.eval a)`;
  this includes zero values and nonunit derivatives, without completeness.
  See [congruences and evaluation](docs/Results.md#headline-results).

- **Torsion and primary exactness.** A single ideal power annihilating a whole
  module is equivalent to its ideal-primary component being top over a
  commutative ring **for a finitely generated module**. Submodule/image laws
  work over commutative semirings and additive commutative monoids; quotient and
  extension laws retain ring/group hypotheses. Height-one primary components
  preserve exact pairs over Dedekind domains when **the source alone is torsion**;
  the abelian-group form uses actual restricted maps on ordinary `p`-primary
  subgroups. See [bounded torsion](docs/Guide.md#uniform-bounded-torsion) and
  [primary components](docs/PrimaryComponent.md).

- **Completion coordinates and scalar restriction.** For an additive commutative
  group `V`, subgroup `L` and integer `ℓ` acting bijectively on `V`, compatible
  sections of the `ℓ^n` kernels on `V/L` identify linearly with the `(ℓ)`-adic
  completion of `L`, sending `[v]` to `[ℓ^n • v]`; negative `ℓ` requires a
  degreewise sign twist. For commutative rings `R`, `S`, an `R`-algebra `S` and
  an additive commutative group `M` with compatible module actions and scalar tower,
  completion along `I.map (algebraMap R S)` is **`R`-linearly** equivalent to
  completion along `I`, including both directions and all boundary levels.
  No finiteness, flatness, separation or completeness is needed for this
  scalar restriction; it is not tensor base change. See the
  [coordinate statements](docs/Results.md#headline-results) and
  [scalar-restriction guide](docs/Guide.md#restricting-scalars-in-adic-completions).

- **Linear maps from an adic completion.** Over a commutative ring, any ideal
  admits canonical extension of linear maps into an adically complete module.
  For a finitely generated ideal, maps into a Hausdorff module are determined
  by their restriction to the original module, without target completeness.
  For a finitely generated ideal and a complete target, restriction is an
  `R`-linear equivalence of Hom modules.
  See the [linear-map API](AdicModules/AdicCompletion/LinearMap.lean) and
  [detailed assumptions, laws and nonzero model](docs/Results.md#linear-maps-from-an-adic-completion).

- **Finite-power completion kernels.** For a commutative ring `R`, an additive
  commutative group module `M` and any `n : ℕ`, finite generation of **only
  `I ^ n`** gives `(I ^ n) • ⊤ = (AdicCompletion.eval I M n).ker` in the
  completed module. Ring and module universes are independent; degree zero is
  included. No separate `I.FG`, finite-module, Noetherian, completeness or
  separatedness hypothesis is required. See the [kernel API](AdicModules/AdicCompletion/Kernel.lean)
  and [usage](docs/Guide.md#finite-power-completion-kernels).

- **Finite-power quotients of completions.** For a commutative ring `R`, any
  ideal `I` and any `n : ℕ`, finite generation of **only `I ^ n`** gives the
  canonical `R`-algebra equivalence
  `(AdicCompletion I R ⧸ (I.map (algebraMap R (AdicCompletion I R))) ^ n) ≃ₐ[R] R ⧸ I ^ n`.
  Its forward map is evaluation; its inverse sends `[r]` to the class of
  `algebraMap R (AdicCompletion I R) r`. Degree zero and trivial rings are
  included. See the [quotient API](AdicModules/AdicCompletion/Quotient.lean)
  and [representative and inverse formulas](docs/Guide.md#finite-power-quotients-of-completions).

- **Completion–tensor comparisons.** For any ideal in a commutative ring and an
  additive commutative group module, the canonical `AdicCompletion I R`-linear
  tensor comparison is injective for projective modules without module finiteness.
  It is an equivalence for finite projective modules, or for
  finite modules over a Noetherian ring,
  with independent ring/module universes. For finitely presented modules,
  **finite-free induced/intrinsic cofinality** suffices, without `I.FG`,
  projectivity, flatness or Noetherianity; Artin–Rees supplies it over Noetherian
  rings. Agreement with Mathlib's
  finite-Noetherian equivalence uses a common universe. Quotient–tensor
  naturality holds for ideal inclusions and linear maps without finiteness.
  See [comparison formulas and overlap laws](docs/Results.md#headline-results).

- **Adic topology and local structure.** Over commutative rings, adic module
  topology agrees with the algebra's mapped-ideal topology without finite
  generation. For additive commutative group modules, semilinear maps between
  adic module topologies are continuous when `I.map φ ≤ J`, open when surjective
  and `J ≤ I.map φ`, and open quotient
  maps when surjective and equality holds; scalar-map surjectivity is not needed.
  Evaluation kernels give a completion zero-neighborhood basis for **`I.FG`**,
  without finite `M`. The abstract uniform-completion package needs a compatible
  uniform additive group, `IsAdic I` and `I.FG`. For any ideal in a commutative
  ring, level-one projection detects units and has Jacobson kernel; a local
  residue quotient makes the completion local. For prime `p`, the canonical
  integer `(p)`-adic completion is `ℤ`-algebra isomorphic to `ℤ_[p]`, with all
  residue coordinates, and is a homeomorphism for the mapped-ideal adic topology
  and the usual p-adic norm topology. See [details](docs/Results.md#headline-results).

- **Compactness for a given adic uniformity.** For a commutative ring `R` with
  a given `UniformSpace R`, `IsLeftUniformAddGroup R` and `IsAdic I` for the
  induced topology,
  `CompactSpace R ↔ CompleteSpace R ∧ ∀ n : ℕ, Finite (R ⧸ I ^ n)`.
  All natural powers, including `n = 0`, occur. If `I.FG`, this reduces to
  `CompactSpace R ↔ CompleteSpace R ∧ Finite (R ⧸ I)`.
  Completeness is uniform completeness for this given uniformity, not algebraic
  `IsAdicComplete`. No separation axiom or properness of `I` is required.
  See the [compactness criteria](AdicModules/Topology/Algebra/AdicCompactness.lean).

- **Hensel lifting.** For a commutative ring complete along any ideal, a monic
  polynomial's **coprime monic** residue factors lift with prescribed reductions;
  no locality or properness is required, and uniqueness is not asserted.
  Over any **Henselian pair**, simple residue roots lift for arbitrary polynomials,
  not just monic ones. With `d = f.derivative.eval a`,
  `f.eval a ∈ Ideal.span {d^2} * I` gives a root `b` with
  `b-a ∈ Ideal.span {d} * I` and `Associated (f.eval a) (d * (b-a))`,
  even for zero or nonunit `d`. Separately, a **global** coprime monic
  factor-lifting property for every monic polynomial at a **maximal** ideal makes
  every monic irreducible reduce to a positive power of a monic irreducible.
  Adic completeness supplies that global property; no equivalence of this
  property with simple-root classes is asserted. See [Hensel details](docs/Results.md#headline-results).

- **Monic factor lifting over Henselian pairs.** For an arbitrary commutative
  ring `R` and ideal `I` with Mathlib's `HenselianRing R I`, every ordered,
  prescribed coprime monic factorization of a monic polynomial modulo `I`
  lifts to monic factors over `R`, with the given product and **both**
  prescribed reductions. No completeness or locality is needed. See
  [`HenselianRing.exists_monic_factorization`](AdicModules/Polynomial/Hensel.lean)
  and its [3-adic and zero-ring examples](AdicModulesTest/Polynomial/HenselianFactorization.lean).

- **Monic factor uniqueness.** Over arbitrary commutative rings, a scalar
  unit-reflecting ring map `φ` (`IsLocalHom φ`), only the left factors `g,g'`
  monic, `g*h = g'*h'`, one left-image equality `g.map φ = g'.map φ`, and
  Bézout coprimeness of `g.map φ` and `h.map φ` imply `g=g' ∧ h=h'`.
  No completeness or right monicity is required. See
  [factor uniqueness](AdicModules/Polynomial/Hensel.lean) and its
  [coprimeness criterion](AdicModules/Polynomial/Coprime.lean).

- **Simple-root uniqueness.** For a commutative ring `R`, a possibly
  noncommutative semiring `S` and a scalar unit-reflecting ring map
  `φ : R →+* S` (`IsLocalHom φ`), two roots `a, b` of any polynomial `f`
  with `φ a = φ b` and `IsUnit (φ (f.derivative.eval a))` are equal.
  Ring and semiring universes are independent. See
  [`Polynomial.IsRoot.eq_of_map_eq`](AdicModules/Polynomial/RootUniqueness.lean)
  and its [examples](AdicModulesTest/Polynomial/RootUniqueness.lean).

- **Frobenius limits and Teichmüller maps.** For a field of prime characteristic
  `p`, the inverse-Frobenius limit `Perfection K p` is a field without perfectness
  of `K`; this is not a root-adjoining extension or surjectivity onto `K`.
  For a reduced commutative ring of exponential characteristic `p`, the stock
  intersection of iterated Frobenius ranges is perfect and contains every perfect
  subring; for fields it is the largest perfect subfield. Exponential
  characteristic one is included; the `PerfectionMap` and universal-property
  interface uses prime characteristic. For a surjective map of commutative rings
  `f : R →+* κ`, with `κ` perfect of prime characteristic `p` and `R` complete
  along `ker f`, there is a unique multiplicative zero-and-one-preserving section,
  with inverse-Frobenius approximation modulo `(ker f)^(n+1)` for every `n`.
  Its image is `⋂ n, Set.range (fun r : R ↦ r^(p^n))`, including zero and
  `n = 0`, with no compatibility condition on root witnesses.
  It is a ring homomorphism if **`CharP R p`**. No field, locality or finite
  residue hypothesis is needed. See [section and core details](docs/Results.md#headline-results).
  For `p : ℕ` with `[Fact p.Prime]` and any `R : Type u` with `[CommRing R]`
  and `[CharP R p]`, [`WittVector.charZero`](AdicModules/RingTheory/WittVector.lean)
  supplies `CharZero (WittVector p R)`, without field, perfectness, finiteness,
  domain, reducedness or extra `Nontrivial` assumptions. The same module proves
  `WittVector.isUnit_iff_isUnit_coeff_zero`: a Witt vector is a unit exactly when
  its constant coefficient is a unit, with the field specialization
  `WittVector.isUnit_iff_coeff_zero_ne_zero`. It also proves
  `WittVector.isLocalRing_iff`: `IsLocalRing (WittVector p R) ↔ IsLocalRing R`,
  with the same prime-characteristic commutative-ring hypotheses.
  See the
  [Witt-vector API and uses](docs/Guide.md#characteristic-zero-of-witt-vectors).
  The [concrete Witt-vector models](AdicModulesTest/RingTheory/WittVector.lean)
  also give the nonzero nonunit `2` over `ZMod 2`, units and nonunits over the
  local nonfield `PowerSeries (ZMod 2)` with nonsquare `X`, and the nonlocal
  product `ZMod 2 × ZMod 2`.
  For a **reduced** commutative coefficient ring of prime characteristic `p`,
  [`WittVector.teichmuller_expansion_unique`](AdicModules/RingTheory/WittVector.lean)
  states that two digit sequences `a, b : ℕ → R` are equal if their partial sums
  `∑ i ∈ Finset.range (n + 1), teichmuller p (a i) * p^i` and the analogous
  sums for `b` both agree with the same Witt vector modulo `p^(n+1)` for every
  `n`. No perfectness, field, completeness or topology assumption is required.

- **Reducedness of Witt vectors.** For any prime `p` and commutative ring
  `R : Type u`, [`WittVector.isReduced_iff`](AdicModules/RingTheory/WittVector.lean)
  states `IsReduced (WittVector p R) ↔ IsReduced R`. No characteristic,
  nontriviality, domain, perfectness or completeness assumption is required.
  The clients at prime `2` include the mixed-characteristic reduced ring
  `ℤ × ZMod 2`, where `2` is a nonzero zero divisor; `ZMod 4`, with a nonzero
  square-zero Teichmüller lift of `2` and nonreduced Witt ring; and the zero ring
  `ZMod 1`, whose Witt ring is subsingleton and reduced.

- **Prime multiplication in Witt vectors.** For `p : ℕ` with `[Fact p.Prime]`
  and any `k : Type u` with `[CommRing k]` and `[CharP k p]`,
  [`WittVector.mul_p_eq_zero_iff_coeff_pow_eq_zero`](AdicModules/RingTheory/WittVector.lean)
  gives `x * (p : WittVector p k) = 0 ↔ ∀ n : ℕ, x.coeff n ^ p = 0`
  for every `x : WittVector p k`.

- **Prime-power multiplication in Witt vectors.** For `p : ℕ` with `[Fact p.Prime]`
  and any `k : Type u` with `[CommRing k]` and `[CharP k p]`,
  [`WittVector.mul_p_pow_eq_zero_iff_coeff_pow_eq_zero`](AdicModules/RingTheory/WittVector.lean)
  gives `x * (p : WittVector p k) ^ n = 0 ↔ ∀ i : ℕ, x.coeff i ^ (p ^ n) = 0`
  for every `x : WittVector p k` and every `n : ℕ`, including zero.
  [`WittVector.mul_p_eq_zero_iff_coeff_pow_eq_zero`](AdicModules/RingTheory/WittVector.lean)
  is its `n = 1` specialization. Moreover,
  [`WittVector.isRegular_p_iff_isReduced`](AdicModules/RingTheory/WittVector.lean)
  gives `IsRegular (p : WittVector p k) ↔ IsReduced k`.
  The kernel formula needs no reducedness assumption; reducedness is exactly
  the condition for injectivity of multiplication by `p`, not for characteristic
  zero. No field, perfectness, domain, finiteness or topology is required.
  See the [kernel and regularity uses](docs/Guide.md#prime-multiplication-and-reduced-coefficients).

- **Integer torsion in Witt vectors.** For prime `p` and any commutative ring
  `R : Type u` of characteristic `p`,
  [`WittVector.isTorsionFree_int_iff_isReduced`](AdicModules/RingTheory/WittVector/Torsion.lean)
  states `Module.IsTorsionFree ℤ (WittVector p R) ↔ IsReduced R` for the canonical
  integer action. Reduced non-domains are included; no perfectness or finiteness
  is required. See the [criterion and examples](docs/Guide.md#integer-torsion-in-witt-vectors).

- **Ideals and completeness of Witt vectors.** For prime `p` and any commutative
  ring `k` of characteristic `p`, `WittVector p k` is Hausdorff and complete
  for `(p)`. Membership in `(p)^n` means that the first `n` coefficients vanish
  and each remaining coefficient has a `p^n`-th root. For fixed `n`, the roots
  are independent; no perfectness, reducedness or field hypothesis is needed.
  The constant-coefficient kernel equals `(p)` exactly when Frobenius on `k`
  is surjective, and `(p)` is prime exactly when `k` is a domain with
  surjective Frobenius. Prime-field, product and polynomial examples
  distinguish these conditions; a zero prefix alone does not suffice over a
  nonperfect ring. See the
  [coefficient, ideal and completeness API](AdicModules/RingTheory/WittVector/Complete.lean)
  and its [examples](AdicModulesTest/RingTheory/WittVector/Complete.lean).

- **Domain criterion for Witt vectors.** For `p : ℕ` with `[Fact p.Prime]`
  and any `R : Type u` with `[CommRing R]`,
  [`WittVector.isDomain_iff`](AdicModules/RingTheory/WittVector/Domain.lean)
  gives `IsDomain (WittVector p R) ↔ IsDomain R ∧ CharP R p`.
  Domainhood and characteristic `p` of `R` are conclusions, not hypotheses.
  See the [imperfect polynomial, integer and zero-ring models](AdicModulesTest/RingTheory/WittVector/Domain.lean).

- **Discrete valuation criterion for Witt vectors.** For `p : ℕ` with
  `[Fact p.Prime]` and any `R : Type u` with `[CommRing R]`,
  [`WittVector.isDiscreteValuationRing_iff`](AdicModules/RingTheory/WittVector/DiscreteValuationRing.lean)
  equates the existence of `hD : IsDomain (WittVector p R)` satisfying
  `@IsDiscreteValuationRing (WittVector p R) inferInstance hD` with
  `IsField R ∧ CharP R p ∧ PerfectRing R p`.
  The domain proof is bound within the left-hand condition; field,
  characteristic and perfectness of `R` are conclusions, not hypotheses.

- **Witt Frobenius and perfect coefficients.** For a prime `p` and a commutative
  ring `R` with `CharP R p`,
  [`WittVector.frobenius_bijective_iff`](AdicModules/RingTheory/WittVector/Frobenius.lean)
  identifies bijectivity of canonical Witt Frobenius with `PerfectRing R p`.
  No field, domain or reducedness hypothesis is imposed. The
  [examples](AdicModulesTest/WittVector/Frobenius.lean) contrast the perfect
  non-domain `ZMod 2 × ZMod 2` with the nonperfect `DualNumber (ZMod 2)`.

- **Completeness of Witt vectors.** For prime `p` and any commutative ring `k`
  of characteristic `p`, `WittVector p k` is Hausdorff and complete for `(p)`.
  Membership in `(p)^n` means that the first `n` coefficients vanish and each
  remaining coefficient has a `p^n`-th root. For fixed `n`, the roots are
  independent; no perfectness, reducedness or field hypothesis is needed.
  A zero prefix alone does not suffice over a nonperfect ring. See the
  [coefficient and completeness API](AdicModules/RingTheory/WittVector/Complete.lean)
  and its [polynomial-coefficient examples](AdicModulesTest/RingTheory/WittVector/Complete.lean).

- **Principal units.** For a Henselian pair `(R, I)`, the natural `n`-th power
  map on the kernel of `Rˣ → (R ⧸ I)ˣ` is bijective whenever `n` is a unit in
  `R ⧸ I`, without a topology or positivity assumption on `n`.
  In a commutative ring complete along `I`, for prime `p`
  with `(p : R) ∈ I`, the same kernel has canonical `ℤ_[p]`-powers
  agreeing with integer powers and an explicitly supplied additive-form module.
  For an `I`-adic topology, powering is jointly continuous and uniquely
  characterized by continuous agreement with integer powers. See
  [principal-unit powers](AdicModules/Topology/Algebra/PrincipalUnits.lean).

- **Spans, pullbacks and closure.** In a `NonAssocRing`, additive cyclicity or a
  top singleton integer span implies surjective integer casts; nonsurjectivity
  makes every singleton span proper. Semilinear kernel pullbacks satisfy
  `comap f (map f N) = N ⊔ ker f` for additive commutative group sources,
  additive commutative monoid targets and surjective scalar homomorphisms. Over a semiring, on a module
  with a **given compatible topological additive-group structure** and continuous
  fixed-scalar maps, submodule closure is `⨅ i, ⨅ (_ : p i), N ⊔ U i` for an
  active zero-neighborhood basis. Separately, for an additive commutative monoid
  module over a semiring, a dense subsemiring and separately continuous addition,
  span set-closures agree assuming coefficient continuity **only at selected
  generators**. No Hausdorffness or global coefficient continuity is added;
  empty/zero generators give `closure {0}`. See [span and closure details](docs/Results.md#headline-results).

- **Comaximal ideals and density.** For commutative semirings and additive
  commutative monoid modules, `(I ⊓ J) • N = (I • N) ⊓ (J • N)` when
  `I ⊔ J = ⊤`; the finite-family formula includes the essential cap with `N`
  for an empty selection. Arbitrary semiring left ideals satisfy
  `J ⊔ I = ⊤ → J ⊔ I^n = ⊤` for every natural `n`, hence independent pairwise
  power guards. In a ring with a **supplied compatible additive-group topology**
  based on `I^n`, `Dense J ↔ J ⊔ I = ⊤`, without two-sidedness or multiplication
  continuity. For prime `p`, the usual p-adic norm topology has its ideal-power
  basis; integer spans of p-adic units are dense but every singleton integer
  span is proper. See [ideal and p-adic details](docs/Results.md#headline-results).

- **Finite Chinese remainders.** In a possibly noncommutative ring, a finite
  **index type**, **all-family two-sidedness** and pairwise comaximality give
  `(R ⧸ ⨅ i, I i) ≃+* ((i : ι) → R ⧸ I i)` with Mathlib's canonical forward
  map, a unique quotient class and the full representative coset, not a unique
  ring element. Independent powers include zero; the common-ring linear form
  and forward/inverse precision squares use the same data. This is not general
  module CRT for arbitrary left ideals. See [finite quotients](docs/FiniteQuotient.md).

- **Scalar-ideal quotients of algebras.** For a commutative semiring `R` and an
  `R`-algebra semiring `A`, `J • ⊤` has a two-sided ideal view in `A`.
  For a commutative ring `R` and a possibly noncommutative `R`-algebra ring `A`,
  the original submodule quotient `A ⧸ (J • ⊤)` carries ring and `R`-algebra
  structures retaining its quotient additive group and `R`-module action.
  The existing quotient algebra map agrees with the submodule projection;
  adic levels specialize to `J = I ^ n`. See the
  [quotient API and matrix example](docs/Guide.md#scalar-ideal-quotients-of-algebras).

- **Valuation-integer completeness.** Let `R` be a commutative ring and `K`
  a valued field with an `R`-algebra structure identifying `R` with its valuation
  integers. For **nonzero** `a : R` with **separated** powers of `(a)`,
  `IsAdicComplete (Ideal.span {a}) R ↔ CompleteSpace K`, for the **given
  valuation uniformity** on `K`. No topology on `R`, rank or norm is required;
  domain, valuation-ring and fraction-field properties follow from the integer
  identification, rather than being caller hypotheses. Field completeness
  implies adic completeness also for `a = 0`. See the
  [theorem](AdicModules/Valuation/Completeness.lean), [details](docs/Results.md#principal-adic-completeness-and-the-valued-fraction-field),
  [3-adic model](AdicModulesTest/FractionFieldCompletenessPadicClient.lean)
  and [power-series/Laurent-series model](AdicModulesTest/FractionFieldCompletenessSeriesClient.lean).

- **Valuation completions, localization and composites.** For a valuation
  domain, a **nonzero** generator and **separated** principal-adic filtration,
  the inverse limit agrees with the valuation integers of the completed fraction
  field; nonfield, faithful-flatness and spectrum laws additionally require the
  generator in the **maximal ideal**. Denominators **disjoint from the principal
  radical** give literal base-power images sandwiched between successive extended
  powers, not unconditional equality. Together with nonzero generator and
  separatedness this yields the localized-completion embedding and residue
  comparison; at a nonzero prime, separatedness supplies radical-disjointness.
  The completed valuation integers literally equal the residue-preimage composite
  of the completed localization and transported residue factor. No rank-one,
  discreteness or Noetherian premise is added. See [valuation hypotheses](docs/Guide.md#completion-and-valuation-hypotheses)
  and [localization/composites](docs/Guide.md#localization-and-literal-composites).

### Reduced-residue Teichmüller image

For a commutative ring `R`, prime `p` and ideal `I`, with `CharP (R ⧸ I) p`,
`IsAdicComplete I R` and **reduced** residue, `Perfection.teichmuller₀ p I` is
injective with image `⋂ n, Set.range (fun r : R ↦ r^(p^n))`, including zero and
`n = 0`. Roots exist independently at each depth; residue perfectness is not
required. For a **valuation domain**, **maximal** `I` and any specified fraction
field `K`, the composite with `algebraMap R K` has the analogous image in `K`,
without a topology on `K` or perfect/finite residue. See the
[ring-image details and imperfect-residue model](docs/Results.md#reduced-residue-teichmüller-image)
and [fraction-field laws](AdicModules/RingTheory/TeichmullerFractionField.lean).

## Imports and module map

Use the public root, or a narrower library leaf from the table:

```lean
import AdicModules
```

Related `AdicModulesTest` modules require separate imports and are not re-exported by
that root; some expose named concrete results, while the left-ideal, span and
fraction-field completeness models keep their calculations private. The [mathematical guide](docs/Guide.md)
provides detailed hypotheses, formulas and examples. The table below lists library
leaves and their related modules.

| Library leaf (prefix `AdicModules.`) | Related modules (prefix `AdicModulesTest.`) |
| --- | --- |
| [BoundedIdealPowerTorsion](AdicModules/BoundedIdealPowerTorsion.lean) | [BoundedIdealPowerTorsion](AdicModulesTest/BoundedIdealPowerTorsion.lean) |
| [Polynomial.Coprime](AdicModules/Polynomial/Coprime.lean) | [Polynomial.FactorizationUniqueness](AdicModulesTest/Polynomial/FactorizationUniqueness.lean) (monic coprimeness criterion and factor uniqueness) |
| [Polynomial.Hensel](AdicModules/Polynomial/Hensel.lean) | [Polynomial.Hensel](AdicModulesTest/Polynomial/Hensel.lean), [Polynomial.FactorizationUniqueness](AdicModulesTest/Polynomial/FactorizationUniqueness.lean) (nonlocal power series, zero ring and product-projection boundary) |
| [Polynomial.Evaluation](AdicModules/Polynomial/Evaluation.lean) | [Polynomial.Evaluation](AdicModulesTest/Polynomial/Evaluation.lean) (derivative application, nonunit 3-adic derivative and zero boundary) |
| [Polynomial.RootUniqueness](AdicModules/Polynomial/RootUniqueness.lean) | [Polynomial.RootUniqueness](AdicModulesTest/Polynomial/RootUniqueness.lean) |
| [RingTheory.Teichmuller](AdicModules/RingTheory/Teichmuller.lean) | [RingTheory.Teichmuller](AdicModulesTest/RingTheory/Teichmuller.lean) (usual normed 3-adic integers and perfect-field power series, with infinite residue fields) |
| [RingTheory.TeichmullerFractionField](AdicModules/RingTheory/TeichmullerFractionField.lean) | [RingTheory.TeichmullerFractionFieldModel](AdicModulesTest/RingTheory/TeichmullerFractionFieldModel.lean) (usual 3-adics; a power-series fraction field with imperfect infinite residue field) |
| [RingTheory.Perfection](AdicModules/RingTheory/Perfection.lean) | [RingTheory.TeichmullerCore](AdicModulesTest/RingTheory/TeichmullerCore.lean) (imperfect Laurent-series field, prime-field unit and zero boundaries) |
| [RingTheory.FrobeniusCore](AdicModules/RingTheory/FrobeniusCore.lean) | [RingTheory.FrobeniusCore](AdicModulesTest/RingTheory/FrobeniusCore.lean) (imperfect Laurent-series field, universal property, characteristic-one and reduced-product boundaries) |
| [RingTheory.WittVector](AdicModules/RingTheory/WittVector.lean) | [RingTheory.WittVector](AdicModulesTest/RingTheory/WittVector.lean) (nonzero casts of `3` over `ZMod 3` and `(ZMod 3)[X]`; reducedness over `ℤ × ZMod 2`, nonreduced `ZMod 4`, and the zero ring `ZMod 1`; injective multiplication by `3` over the reduced nonperfect `Polynomial (ZMod 3) × ZMod 3` with nonzero zero divisors; nonzero Teichmüller torsion killed by `3` and the coefficientwise kernel criterion over `TrivSqZeroExt (ZMod 3) (ZMod 3)`; the nonzero nonunit `2` over `ZMod 2`, units and nonunits over the local nonfield `PowerSeries (ZMod 2)` with nonsquare `X`, and the nonlocal product `ZMod 2 × ZMod 2`) |
| [RingTheory.WittVector.Complete](AdicModules/RingTheory/WittVector/Complete.lean) | [RingTheory.WittVector.Complete](AdicModulesTest/RingTheory/WittVector/Complete.lean) (prime-field, product and nonperfect polynomial coefficients, independent roots and zero precision; prime-field and nonperfect polynomial coefficients, independent roots and zero precision) |
| [RingTheory.WittVector.Domain](AdicModules/RingTheory/WittVector/Domain.lean) | [RingTheory.WittVector.Domain](AdicModulesTest/RingTheory/WittVector/Domain.lean) (imperfect polynomial domain, characteristic-zero integers and zero-ring boundary) |
| [RingTheory.WittVector.Torsion](AdicModules/RingTheory/WittVector/Torsion.lean) | [RingTheory.WittVector.Torsion](AdicModulesTest/RingTheory/WittVector/Torsion.lean) (reduced non-domain product and dual-number integer torsion) |
| [RingTheory.WittVector.Frobenius](AdicModules/RingTheory/WittVector/Frobenius.lean) | [WittVector.Frobenius](AdicModulesTest/WittVector/Frobenius.lean) (perfect non-domain product and nonperfect dual numbers) |
| [PrimaryComponent](AdicModules/PrimaryComponent.lean) | [PrimaryComponent](AdicModulesTest/PrimaryComponent.lean) |
| [AdicCompletion](AdicModules/AdicCompletion.lean) | [AdicCompletion](AdicModulesTest/AdicCompletion.lean) |
| [AdicCompletion.Functor](AdicModules/AdicCompletion/Functor.lean) | [AdicCompletion.Functor](AdicModulesTest/AdicCompletion/Functor.lean) (completed product inclusion and its nonzero integer boundary) |
| [AdicCompletion.Completeness](AdicModules/AdicCompletion/Completeness.lean) | [AdicCompletion.CompletenessTheorems](AdicModulesTest/AdicCompletion/CompletenessTheorems.lean) |
| [AdicCompletion.Endomorphism](AdicModules/AdicCompletion/Endomorphism.lean) | [IdentityCongruence](AdicModulesTest/IdentityCongruence.lean) (private nonscalar `ZMod 4` shear and criterion application) |
| [AdicCompletion.Kernel](AdicModules/AdicCompletion/Kernel.lean) | [AdicCompletionKernel](AdicModulesTest/AdicCompletionKernel.lean) (private integer `(2)` kernel calibration, degree-zero boundary, finite-generation recovery and separate fixed-power use) |
| [AdicCompletion.LinearMap](AdicModules/AdicCompletion/LinearMap.lean) | [AdicCompletion.LinearMap](AdicModulesTest/AdicCompletion/LinearMap.lean) (independent nonzero integer `(2)`-adic map from `ℕ →₀ ℤ`) |
| [AdicCompletion.Quotient](AdicModules/AdicCompletion/Quotient.lean) | [AdicCompletionQuotient](AdicModulesTest/AdicCompletionQuotient.lean) (integer `(2)` completion quotient, `ZMod 2`, inverse formulas and degree zero) |
| [AdicCompletion.RestrictScalars](AdicModules/AdicCompletion/RestrictScalars.lean) | [AdicCompletion.RestrictScalars](AdicModulesTest/AdicCompletion/RestrictScalars.lean) |
| [AdicCompletion.LocalRing](AdicModules/AdicCompletion/LocalRing.lean) | [AdicCompletion.LocalRing](AdicModulesTest/AdicCompletion/LocalRing.lean) |
| [AdicCompletion.PadicInt](AdicModules/AdicCompletion/PadicInt.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) |
| [AdicCompletion.PadicIntTopology](AdicModules/AdicCompletion/PadicIntTopology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (proper open mod-four kernel and its image) |
| [AdicCompletion.Pi](AdicModules/AdicCompletion/Pi.lean) (algebraic arbitrary-product equivalence for `I.FG`; naturality for every ideal) | [AdicCompletionPi](AdicModulesTest/AdicCompletionPi.lean) (full `ℕ → ZMod 4` model for `I = Ideal.span {2}`, a nonzero proper square-zero ideal; empty-product boundary) and [AdicCompletion.DependentPi](AdicModulesTest/AdicCompletion/DependentPi.lean) (private generic `Prop` contracts and a nonzero `ℕ → ℤ` model, not a universal bijectivity proof) |
| Separate completeness contract/model file | [AdicCompletion.Completeness](AdicModulesTest/AdicCompletion/Completeness.lean) (three proposition `#check`s and completeness/boundary models) |
| [AdicCompletion.Topology](AdicModules/AdicCompletion/Topology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (evaluation-kernel basis application) |
| [AdicCompletion.QuotientTorsion](AdicModules/AdicCompletion/QuotientTorsion.lean) | [ScalarTorsionSections](AdicModulesTest/ScalarTorsionSections.lean) |
| [AdicCompletion.TensorProduct](AdicModules/AdicCompletion/TensorProduct.lean) | [AdicCompletion.TensorProduct](AdicModulesTest/AdicCompletion/TensorProduct.lean) (finite-projective comparison and non-finite countable Finsupp injectivity) |
| [Algebra.Module.Int](AdicModules/Algebra/Module/Int.lean) | [Algebra.Module.Int](AdicModulesTest/Algebra/Module/Int.lean) |
| [LinearAlgebra.Pi](AdicModules/LinearAlgebra/Pi.lean) (finitely generated ideal action on dependent products and coordinatewise reduction kernel) | See the `AdicCompletion.DependentPi` models above |
| [LinearAlgebra.Span.Basic](AdicModules/LinearAlgebra/Span/Basic.lean) | [KernelPullback](AdicModulesTest/KernelPullback.lean) |
| [LinearAlgebra.TensorProduct.Quotient](AdicModules/LinearAlgebra/TensorProduct/Quotient.lean) | [LinearAlgebra.TensorProduct.Quotient](AdicModulesTest/LinearAlgebra/TensorProduct/Quotient.lean) |
| [RingTheory.Ideal.IsPrincipalPowQuotient](AdicModules/RingTheory/Ideal/IsPrincipalPowQuotient.lean) (representatives and inverse formulas) | [RingTheory.Ideal.IsPrincipalPowQuotient](AdicModulesTest/RingTheory/Ideal/IsPrincipalPowQuotient.lean) (nonzero chosen-generator class for `(5)` in `ℤ`) |
| [RingTheory.Ideal.Operations](AdicModules/RingTheory/Ideal/Operations.lean) | [RingTheory.Ideal.Operations.MatrixNat](AdicModulesTest/RingTheory/Ideal/Operations/MatrixNat.lean) (independent original calculations; additional private comaximal-powers application) |
| [RingTheory.Ideal.Quotient.Finite](AdicModules/RingTheory/Ideal/Quotient/Finite.lean) | [RingTheory.Ideal.Quotient.Finite](AdicModulesTest/RingTheory/Ideal/Quotient/Finite.lean) (integer quotient and boundary calculations), [RingTheory.Ideal.Quotient.FiniteEquivalence](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteEquivalence.lean) (equivalence client), [RingTheory.Ideal.Quotient.FinitePowers](AdicModulesTest/RingTheory/Ideal/Quotient/FinitePowers.lean) (powers-surjectivity client), [RingTheory.Ideal.Quotient.FiniteInverse](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteInverse.lean) (inverse and representatives client), [RingTheory.Ideal.Quotient.FiniteLinear](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteLinear.lean) (linear definition and integer client), [RingTheory.Ideal.Quotient.FiniteReduction](AdicModulesTest/RingTheory/Ideal/Quotient/FiniteReduction.lean) (precision-reduction client), [RingTheory.Ideal.Quotient.Matrix](AdicModulesTest/RingTheory/Ideal/Quotient/Matrix.lean) (two-sided matrix examples), [RingTheory.Ideal.Quotient.LeftIdeal](AdicModulesTest/RingTheory/Ideal/Quotient/LeftIdeal.lean) (left-ideal counterexample) |
| [RingTheory.Ideal.Quotient.SMulTop](AdicModules/RingTheory/Ideal/Quotient/SMulTop.lean) | [RingTheory.Ideal.Quotient.SMulTop](AdicModulesTest/RingTheory/Ideal/Quotient/SMulTop.lean) (noncommutative integer matrices at the bottom ideal, level one) |
| [Topology.Algebra.Ideal](AdicModules/Topology/Algebra/Ideal.lean) | [Topology.Algebra.Ideal.Int](AdicModulesTest/Topology/Algebra/Ideal/Int.lean), [Topology.Algebra.Ideal.Matrix](AdicModulesTest/Topology/Algebra/Ideal/Matrix.lean), [Topology.Algebra.Ideal.Boundary](AdicModulesTest/Topology/Algebra/Ideal/Boundary.lean) (independent original calculations; additional private density application in Int) |
| [Topology.Algebra.Module.AdicTopology](AdicModules/Topology/Algebra/Module/AdicTopology.lean) | [Topology.Algebra.Module.AdicTopology](AdicModulesTest/Topology/Algebra/Module/AdicTopology.lean) (integer-pair projection and quotient descent) |
| [Topology.Algebra.Submodule](AdicModules/Topology/Algebra/Submodule.lean) | [Topology.Algebra.SubmoduleClosure](AdicModulesTest/Topology/Algebra/SubmoduleClosure.lean) |
| [Topology.Algebra.PadicInt](AdicModules/Topology/Algebra/PadicInt.lean) | [Topology.Algebra.PadicInt](AdicModulesTest/Topology/Algebra/PadicInt.lean) |
| [Topology.Algebra.AdicTopology](AdicModules/Topology/Algebra/AdicTopology.lean) | [AdicCompletion.PadicInt](AdicModulesTest/AdicCompletion/PadicInt.lean) (module-to-mapped-ideal topology application) |
| [Topology.Algebra.AdicCompactness](AdicModules/Topology/Algebra/AdicCompactness.lean) | [Topology.Algebra.AdicCompactness](AdicModulesTest/Topology/Algebra/AdicCompactness.lean) (3-adic applications, complete discrete integers with infinite first quotient, and zero-ring/zeroth-power boundaries) |
| [Topology.Algebra.PrincipalUnits](AdicModules/Topology/Algebra/PrincipalUnits.lean) | [Topology.Algebra.PrincipalUnits](AdicModulesTest/Topology/Algebra/PrincipalUnits.lean) (`p`-adic integer, 2-torsion and `X`-adic power-series models); [Topology.Algebra.PrincipalUnits.Henselian](AdicModulesTest/Topology/Algebra/PrincipalUnits/Henselian.lean) (3-adic square roots, a `ZMod 9` nonunit-exponent boundary, bottom ideal and zero ring) |
| [Topology.Algebra.Module.Span](AdicModules/Topology/Algebra/Module/Span.lean) | [Topology.Algebra.Module.Span.Real](AdicModulesTest/Topology/Algebra/Module/Span/Real.lean), [Topology.Algebra.Module.Span.Discrete](AdicModulesTest/Topology/Algebra/Module/Span/Discrete.lean), [Topology.Algebra.Module.Span.PadicInt](AdicModulesTest/Topology/Algebra/Module/Span/PadicInt.lean), [Topology.Algebra.Module.Span.Boundary](AdicModulesTest/Topology/Algebra/Module/Span/Boundary.lean), [Topology.Algebra.Module.Span.Indiscrete](AdicModulesTest/Topology/Algebra/Module/Span/Indiscrete.lean) (independent original calculations; additional private comparison application in Real) |
| [Valuation.Completeness](AdicModules/Valuation/Completeness.lean) | [Valuation.Completeness](AdicModulesTest/Valuation/Completeness.lean) (5-adic and discrete-valuation examples), [FractionFieldCompletenessPadicClient](AdicModulesTest/FractionFieldCompletenessPadicClient.lean) (3-adic maximal-ideal valuation), [FractionFieldCompletenessSeriesClient](AdicModulesTest/FractionFieldCompletenessSeriesClient.lean) (power/Laurent series over any field, with no coefficient topology) |
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
options, thread-setting limits and cold-machine caveats, not machine-size guarantees.
The [historical API snapshot](docs/API.md) and [generation notes](docs/README.md)
cover 13 leaves, 28 modules and 103 display sites, not the current whole library.
Use the [results reference](docs/Results.md), [Guide](docs/Guide.md),
[primary components](docs/PrimaryComponent.md), the [finite-quotient guide](docs/FiniteQuotient.md)
and current Lean signatures.

## Credits, references and scope

Developed and reviewed by Formal Frontier AI agents; not human peer review,
source-author endorsement or complete source formalization. License: [Apache-2.0](LICENSE).
[Credits and provenance](docs/CREDITS.md) retain project/adaptation authorship
and authentic upstream notices. The [detailed credits](docs/Results.md#credits-references-and-scope)
retain the mathematical bibliography, Mathlib contributor credits and reuse of
[Group Theory](https://github.com/FormalFrontier/group-theory)'s scalar-torsion interface.

The endomorphism criterion uses the adic lifting and separation framework in
Mathlib's [Functoriality.lean](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/AdicCompletion/Functoriality.lean)
(Judith Ludwig and Christian Merten) and
[Basic.lean](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/RingTheory/AdicCompletion/Basic.lean)
(Kenny Lau, Judith Ludwig, Christian Merten and Jiedong Jiang), together with
Mathlib's [linear-equivalence and unit API](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Algebra/Module/Equiv/Basic.lean).

The Witt-vector unit criteria follow Mathlib's generic unit constructor and
field criterion in `RingTheory/WittVector/DiscreteValuationRing.lean`, by
Robert Y. Lewis, Heather Macbeth and Johan Commelin; the constant-coefficient
surjection is provided by Mathlib's `RingTheory/WittVector/Teichmuller.lean`.
The locality equivalence combines this surjection and the unit criterion with
Mathlib's local-ring criteria in `RingTheory/LocalRing/Basic.lean`, by Kenny Lau,
Chris Hughes and Mario Carneiro.
Mathematical references include Fesenko–Vostokov, *Local Fields and Their Extensions*,
and Fujiwara–Kato, *Foundations of Rigid Geometry I* ([arXiv](https://arxiv.org/abs/1308.4734v5)).
Dependencies: [Lean](https://lean-lang.org/) and [mathlib4](https://github.com/leanprover-community/mathlib4).
General nonseparated reduction, arbitrary-denominator localization, value-group
exact sequences, height/rational-rank additivity and whole-source coverage or
correspondence are outside the asserted scope. Ordinary builds and historical
API output are not complete transitive standard-axiom assurance or stored-proof replay.
