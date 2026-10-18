# Results and API detail

This reference expands the [concise overview](../README.md#headline-results).
The [Guide](Guide.md) gives usage and the complete current source map;
[CREDITS](CREDITS.md) records project and upstream provenance.
These are statements about the current library, not the historical API inventory.

## Headline results

- **Iterated ideal-power congruences.** For a commutative ring `R`, an ideal `I`,
  and a natural number `q` with `(q : R) ∈ I`, a congruence
  `x ≡ y [SMOD I ^ m]` at positive depth `m` implies
  `x ^ (q ^ n) ≡ y ^ (q ^ n) [SMOD I ^ (m + n)]` for every natural `n`.
  No primality, reducedness or completeness is required. See
  [`SModEq.pow_pow_add`](../AdicModules/LinearAlgebra/SModEq/Pow.lean).

- **Functoriality of adic module topologies.**
  For commutative rings `R`, `S`, a ring homomorphism `φ : R →+* S`,
  additive commutative groups `M`, `N` with `Module R M`, `Module S N`,
  and any `φ`-semilinear map `f`, let `I : Ideal R` and `J : Ideal S`.
  The powers `I ^ n • ⊤` form an indexed
  zero-neighborhood basis for Mathlib's `I.adicModuleTopology M`.
  The map `f` is continuous to `J.adicModuleTopology N` if `I.map φ ≤ J`.
  If `f` is surjective, the **reverse** containment `J ≤ I.map φ` gives
  openness; equality gives an `IsOpenQuotientMap`, hence descent of continuity
  along `f`. Ring and module universes are independent. No finite generation,
  Noetherianity, freeness, separation, completeness or surjectivity of `φ`
  is required. See the [module-topology API](../AdicModules/Topology/Algebra/Module/AdicTopology.lean)
  and the [integer-pair projection example](../AdicModulesTest/Topology/Algebra/Module/AdicTopology.lean),
  with proper nonzero precision-two neighborhoods and nondiscrete target.

- **Scalar-power torsion and completion coordinates.** For an
  additive commutative group `V`, subgroup `L`, and integer `ℓ` acting bijectively
  on `V`, the [comparison](../AdicModules/AdicCompletion/QuotientTorsion.lean)
  constructs a linear equivalence from stock compatible sections of the kernels
  of `ℓ ^ n` on `V / L` to `AdicCompletion (Ideal.span {ℓ}) L`. Its coordinate
  statements send `[v]` to `[ℓ ^ n • v]`; negative scalars require a degreewise
  sign twist of the natural-scalar quotient-torsion equivalence. The independent
  [rational model](../AdicModulesTest/ScalarTorsionSections.lean)
  constructs the nonzero family `[1 / (-2) ^ n]` and proves that its untwisted
  natural coordinates fail ordinary reduction from degree three to degree two,
  whereas the sign-normalized coordinates agree.

- **Natural powers of principal units over Henselian pairs.**
  For a commutative ring `R`, ideal `I`, `[HenselianRing R I]` and `n : ℕ`
  with `IsUnit (n : R ⧸ I)`,
  `HenselianRing.bijective_pow_principal_units` gives bijectivity of
  `fun u => u ^ n` on `(Units.map (Ideal.Quotient.mk I).toMonoidHom).ker`.
  Every unit reducing to one therefore has a unique `n`-th root reducing to
  one. No complete-ring, local-ring, domain, topology, nontriviality or
  positive-exponent assumption is needed. The [principal-unit module](../AdicModules/Topology/Algebra/PrincipalUnits.lean)
  also supplies `Ideal.mem_ker_unitsMap_quotient_iff`, identifying membership
  with `(u : R) - 1 ∈ I`. The [Henselian examples](../AdicModulesTest/Topology/Algebra/PrincipalUnits/Henselian.lean)
  exhibit the square root `-2` of `4` in `ℤ_[3]`, the Henselian pair
  `ZMod 9` at `(3)` where the nonunit exponent `3` gives noninjective cubing,
  the bottom ideal and the zero ring at exponent zero.

- **p-adic powers of principal units.**
  For a commutative ring `R`, an ideal `I` with `IsAdicComplete I R`, and a
  prime `p` with `(p : R) ∈ I`, the kernel of `Rˣ → (R ⧸ I)ˣ` has canonical
  `ℤ_[p]`-powers. They agree with all integer powers and define an explicitly
  supplied `ℤ_[p]`-module on the kernel's additive form. For an `I`-adic
  topology, powering is jointly continuous and characterized by continuous
  agreement with integer powers. See
  [principal-unit powers](../AdicModules/Topology/Algebra/PrincipalUnits.lean).

- **Field structure on an inverse-Frobenius limit.**
  The mathematical contract of the
  [perfection field interface](../AdicModules/RingTheory/Perfection.lean) is
  `Field (Perfection K p)` for any field `K` of prime characteristic `p`, with
  the existing commutative ring data unchanged. Perfectness of `K` is not a
  hypothesis. This inverse limit is not a field extension formed by adjoining
  roots. Its coefficient ring maps use Mathlib's `map_inv₀`, `map_div₀`,
  `map_zpow₀` and `map_pow`; inversion is not specified by definitional reduction.
  The [Laurent-series model](../AdicModulesTest/RingTheory/TeichmullerCore.lean)
  uses the infinite imperfect field `(ZMod 3)((T))` and a unit lifted from the
  prime field, alongside zero and perfect-prime-field boundaries. A field
  structure on the limit does not make the original field perfect or assert
  surjectivity of the zeroth coefficient onto an imperfect field.

- **Perfect cores from Frobenius ranges.**
  For a reduced commutative ring `R` of exponential characteristic `p`, the
  stock subring `B = ⨅ n : ℕ, (iterateFrobenius R p n).range` is perfect,
  and every `PerfectRing S p` subring `S` lies in `B`. For a field `K` of
  exponential characteristic `p`, the analogous stock field-range intersection
  is the largest perfect subfield. Exponential characteristic one is included.
  For prime `p` and `[CharP R p]`, the inclusion `B →+* R` is a
  `PerfectionMap`; Mathlib's associated equivalence has zeroth coefficient as
  its inverse's underlying value, and its `lift` gives the universal property.
  No perfectness of the ambient ring, domain, valuation, topology or completeness
  premise is added. See the [Frobenius-range module](../AdicModules/RingTheory/FrobeniusCore.lean)
  and the [imperfect Laurent-series and reduced-product models](../AdicModulesTest/RingTheory/FrobeniusCore.lean).
  This generalizes the algebraic perfect-core consequence of Fesenko–Vostokov,
  *Local Fields and Their Extensions*, I §7, (7.1), not its full
  residue-representative theorem. The proof reuses Kenny Lau's Mathlib
  perfection and Teichmüller constructions.

- **Perfect-residue Teichmüller sections.**
  For commutative rings `R`, `κ` in independent universes, a prime `p`,
  `[CharP κ p]`, `[PerfectRing κ p]`, a surjective ring map `f : R →+* κ`
  and `[IsAdicComplete (RingHom.ker f) R]`,
  `RingHom.teichmullerSection p f hf : κ →*₀ R` is a multiplicative section,
  unique among all multiplicative zero-and-one-preserving sections. Every lift of the
  `n`-fold inverse-Frobenius root of `a` has `p^n`-th power congruent to the
  section value modulo `(RingHom.ker f)^(n+1)`, including `n = 0` and `a = 0`.
  With **`[CharP R p]`**, the same function is a ring homomorphism; perfection
  of `R` is not required. No topology, continuity, field, locality, finite residue,
  Noetherianity, torsion-freeness or odd-prime assumption is imposed.
  The construction reuses Mathlib's ideal-based Teichmüller map and perfection
  lift, with an agreement law for quotient maps. See the
  [section module](../AdicModules/RingTheory/Teichmuller.lean) and
  [3-adic and perfect-field power-series models](../AdicModulesTest/RingTheory/Teichmuller.lean),
  including infinite residue fields and failure of additivity in mixed characteristic.
  `RingHom.range_teichmullerSection` identifies its image with
  `⋂ n : ℕ, Set.range (fun r : R ↦ r^(p^n))`, and
  `RingHom.mem_range_teichmullerSection_iff` expresses membership by separate
  root witnesses at every depth, including zero and `n = 0`. The proof combines
  the reduced-residue image theorem with Mathlib's perfection universal property
  and the section's uniqueness law. No Witt-vector characterization is asserted.

- **Polynomial-value association.**
  For a commutative ring `R`, an ideal `I ≤ Ideal.jacobson ⊥`, any polynomial
  `g : R[X]` and `a, b : R`, the statement
  `Polynomial.associated_eval_of_sub_mem_span_mul` says that
  `b - a ∈ Ideal.span {g.eval a} * I` implies `Associated (g.eval b) (g.eval a)`
  in `R`. There is no nonzero, domain, derivative-unit, Henselian or completeness
  premise. Taking `g = f.derivative` gives derivative stability up to a unit.
  See the [evaluation module](../AdicModules/Polynomial/Evaluation.lean) and the
  [3-adic example](../AdicModulesTest/Polynomial/Evaluation.lean), whose distinct
  arguments `1` and `10` have displacement `9` and initial derivative `3` for
  `f = X³`; that derivative is a nonunit. The example inputs and zero-derivative
  boundary are proved independently, and their association conclusions follow
  from the polynomial-value theorem.

- **Teichmüller images in fraction fields.**
  For a valuation domain `R` complete along a maximal ideal `I`, a prime `p`
  with `[CharP (R ⧸ I) p]`, and any specified fraction field `K`, the composite
  of `Perfection.teichmuller₀ p I` with `algebraMap R K` has image
  `⋂ n : ℕ, Set.range (fun y : K ↦ y ^ (p ^ n))`.
  Equivalently, membership means that a separate `p^n`-th root exists at every
  depth, including zero and `n = 0`. The universes of `R` and `K` are independent.
  No perfectness or finiteness of the residue field, topology on `K`, or
  compatible family of roots is assumed. See the
  [fraction-field image laws](../AdicModules/RingTheory/TeichmullerFractionField.lean)
  and their [3-adic and imperfect infinite-residue models](../AdicModulesTest/RingTheory/TeichmullerFractionFieldModel.lean).

- **Coprime Hensel factor lifting.**
  For any commutative ring `R`, any ideal `I` and `[IsAdicComplete I R]`,
  a monic `f : R[X]` whose reduction is a product of **coprime monic**
  `g₀, h₀ : (R ⧸ I)[X]` has monic coprime factors `g, h : R[X]` with
  `f = g * h` and reductions exactly `g₀, h₀`.
  `Polynomial.exists_monic_factorization_of_isAdicComplete` needs no
  nontriviality, proper-ideal, local-ring, Noetherian or finite-generation
  assumption. It does not assert uniqueness or supply a chosen factorization.
  See the [factor-lifting module](../AdicModules/Polynomial/Hensel.lean) and the
  [5-adic `X² - 6` example](../AdicModulesTest/Polynomial/Hensel.lean).

- **Roots and derivative-square error estimates over Henselian pairs.**
  For a commutative ring `R`, ideal `I` and stock `[HenselianRing R I]`,
  `HenselianRing.exists_root` lifts any root of an arbitrary `f : R[X]` modulo
  `I` whose derivative is a unit modulo `I`, preserving its congruence class.
  With `d = f.derivative.eval a`, the stronger error condition
  `f.eval a ∈ Ideal.span {d ^ 2} * I` gives a root `b` such that
  `b - a ∈ Ideal.span {d} * I` and `Associated (f.eval a) (d * (b - a))`, by
  `HenselianRing.exists_root_of_eval_mem_span_derivative_sq_mul`.
  In this estimate `d` may vanish, be a nonunit or be a zero divisor.
  Neither result requires monicity, locality, completeness or a domain; the
  zero ring is allowed. The local-ring root and prescribed-residue APIs,
  including `HenselianLocalRing.exists_root_residue`, are specializations.
  See the [Hensel module](../AdicModules/Polynomial/Hensel.lean).

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
  The [5-adic examples](../AdicModulesTest/Polynomial/Hensel.lean) independently prove
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
  See [bounded torsion](Guide.md#uniform-bounded-torsion) and
  [primary-component exactness](PrimaryComponent.md).

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
  See [completion hypotheses](Guide.md#completion-and-valuation-hypotheses)
  and [scalar restriction](Guide.md#restricting-scalars-in-adic-completions).

- **Integer adic completion and p-adic integers.**
  For `p : ℕ` with `[Fact p.Prime]`, `AdicCompletion.padicIntEquiv p` is the
  canonical `ℤ`-algebra equivalence
  `AdicCompletion (Ideal.span {(p : ℤ)}) ℤ ≃ₐ[ℤ] ℤ_[p]`.
  In namespace `AdicCompletion`, `toZModPow_padicIntEquiv` identifies every
  residue modulo `p ^ n` with `evalZModPow p n`, including `n = 0`;
  `toZModPow_comp_padicIntEquiv` gives the bundled ring-homomorphism identity.
  `evalZModPow_padicIntEquiv_symm` recovers every residue in the inverse direction.
  `padicIntEquiv_of` and `padicIntEquiv_symm_intCast` identify canonical integer
  images with p-adic integer casts in both directions. See the
  [algebraic comparison module](../AdicModules/AdicCompletion/PadicInt.lean).
  Its [topological refinement](../AdicModules/AdicCompletion/PadicIntTopology.lean),
  `AdicCompletion.isHomeomorph_padicIntEquiv p`, proves that **this same map** is a
  homeomorphism from the `J`-adic topology, where
  `J = (Ideal.span {(p : ℤ)}).map (algebraMap ℤ C)` and
  `C = AdicCompletion (Ideal.span {(p : ℤ)}) ℤ`, to the **usual norm topology**
  on `ℤ_[p]`. The domain topology is specified independently of the comparison;
  the target is not given a transported topology. The
  [mod-four example](../AdicModulesTest/AdicCompletion/PadicInt.lean) identifies the
  image of the proper open completion kernel with the proper open p-adic residue kernel.

- **Adic module topologies and evaluation neighborhoods.**
  For commutative rings `R`, `A`, an `R`-algebra `A` and any ideal `I : Ideal R`,
  `Ideal.adicModuleTopology_eq_adicTopology_map` identifies the adic topology on
  the underlying `R`-module with the ring topology for `I.map (algebraMap R A)`.
  This [generic bridge](../AdicModules/Topology/Algebra/AdicTopology.lean) needs
  **no finite-generation hypothesis**, with independent ring and algebra universes.
  For an arbitrary additive commutative group `M` with `Module R M`,
  `AdicCompletion.hasBasis_nhds_zero_ker_eval I M hI` gives the evaluation-kernel
  basis at zero in the adic module topology on `AdicCompletion I M`, assuming
  **only `hI : I.FG`**. The module need not be finite; all natural precisions,
  including zero, occur. See the
  [completion topology module](../AdicModules/AdicCompletion/Topology.lean).
  These compare existing adic constructions, not a new topology instance or a
  separate identification with a product topology.

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
  [unit detection and local-completion module](../AdicModules/AdicCompletion/LocalRing.lean).

<a id="linear-maps-from-an-adic-completion"></a>

- **Linear maps from an adic completion.**
  For any ideal `I` of a commutative ring `R` and `R`-modules `M`, `N` with
  additive commutative group structures, `[IsAdicComplete I N]` gives the
  canonical extension `AdicCompletion.extend I : (M →ₗ[R] N) →
  (AdicCompletion I M →ₗ[R] N)`. Its canonical-image, quotient, lift and
  naturality laws require no finite generation of `I`. If `I.FG`,
  `AdicCompletion.ext_of` gives uniqueness for a Hausdorff target
  `[IsHausdorff I N]`, without completeness. With `I.FG` and a complete target,
  `AdicCompletion.precompOfLinearEquiv I` is an `R`-linear equivalence
  `(AdicCompletion I M →ₗ[R] N) ≃ₗ[R] (M →ₗ[R] N)`, whose forward map is
  `LinearMap.lcomp R N (AdicCompletion.of I M)` and whose inverse is `extend I`.
  Ring, source and target universes are independent; no Noetherian, finite-module
  or projectivity hypothesis is imposed. See the
  [linear-map API](../AdicModules/AdicCompletion/LinearMap.lean) and its
  [nonzero integer free-module example](../AdicModulesTest/AdicCompletion/LinearMap.lean).

- **Adic completion of projective modules.**
  For a commutative ring `R`, an additive commutative group `M` with `Module R M`
  and `Module.Projective R M`, and any ideal `I`,
  `AdicCompletion.ofTensorProduct_injective_of_projective I M` proves injectivity
  of Mathlib's canonical **`AdicCompletion I R`-linear** comparison
  `AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M`.
  No finiteness assumption on `M` is needed for injectivity. With the additional
  hypothesis `Module.Finite R M`,
  `AdicCompletion.ofTensorProduct_bijective_of_finite_of_projective I M` proves
  bijectivity, and `AdicCompletion.ofTensorProductEquivOfFiniteProjective I M`
  gives an **`AdicCompletion I R`-linear** equivalence
  `AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M`.
  Its underlying linear map is `AdicCompletion.ofTensorProduct I M`; its
  characteristic lemmas give `a ⊗ₜ m ↦ a • AdicCompletion.of I M m` and
  `AdicCompletion.of I M m ↦ 1 ⊗ₜ m` for the inverse. Ring and module universes
  are independent; no Noetherian or finitely generated ideal hypothesis is needed.
  The separate `ofTensorProductEquivOfFiniteProjective_eq_ofFiniteNoetherian`
  lemma identifies it with Mathlib's Noetherian equivalence where both apply:
  over a Noetherian ring, with the ring and module in the same universe.
  The [integer models](../AdicModulesTest/AdicCompletion/TensorProduct.lean) retain
  the finite rank-two canonical-map, pure-tensor and inverse identities and the
  rank-zero boundary. They also include a projective, non-finite countable Finsupp
  module `ℕ →₀ ℤ` with a nonzero canonical tensor and completion image, and apply
  injectivity to that same module. See the
  [tensor comparison module](../AdicModules/AdicCompletion/TensorProduct.lean).
- **Adic completion of finite Noetherian modules.**
  For a commutative Noetherian ring `R`, a finite `R`-module `M` and any ideal `I`,
  `AdicCompletion.ofTensorProduct_bijective I M` states bijectivity of the canonical
  completed-ring-linear tensor comparison, with independent ring and module universes.
  Its common-universe bridge identifies `LinearEquiv.ofBijective` of that same map with
  Mathlib's finite-Noetherian equivalence. See the
  [tensor comparison module](../AdicModules/AdicCompletion/TensorProduct.lean) and the
  [lifted residue-module model](../AdicModulesTest/AdicCompletion/FiniteNoetherian.lean).

- **Naturality of quotient–tensor comparison.**
  For any commutative ring `R`, ideals `I ≤ J`, additive commutative groups
  `M`, `N` with `R`-module structures and any `R`-linear map `f : M →ₗ[R] N`,
  `TensorProduct.quotTensorEquivQuotSMul_naturality` proves that the canonical
  quotient–tensor equivalences commute with coefficient reduction tensor `f`
  and the induced module quotient map. Ring and module universes are independent;
  no finite generation, freeness, flatness, Noetherian or nonzero premise is needed.
  For principal ideals, `quotTensorEquivQuotSMul_span_singleton` identifies the
  equivalence with the inverse of Mathlib's `QuotSMulTop.equivQuotTensor`, after
  representative-preserving quotient transport. See the
  [quotient–tensor module](../AdicModules/LinearAlgebra/TensorProduct/Quotient.lean)
  and its [nonzero integer reduction example](../AdicModulesTest/LinearAlgebra/TensorProduct/Quotient.lean).

- **Adic completion of finitely presented modules.**
  For any ideal `I` of a commutative ring `R`, assume induced/intrinsic cofinality
  on all finitely generated submodules of finite free modules:
  `hcofinal : ∀ n (K : Submodule R (Fin n → R)), K.FG →
  ∀ k, ∃ l, K ⊓ (I ^ l • ⊤) ≤ I ^ k • K`.
  For any finitely presented `R`-module `M`,
  `AdicCompletion.ofTensorProductEquivOfFinitePresentation I M hcofinal` packages
  the canonical comparison as an `AdicCompletion I R`-linear equivalence
  `AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M`.
  Ring and module universes are independent. No finite-generation hypothesis on
  `I`, Noetherianity, projectivity or flatness is required. The pure-tensor,
  inverse-on-canonical-element and uniqueness identities identify this equivalence
  with the finite-projective and Mathlib finite-Noetherian comparisons where both
  apply. Artin–Rees supplies the cofinality hypothesis over a Noetherian ring.
  See the [finite-presentation comparison module](../AdicModules/AdicCompletion/FinitePresentation.lean),
  which reuses the canonical comparisons of Judith Ludwig and Christian Merten
  in Mathlib, and the [integer residue module](../AdicModulesTest/AdicCompletion/FinitePresentation.lean).

- **Integer singleton spans in unital rings.**
  For a `NonAssocRing R`, additive cyclicity or a top singleton integer span
  implies surjectivity of `ℤ → R`. Nonsurjective casts therefore make **every**
  singleton integer span proper, using the canonical additive-group integer
  action. No multiplication associativity, commutativity, characteristic-zero,
  nontriviality or topology premise is needed. Properness of one span does not
  imply nonsurjective casts: `(2)` is proper in `ℤ`. See the
  [integer-span guide](Guide.md#integer-singleton-spans-in-unital-rings),
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
  does not construct a topology. See the [closure guide](Guide.md#submodule-closure-from-a-neighborhood-basis).

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
  [ideal operations module](../AdicModules/RingTheory/Ideal/Operations.lean).

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
  continuity is assumed. See [comaximal powers](Guide.md#comaximal-powers-of-left-ideals),
  [density](Guide.md#left-ideal-density-and-integer-powers-topologies),
  [integer/matrix models](Guide.md#matrix-left-ideal-models) and
  [boundary models](Guide.md#ideal-power-boundary-models).

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
  completion or general module CRT. See the [finite-quotient guide](FiniteQuotient.md)
  for formulas, API names, integer examples and the arbitrary-left-ideal boundary.

- **P-adic neighborhood bases and proper dense integer spans.**
  For prime `p`, powers generated by `p ^ n` form a zero-neighborhood basis in
  the usual norm topology on `ℤ_[p]`, including `n = 0`.
  `PadicInt.isAdic_span_p p` identifies this norm topology with the adic topology
  for `Ideal.span {(p : ℤ_[p])}`. Restriction to `ℤ`
  retains **all p-adic multiples**; linearity for self/integer scalars uses no
  new global instances. In any ring with dense integer casts and continuous
  fixed-ring-scalar multiplication, the integer span of a unit is dense.
  Thus p-adic units and integer generators not divisible by `p` give dense
  spans, while every integer generator, even `0` and `±1`, has proper span.
  In `ℤ_[2]`, the integer span of `3` is proper and dense, excludes `1`, and
  sums to top with every restricted ideal generated by `2 ^ n`; it is not the
  self-scalar ideal of the unit `3`. See the [p-adic guide](Guide.md#p-adic-neighborhood-bases-and-integer-spans).

- **Adic completeness of valuation integers.**
  If `V` is the integer ring of a field `K` complete for its **valuation
  uniformity**, then `Valuation.Integers.isAdicComplete_span_singleton` gives
  `IsAdicComplete (Ideal.span {a}) V` whenever the powers of `(a)` are separated.
  This includes `a = 0`, with no rank, discreteness, Noetherianity, finite-residue
  or local-compactness hypothesis. No topology on `V` is assumed. See the
  [completeness module](../AdicModules/Valuation/Completeness.lean) and its
  [5-adic and discrete-valuation examples](../AdicModulesTest/Valuation/Completeness.lean).
  For the converse at a nonzero generator, see the
  [equivalence and models](#principal-adic-completeness-and-the-valued-fraction-field).

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
  discreteness or Noetherian premise is added. See [valuation hypotheses](Guide.md#completion-and-valuation-hypotheses).

- **Localization in one completed fraction field.**
  Denominators disjoint from the radical of `(a)` give literal base-power images
  as `V`-submodules, sandwiched between successive extended-ideal powers, not
  unconditionally equal to those powers. This filtration defines the localized
  topology; principal-adic separatedness gives separation. With `a ≠ 0`, those
  denominator and separatedness hypotheses give an embedding of the localized
  completion into the common completed field, a valuation-subring description
  and a residue-field comparison. At a nonzero prime, separatedness supplies
  radical-disjointness; the quotient valuation subring retains these premises.
  See the [localization guide](Guide.md#localization-and-literal-composites).

- **Literal composite valuations.**
  `ValuationSubring.composite` is a residue preimage; localization at its
  distinguished prime and quotient recover the factors. The completed valuation
  integers above equal the composite of the completed localization and the
  transported residue factor **literally**, not by a new notion of completion.
  See [composites](Guide.md#localization-and-literal-composites).

- **Closure of spans over a dense subsemiring.**
  For a semiring `R`, additive commutative monoid `M` with `Module R M`,
  independent universes/topologies, dense `A : Subsemiring R`, separately
  continuous addition on `M` and continuity of `r ↦ r • m` **only for `m ∈ E`**,
  `Submodule.closure_span_eq_of_dense_subsemiring` equates the set closures of
  `Submodule.span A E` and `Submodule.span R E` for the same canonical action.
  No additive group, joint addition, global coefficient continuity,
  `ContinuousSMul`, `T1`, nonempty or finite generating set is required.
  For empty/zero generators the closure is `closure {0}`, not necessarily `{0}`.
  See the [span-comparison guide](Guide.md#closure-of-spans-over-a-dense-subsemiring)
  for real, discrete, mixed, p-adic and indiscrete examples and counterexamples.

## Precompleteness and adic completeness

Let `R` be a commutative ring and let `M` and `N` be `R`-modules with additive
commutative group structures. Their type universes may be independent. The
[completeness API](../AdicModules/AdicCompletion/Completeness.lean) uses the stock
predicates `IsPrecomplete` and `IsAdicComplete`.

- **Sums of ideals.** `IsPrecomplete.sup` says that precompleteness of `M` for
  arbitrary ideals `I` and `J` implies precompleteness for `I ⊔ J`.
  `IsPrecomplete.finset_sup` extends this to any `s : Finset ι` and family
  `K : ι → Ideal R`: precompleteness for each `K i` with `i ∈ s` implies
  precompleteness for `s.sup K`. The index type and its universe are arbitrary;
  no finiteness of the index type or finite generation of the ideals is needed.
- **Surjective images.** For any ideal `I`, `IsPrecomplete.of_surjective`
  transfers precompleteness from `M` to `N` along a surjective `R`-linear map
  `f : M →ₗ[R] N`, without Hausdorffness of either module. Reduction
  `ℤ₂ → ℤ/4ℤ` along `(2) ⊆ ℤ` is a nontrivial example.
- **Separated quotient.** If `M` is `I`-precomplete, then
  `Hausdorffification I M` is `I`-adically complete. This follows from source
  precompleteness, with no Hausdorff assumption on `M`.
- **Principal ideals.** The named theorem `IsAdicComplete.span_singleton`
  gives `IsAdicComplete (Ideal.span {a}) M` from `a ∈ I` and
  `[IsAdicComplete I M]`. It is not a typeclass instance. The ideal `I` is
  arbitrary: no finite-generation, Noetherian, domain or nontriviality
  assumption is added. Adic Hausdorffness of the source is already included
  in `IsAdicComplete I M`, rather than a separate extra hypothesis.

- **Finite sets of generators.** `IsPrecomplete.span_finset` gives
  `IsPrecomplete (Ideal.span (s : Set R)) M` from precompleteness for each
  `Ideal.span {a}`, with `a ∈ s`. It requires no Hausdorffness.
  Under `[IsHausdorff (Ideal.span (s : Set R)) M]`,
  `isAdicComplete_span_finset_iff` identifies completeness for the generated
  ideal with completeness for each of these principal ideals. No finite
  generation of the module, Noetherianity or nonemptiness is needed.

The precompleteness and separated-quotient statements likewise require neither
finite generation of `I` nor Noetherianity. For a finite subset `t : Set R`,
completeness for each principal ideal generated by a member of `t` therefore
implies completeness of `Hausdorffification (Ideal.span t) M` for `Ideal.span t`,
without assuming Hausdorffness of `M`.

## Principal-adic completeness and the valued fraction field

Import [`AdicModules.Valuation.Completeness`](../AdicModules/Valuation/Completeness.lean)
or the public root. Let `R` be a commutative ring, `K` a field with an
`R`-algebra structure, and `Γ₀` a linearly ordered commutative group with zero.
For a specified `[hv : Valued K Γ₀]`, `hR : hv.v.Integers R` says that the
algebra map is injective and its image is exactly the elements of valuation at
most one. For a nonzero `a : R` whose principal-ideal powers are separated,
`Valuation.Integers.isAdicComplete_span_singleton_iff` has the signature:

```lean
{R : Type u} {K : Type v} {Γ₀ : Type w}
[CommRing R] [Field K] [Algebra R K]
[LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]
(hR : hv.v.Integers R) {a : R} (ha0 : a ≠ 0)
[IsHausdorff (Ideal.span {a}) R] :
IsAdicComplete (Ideal.span {a}) R ↔ CompleteSpace K
```

The three universes are independent. In particular, `CompleteSpace K` is a
conclusion of the adic-to-field direction, not a caller hypothesis. The domain,
valuation-ring and fraction-field structures follow from `hR`; callers do not
supply them separately. No topology on `R`, rank, discreteness, normed-field
structure, Noetherianity, finite or perfect residue field, characteristic,
local compactness or additional cofinality assumption is required.
`CompleteSpace K` always refers to the uniformity of the supplied `hv`, not to
a newly chosen norm or a different field structure. The proof compares it with
the canonical valuation through identity-on-elements uniform equivalences.

The nonzero hypothesis is essential to this equivalence: the zero ideal is
adically complete even when the ambient field is incomplete. The earlier
`Valuation.Integers.isAdicComplete_span_singleton` retains the field-to-adic
implication for `a = 0`. Separation excludes the unit-ideal filtration on a
nontrivial ring. Adic completeness here is the algebraic predicate for the
powers of `(a)`, not an assumed completeness of a separately chosen topology
on `R`. In the converse proof, the principal-adic topology comparison makes the
valuation integers complete; their image is a complete neighborhood of zero
in `K`, so the valued field is complete.

### 3-adic and series models

The two separately imported model modules retain the usual field operations
and integer embeddings. Their valuation-integer identifications, nonzero
separated generators and field-completeness inputs are established using
Mathlib independently of the equivalence.

- The [3-adic module](../AdicModulesTest/FractionFieldCompletenessPadicClient.lean)
  uses `ℤ_[3] → ℚ_[3]` and the valuation associated to the height-one maximal
  ideal of `ℤ_[3]`. That ideal is `(3)`, and the value of `3` is
  `WithZero.exp (-1 : ℤ)`. Mathlib's maximal-adic completeness supplies
  `IsAdicComplete (Ideal.span {(3 : ℤ_[3])}) ℤ_[3]`. Independently,
  completeness for this specified valuation follows from the usual 3-adic norm
  via an identity-on-elements uniform equivalence, preserving the integer
  embedding. The adic-to-field implication recovers completeness for the same
  maximal-ideal valuation, not merely for an unspecified uniformity.

- The [power-series/Laurent-series module](../AdicModulesTest/FractionFieldCompletenessSeriesClient.lean)
  works over **any field `κ`**, with no topology or completeness assumption on
  `κ`. It keeps Mathlib's Hahn-series embedding `κ[[X]] → κ((X))` and identifies
  the power-series maximal-ideal valuation with the usual `X`-adic valuation
  on Laurent series. Mathlib's coefficientwise construction supplies valued
  Laurent-series completeness independently. The field-to-adic theorem gives
  power-series completeness at `(X)` (also its maximal ideal), and the converse
  recovers completeness for that same valuation. This last application is a
  compatibility check, not another independent construction of field completeness.
  The coefficient in degree `-1` proves that `X⁻¹` is outside the power-series
  image and is not a valuation integer.

These model declarations are private calculations, not additional public API
names. The [5-adic and discrete-valuation examples](../AdicModulesTest/Valuation/Completeness.lean)
also retain the zero-generator boundary for the field-to-adic implication.

## Reduced-residue Teichmüller image

For a commutative ring `R`, a prime `p` and an ideal `I` with
`[CharP (R ⧸ I) p]`, `[IsAdicComplete I R]` and `[IsReduced (R ⧸ I)]`,
`Perfection.teichmuller₀ p I` is injective, and its image is exactly
`⋂ n : ℕ, Set.range (fun r : R ↦ r ^ (p ^ n))`. This includes zero and
`n = 0`; the roots may be chosen independently at each degree. Reducedness
forces their residue classes to be compatible, without requiring residue
Frobenius to be surjective. These are the adic-ring forms of
Fesenko–Vostokov, I §7, (7.1), using Kenny Lau's Mathlib perfection and
Teichmüller construction, not an ambient-field or integrality characterization.
The [imperfect-residue model](../AdicModulesTest/RingTheory/TeichmullerCore.lean)
uses `((ZMod 3)((T)))[[X]]` along its nonzero ideal `(X)`, distinguishes the
images of two and zero, and shows that the constant Laurent monomial `T`
is outside the image because it has no cube root.

## Credits, references and scope

Developed and reviewed by Formal Frontier AI agents; this is not human peer
review, source-author endorsement or complete formalization of a selected source.
The project uses [Apache-2.0](../LICENSE). [Credits and provenance](CREDITS.md)
retain project authorship, upstream author notices, stock-API reuse and the full
mathematical bibliography, including Kenny Lau and Patrick Massot's CRT credit.
The tensor comparison reuses Mathlib's adic-completion API by Judith Ludwig and
Christian Merten, including naturality, finite-module surjectivity, finite-product
bijectivity and the Noetherian comparison; the projective splitting API by Kevin
Buzzard and Antoine Labelle; and the tensor/Finsupp equivalence by Johannes Hölzl
and Antoine Chambert-Loir.
The principal-power quotient representative formulas use Yakov Pechersky's
Mathlib linear equivalence and its plain equivalence wrapper.

The valuation-integers equivalence extends the completeness bridge motivated
by Fesenko–Vostokov, II §1, Corollary 1; it is not a factor-lifting theorem.
Its complete-neighborhood argument generalizes Mathlib's right-uniform group
completeness proof by Patrick Massot and Johannes Hölzl in
`Mathlib.Topology.Algebra.IsUniformGroup.Basic`. The authentic upstream
copyright, license and author notice is retained with that adapted argument in
the [completeness module](../AdicModules/Valuation/Completeness.lean).
The proof also uses Mathlib's valuation-integers and `WithVal` interfaces and
this library's principal-adic topology and uniform-inducing fraction-field map;
[CREDITS](CREDITS.md) records their contributors.

The 3-adic model reuses Mathlib's p-adic work by Robert Y. Lewis, Mario Carneiro
and Johan Commelin, valuation and DVR APIs by Kenny Lau and María Inés de
Frutos-Fernández, and normed-valued comparison by María Inés de
Frutos-Fernández and Filippo A. E. Nuccio. The series model reuses Mathlib's
power-series, Laurent-series and discrete-valuation identifications and
coefficientwise completeness, particularly the work of Aaron Anderson,
María Inés de Frutos-Fernández and Filippo A. E. Nuccio. Both use Mathlib's
uniform-space completeness infrastructure; their module references give the
corresponding formalization credits. No upstream notices are replaced.

The Teichmüller sections follow the perfect-residue and equal-characteristic
corollaries of I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*,
second edition (2002), I §7, (7.3). The construction and approximation proofs reuse
Kenny Lau's Mathlib Teichmüller and perfection APIs. The field interface for
perfection also uses Mathlib's `Field.ofIsUnitOrEqZero` and unit-mapping
constructions, retaining the original perfection ring data.

The coprime Hensel theorem follows the factor-lifting form in I. B. Fesenko and
S. V. Vostokov, *Local Fields and Their Extensions*, second edition (2002), II, §1,
Corollary 1, generalized to adically complete rings. Its proof assembles Andrew Yang's
Mathlib universal coprime factorization ring and the formally smooth adic lifting
API of Judith Ludwig and Christian Merten.

The local-completion results use Mathlib's canonical completion and algebraic
projections (Judith Ludwig and Christian Merten), positive-power quotient-unit
lifting, `IsLocalHom`/`isUnit_map_iff`, `Ideal.mem_jacobson_bot` and
`RingHom.domain_isLocalRing`. The
[local-completion module](../AdicModules/AdicCompletion/LocalRing.lean) records
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

For imports and the complete current source map, see the [Guide](Guide.md#module-map).
