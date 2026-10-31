# COUNTABLY-RECOGNIZABLE-CLASSES-OF-GROUPS-WITH-RESTRICTED-CONJUGACY-CLASSES-A-Formalization-in-Lean


## FC-groups: Lemma 3.1 in Lean 4

Formalization of Lemma 3.1 from de Giovanni & Trombetti, *Countably recognizable classes of groups with restricted conjugacy classes*, Int. J. Group Theory 7 (2018), 5–16.

**Lemma 3.1.** For every group $G$, countable subgroup $X$ and $n \ge 0$, there is a countable subgroup $H \ge X$ with $H \cap FC_n(G) = FC_n(H)$.

### Definitions
- `fcCenter G`: the FC-centre of `G`.
- `fcSeriesAux G n`: auxiliary recursion for the series (each term with its normality proof).
- `fcSeries G n`: the upper FC-central series, `FC_n(G)`.
- `FCGood G n H`: `FC_n(H) ⊆ FC_n(G)`.

### Instances
- `fcCenter_normal`: `FC(G)` is normal.
- `fcSeries_normal`: `FC_n(G)` is normal.

### Lemmas
- `mem_fcCenter`: `x ∈ FC(G)` iff the conjugacy class of `x` is finite.
- `fcSeries_zero`: `FC_0(G) = 1`.
- `mem_fcSeries_succ`: `x ∈ FC_{n+1}(G)` iff `x FC_n(G) ∈ FC(G/FC_n(G))`.
- `exists_conj_seq_of_not_mem_fcSeries_succ`: if `a ∉ FC_{n+1}(G)`, there are infinitely many conjugates of `a` in distinct cosets of `FC_n(G)`.
- `countable_inv`: `S` countable implies `S⁻¹` countable.
- `countable_closure'`: `S` countable implies `⟨S⟩` countable.
- `countable_iSup`: a countable join of countable subgroups is countable.
- `fcCenter_of_surjective`: surjective homomorphisms preserve the FC-centre.
- `fcCenter_of_injective`: if `f` is injective and `f a ∈ FC(B)`, then `a ∈ FC(A)`.
- `fcSeries_comap_le`: if `f` is injective, `f⁻¹(FC_n(B)) ≤ FC_n(A)`; for subgroups, `Y ∩ FC_n(G) ≤ FC_n(Y)`.

## Main theorem
- `exists_countable_fcSeries` (Lemma 3.1): for countable `X ≤ G`, there is a countable `H ≥ X` with `FC_n(H) ⊆ FC_n(G)`. Together with `fcSeries_comap_le` this gives `H ∩ FC_n(G) = FC_n(H)`.
  
## Lemma 3.3 in Lean 4

Formalization of Lemma 3.3 from de Giovanni & Trombetti: a countable union of subgroup-closed, countably recognizable group classes is countably recognizable.

**Lemma 3.3.** Let $(\mathfrak{X}_n)_{n}$ be a countable collection of subgroup-closed, countably recognizable group classes. Then $\mathfrak{X} = \bigcup_n \mathfrak{X}_n$ is countably recognizable.

### Definitions
- `GroupProperty`: a class of groups, viewed as a predicate on groups.
- `IsoClosed X`: `X` is invariant under isomorphism.
- `SubgroupClosed X`: every subgroup of an `X`-group is an `X`-group.
- `CountablyRecognizable X`: `G ∈ X` whenever all countable subgroups of `G` are in `X`.

### Lemmas
- `SubgroupClosed.of_le`: if `H ≤ K` and `K ∈ X`, then `H ∈ X` (for `X` subgroup- and iso-closed).
- `countable_inv`: `S` countable implies `S⁻¹` countable.
- `countable_closure`: `S` countable implies `⟨S⟩` countable (as a set).
- `countable_closure'`: `S` countable implies `⟨S⟩` countable (as a type).
- `countable_iSup`: a countable join of countable subgroups is countable.

### Main theorem
- `countablyRecognizable_iUnion` (Lemma 3.3): the union of countably many iso-closed, subgroup-closed, countably recognizable classes is countably recognizable.


## Theorem 3.2 in Lean 4

**Theorem 3.2.** For each positive integer $n$, the class of $FC$-nilpotent groups of class at most $n$ is countably recognizable. In Lean it is proved for every `n : ℕ`, including `n = 0`.

### Setup
- `universe u v`: universe levels.
- `variable {G : Type u} [Group G]`: default group used in the lemmas without their own binders.

### Abbreviations
- `GroupProperty`: a class of groups, viewed as a predicate on groups.

### Definitions
- `CountablyRecognizable X`: a group `G` satisfies `X` whenever all its countable subgroups do.
- `fcCenter G`: the FC-centre of `G`.
- `fcSeriesAux G n`: auxiliary recursion for the series (each term bundled with its normality proof).
- `fcSeries G n`: the upper FC-central series, `FC_n(G)`.
- `IsFCNilpotentOfClassLE n G`: `G` is FC-nilpotent of class at most `n`, i.e. `FC_n(G) = G`.
- `FCGood G n H`: `FC_n(H) ⊆ FC_n(G)`.

### Instances
- `fcCenter_normal`: `FC(G)` is normal.
- `fcSeries_normal`: `FC_n(G)` is normal.

### Lemmas
- `mem_fcCenter`: `x ∈ FC(G)` iff the conjugacy class of `x` is finite.
- `fcSeries_zero` (`@[simp]`): `FC_0(G) = 1`.
- `mem_fcSeries_succ`: `x ∈ FC_{n+1}(G)` iff `x FC_n(G) ∈ FC(G/FC_n(G))`.
- `exists_conj_seq_of_not_mem_fcSeries_succ`: if `a ∉ FC_{n+1}(G)`, there is a sequence of conjugates of `a` lying in pairwise distinct cosets of `FC_n(G)`.
- `countable_inv`: `S` countable implies `S⁻¹` countable.
- `countable_closure'`: `S` countable implies `⟨S⟩` countable.
- `countable_iSup`: a countable join of countable subgroups is countable.
- `fcCenter_of_surjective`: if `f : A →* B` is surjective and `a ∈ FC(A)`, then `f a ∈ FC(B)`.
- `fcCenter_of_injective`: if `f : A →* B` is injective and `f a ∈ FC(B)`, then `a ∈ FC(A)`.
- `fcSeries_comap_le`: if `f : A →* B` is injective, then `f⁻¹(FC_n(B)) ≤ FC_n(A)`. For subgroups, `Y ∩ FC_n(G) ≤ FC_n(Y)`.

### theorems
- `exists_countable_fcSeries` (Lemma 3.1): for a countable `X ≤ G`, there is a countable `H ≥ X` with `FC_n(H) ⊆ FC_n(G)`. Together with `fcSeries_comap_le` this gives `H ∩ FC_n(G) = FC_n(H)`.
  
### Main theorem
- `isFCNilpotentOfClassLE_countablyRecognizable` (Theorem 3.2): `CountablyRecognizable (IsFCNilpotentOfClassLE n)` for every `n`.

## Corollary 3.4 in Lean 4

**Corollary 3.4.** The class of FC-nilpotent groups is countably recognizable.

### Definitions

* `GroupProperty`: a class of groups, viewed as a predicate on groups.
* `CountablyRecognizable X`: `G ∈ X` whenever all countable subgroups of `G` are in `X`.
* `IsoClosed X`: `X` is invariant under isomorphism.
* `SubgroupClosed X`: every subgroup of an `X`-group is an `X`-group.
* `fcCenter G`: the FC-centre of `G`, i.e. the subgroup of elements with finitely many conjugates.
* `fcSeriesAux G n`: the `n`-th term of the upper FC-central series, bundled with a proof that it is normal (auxiliary).
* `fcSeries G n`: the `n`-th term $FC_n(G)$ of the upper FC-central series, with $FC_0(G) = 1$ and $FC_{n+1}(G)/FC_n(G) = FC(G/FC_n(G))$.
* `IsFCNilpotentOfClassLE n G`: $FC_n(G) = G$, i.e. `G` is FC-nilpotent of class at most `n`.
* `IsFCNilpotent G`: $FC_n(G) = G$ for some `n`.
* `FCGood G n H`: for a subgroup `H ≤ G`, $FC_n(H) \le FC_n(G)$ (the non-trivial inclusion in Lemma 3.1).

### Lemmas

FC-centre and FC-series:

* `mem_fcCenter`: `x ∈ fcCenter G` if and only if `x` has finitely many conjugates.
* `fcCenter_normal`: the FC-centre is a normal subgroup (instance).
* `fcCenter_of_injective`: if `f : A →* B` is injective and `f a ∈ FC(B)`, then `a ∈ FC(A)`.
* `fcCenter_of_surjective`: if `f : A →* B` is surjective and `a ∈ FC(A)`, then `f a ∈ FC(B)`.
* `fcSeries_zero`: `fcSeries G 0 = ⊥` (simp lemma).
* `fcSeries_normal`: every `fcSeries G n` is normal (instance).
* `mem_fcSeries_succ`: `x ∈ fcSeries G (n + 1)` if and only if its image in `G / fcSeries G n` lies in the FC-centre.
* `fcSeries_comap_le`: for an injective `f : A →* B`, $f^{-1}(FC_n(B)) \le FC_n(A)$; for `H ≤ G` this gives $H \cap FC_n(G) \le FC_n(H)$.
* `exists_conj_seq_of_not_mem_fcSeries_succ`: if `a ∉ fcSeries G (n + 1)`, there is a sequence `w : ℕ → G` whose conjugates `w i * a * (w i)⁻¹` lie in pairwise distinct cosets of `fcSeries G n`.

Closure properties of the classes $FC_n$:

* `isFCNilpotentOfClassLE_isoClosed`: the class of FC-nilpotent groups of class at most `n` is isomorphism-closed.
* `isFCNilpotentOfClassLE_subgroupClosed`: the same class is subgroup-closed.
* `SubgroupClosed.of_le`: if `H ≤ K` and `K ∈ X`, then `H ∈ X` (for `X` subgroup- and iso-closed).

Countability:

* `countable_inv`: `S` countable implies `S⁻¹` countable.
* `countable_closure'`: `S` countable implies `⟨S⟩` countable (as a set).
* `countable_iSup`: a countable join of countable subgroups is countable.

### Main theorems

* `exists_countable_fcSeries` (Lemma 3.1): for every `n` and every countable subgroup `X` of `G` there is a countable subgroup `H` with `X ≤ H` and `FCGood G n H`. Together with `fcSeries_comap_le`, this gives $H \cap FC_n(G) = FC_n(H)$.
* `isFCNilpotentOfClassLE_countablyRecognizable` (Theorem 3.2): for every `n`, the class of FC-nilpotent groups of class at most `n` is countably recognizable.
* `countablyRecognizable_iUnion` (Lemma 3.3): the union of countably many iso-closed, subgroup-closed, countably recognizable classes is countably recognizable.
* `isFCNilpotent_countablyRecognizable` (Corollary 3.4): the class of FC-nilpotent groups is countably recognizable. It is `countablyRecognizable_iUnion` applied to the classes `IsFCNilpotentOfClassLE n`.

## Lemma 3.5 in Lean 4

Formalization of Lemma 3.5 from de Giovanni & Trombetti: for a countable subgroup $X$ of a group $G$ and an element $g \in G$, there is a countable subgroup $Y$ containing $\langle g, X\rangle$ such that $C_X(\langle g\rangle^{G}) = C_X(\langle g\rangle^{Y})$.

**Lemma 3.5.** Let $G$ be a group, and let $X$ be a countable subgroup of $G$. Then for every element $g$ of $G$ there exists a countable subgroup $Y$ of $G$ such that $\langle g, X\rangle \le Y$ and $C_X(\langle g\rangle^{G}) = C_X(\langle g\rangle^{Y})$.

### Definitions

* `conjSet g Y`: the set $\{ygy^{-1} : y \in Y\}$ of `Y`-conjugates of `g`; it generates the normal closure $\langle g\rangle^{Y}$.
* `conjCent g Y`: the centralizer in `G` of `conjSet g Y`, i.e. $C_G(\langle g\rangle^{Y})$ (built on Mathlib's `Subgroup.centralizer`).

###
Lemmas

* `mem_conjCent_iff`: `x ∈ conjCent g Y` if and only if `x` commutes with every `Y`-conjugate of `g`.
* `conjCent_antitone`: if `Y ≤ Z` then `conjCent g Z ≤ conjCent g Y`.
* `countable_inv`: `S` countable implies `S⁻¹` countable.
* `countable_closure'`: `S` countable implies `⟨S⟩` countable (as a set).

## Main theorem

* `exists_countable_conjCent_eq` (Lemma 3.5): for a countable subgroup `X` and `g : G`, there is a countable subgroup `Y` with `g ∈ Y`, `X ≤ Y` and `X ⊓ conjCent g ⊤ = X ⊓ conjCent g Y`.


## Theorem 3.6 in Lean 4

Formalization of Theorem 3.6 from de Giovanni & Trombetti, *Countably recognizable classes of groups with restricted conjugacy classes*.

**Theorem 3.6.** Let \(\mathfrak{X}\) be a subgroup-closed and countably recognizable class of groups. Then the class \(M\mathfrak{X}\) is countably recognizable.

### Definitions

- `GroupProperty`: a class of groups represented as a predicate on groups.
- `IsMX X G`: every finite subset of `G` is contained in a normal subgroup belonging to `X`.
- `IsoClosed X`: the class `X` is invariant under group isomorphisms.
- `SubgroupClosed X`: every subgroup of an `X`-group belongs to `X`.
- `CountablyRecognizable X`: if every countable subgroup of `G` belongs to `X`, then `G` belongs to `X`.

### Auxiliary lemmas

- `exists_mem_of_mem_closure_subset`: transfers membership in a subgroup generated by a set to a subgroup whose elements represent those generators.
- `countable_inv`: the inverse of a countable set is countable.
- `countable_closure`: the subgroup generated by a countable set is countable.
- `countable_closure'`: the generated subgroup is countable as a type.
- `exists_countable_subset_of_subset_closure`: if a countable set `A` is contained in `⟨s⟩`, there exists a countable subset `c ⊆ s` such that `A ⊆ ⟨c⟩`.
- `SubgroupClosed.of_le`: subgroup-closure and isomorphism-closure allow membership in `X` to pass to smaller subgroups.
- `isMX_iff`: characterizes membership in `MX` using normal closures of finite subsets.

### Main theorem

- `isMX_countablyRecognizable` (Theorem 3.6): if `X` is subgroup-closed, isomorphism-closed, and countably recognizable, then `IsMX X` is countably recognizable.

## Theorem 3.7 in Lean 4

Source: [Theorem 3 7.lean](Theorem%203%207.lean).

**Theorem 3.7.** If a group class X is subgroup-closed and countably recognizable, then XC is countably recognizable. In Lean, isomorphism-closure is an explicit hypothesis.

### Definitions and abbreviations

- `GroupProperty`: A group class represented as a predicate on a type equipped with a group structure.
- `CountablyRecognizable`: If every countable subgroup of G satisfies the property, then G satisfies it.
- `IsoClosed`: Membership in the class is preserved by group isomorphisms.
- `SubgroupClosed`: Every subgroup of a group in the class is also in the class.
- `conjSet`: The set of conjugates y * g * y⁻¹ with y in the specified subgroup.
- `conjCent`: The centralizer in the ambient group of that conjugate set.
- `IsXC`: For every g, the quotient by conjCent g ⊤ satisfies the given class predicate.
- `QuotientClosed`: Every quotient of a group in the class by a normal subgroup is in the class.

### Instances

- `conjCent`: The centralizer in the ambient group of that conjugate set.
- `conjCent_top_normal`: Provides normality of conjCent g ⊤, allowing the quotient group to be formed.

### Auxiliary lemmas and reused results

- `mem_conjCent_iff`: Expands centralizer membership into commuting with each conjugate.
- `conjCent_antitone`: If Y ≤ Z, then conjCent g Z ≤ conjCent g Y.
- `conjSet_top`: Identifies all conjugates of g with Mathlib's conjugates of the singleton {g}.
- `conjCent_top_eq`: Identifies conjCent g ⊤ with the centralizer of the normal closure of {g}.
- `conjCent_map_equiv`: An isomorphism maps the centralizer of the normal closure of g onto the corresponding centralizer of its image.
- `QuotientClosed.of_surjective`: Transfers class membership to the target of a surjective homomorphism via the quotient by its kernel; requires IsoClosed and QuotientClosed.
- `conjCent_top_subtype`: Relates the centralizer computed in a subgroup type to the ambient centralizer restricted using subgroupOf.
- `SubgroupClosed.of_injective`: Transfers class membership from the target to the source of an injective homomorphism; requires SubgroupClosed and IsoClosed.
- `isXC_isoClosed`: Proves IsoClosed (IsXC X) from IsoClosed X.
- `isXC_quotientClosed`: Proves QuotientClosed (IsXC X) from IsoClosed X and QuotientClosed X.
- `isXC_subgroupClosed`: Proves SubgroupClosed (IsXC X) from IsoClosed X, SubgroupClosed X, and QuotientClosed X.
- `countable_inv`: The inverse set of a countable set is countable.
- `countable_closure'`: The subgroup generated by a countable set is countable, using finite lists of generators and their inverses.
- `exists_countable_conjCent_eq`: Lemma 3.5: constructs a countable overgroup containing g and a countable subgroup X while preserving X ⊓ conjCent g ⊤.
- `exists_subgroup_mulEquiv_range`: Builds an isomorphism from the image of a restricted ambient quotient map to a subgroup of a quotient inside the countable overgroup, by proving equality of kernels.
- `range_mk'_comp_subtype_eq`: Shows that the image of the subgroup generated by chosen representatives is exactly the original quotient subgroup.

### Direct dependencies of the main proof

`countable_closure'`, `exists_countable_conjCent_eq`, `range_mk'_comp_subtype_eq`, and `exists_subgroup_mulEquiv_range`. The final step uses the hypotheses `hsub` and `hiso` and Mathlib's `MulEquiv.subgroupCongr`. This theorem does not require `QuotientClosed X`; the file also contains closure lemmas needed later.

### Mathlib tools used in this file

- `Quotient.exists_rep`: Chooses a representative for a quotient element.
- `QuotientGroup.mk'`: The canonical quotient homomorphism.
- `QuotientGroup.eq`: Relates equality of cosets to membership of a difference in the subgroup.
- `QuotientGroup.eq_one_iff`: Relates a quotient element being the identity to subgroup membership.
- `QuotientGroup.quotientKerEquivRange`: The first isomorphism theorem, identifying the quotient by a kernel with the range.
- `QuotientGroup.quotientMulEquivOfEq`: Identifies quotients by equal normal subgroups.
- `QuotientGroup.quotientKerEquivOfSurjective`: Identifies the quotient by a kernel with the target of a surjective homomorphism.
- `QuotientGroup.map`: Builds a homomorphism induced between quotient groups.
- `QuotientGroup.lift`: Factors a homomorphism through a quotient when its kernel contains the denominator.
- `QuotientGroup.congr`: Builds an isomorphism of quotient groups from an isomorphism carrying one denominator onto the other.
- `MonoidHom.ofInjective`: Identifies the source of an injective homomorphism with its range.
- `MonoidHom.map_closure`: Computes the image of a generated subgroup.
- `MulEquiv.subgroupCongr`: Builds a group isomorphism from equality of subgroups.
- `Subgroup.subset_closure`: Places generators in the subgroup they generate.
- `Subgroup.closure_le`: Proves that a generated subgroup lies in another subgroup by checking its generators.
- `Subgroup.mem_subgroupOf`: Translates membership in a subgroup restricted to another subgroup type.
- `Subgroup.inclusion`: The homomorphism associated with an inclusion of subgroups.
- `Set.countable_range`: The range of a map from a countable type is countable.
- `Submonoid.exists_list_of_mem_closure`: Expresses membership in a generated submonoid as a finite product; used in countable_closure'.

### Proof method

Assume the quotient associated with some g lies outside X. Countable recognizability supplies a countable subgroup K of this quotient outside X. Choose representatives, generate a countable subgroup X₀ of G, and apply Lemma 3.5 to obtain a countable overgroup Y. Equal kernels identify K with a subgroup of the quotient of Y by the centralizer of the normal closure of g in Y. The hypothesis on countable subgroups, subgroup-closure, and isomorphism-closure then force K into X, a contradiction.

### Main theorem

- `isXC_countablyRecognizable`: Theorem 3.7: proves CountablyRecognizable (IsXC X) from IsoClosed X, SubgroupClosed X, and CountablyRecognizable X.

## Corollary 3.8 in Lean 4

Source: [Corollary 3 8.lean](Corollary%203%208.lean).

**Corollary 3.8.** The class $FC^n$ is countably recognizable for every non-negative integer n.

### Definitions and abbreviations

- `GroupProperty`: A group class represented as a predicate on a type equipped with a group structure.
- `CountablyRecognizable`: If every countable subgroup of G satisfies the property, then G satisfies it.
- `IsoClosed`: Membership in the class is preserved by group isomorphisms.
- `conjSet`: The set of conjugates y * g * y⁻¹ with y in the specified subgroup.
- `conjCent`: The centralizer in the ambient group of that conjugate set.
- `IsXC`: For every g, the quotient by conjCent g ⊤ satisfies the given class predicate.
- `FCpow`: Defines FCpow 0 G as Finite G and FCpow (n + 1) as IsXC (FCpow n); this is the class FC^n, not the term FC_n(G) of the upper FC-central series.
- `SubgroupClosed`: Every subgroup of a group in the class is also in the class.
- `QuotientClosed`: Every quotient of a group in the class by a normal subgroup is in the class.

### Instances

- `conjCent`: The centralizer in the ambient group of that conjugate set.
- `conjCent_top_normal`: Provides normality of conjCent g ⊤, allowing the quotient group to be formed.

### Auxiliary lemmas and reused results

- `mem_conjCent_iff`: Expands centralizer membership into commuting with each conjugate.
- `countable_inv`: The inverse set of a countable set is countable.
- `countable_closure'`: The subgroup generated by a countable set is countable, using finite lists of generators and their inverses.
- `finite_countablyRecognizable`: Proves countable recognizability of finite groups by extracting an infinite sequence from a hypothetical infinite group and generating a countable infinite subgroup.
- `conjSet_top`: Identifies all conjugates of g with Mathlib's conjugates of the singleton {g}.
- `conjCent_top_eq`: Identifies conjCent g ⊤ with the centralizer of the normal closure of {g}.
- `conjCent_map_equiv`: An isomorphism maps the centralizer of the normal closure of g onto the corresponding centralizer of its image.
- `QuotientClosed.of_surjective`: Transfers class membership to the target of a surjective homomorphism via the quotient by its kernel; requires IsoClosed and QuotientClosed.
- `conjCent_top_subtype`: Relates the centralizer computed in a subgroup type to the ambient centralizer restricted using subgroupOf.
- `finite_subgroupClosed`: A subgroup of a finite group is finite.
- `finite_quotientClosed`: A quotient of a finite group is finite.
- `finite_isoClosed`: An isomorphic copy of a finite group is finite.
- `isXC_isoClosed`: Proves IsoClosed (IsXC X) from IsoClosed X.
- `SubgroupClosed.of_injective`: Transfers class membership from the target to the source of an injective homomorphism; requires SubgroupClosed and IsoClosed.
- `conjCent_antitone`: If Y ≤ Z, then conjCent g Z ≤ conjCent g Y.
- `isXC_quotientClosed`: Proves QuotientClosed (IsXC X) from IsoClosed X and QuotientClosed X.
- `isXC_subgroupClosed`: Proves SubgroupClosed (IsXC X) from IsoClosed X, SubgroupClosed X, and QuotientClosed X.
- `fcPow_closed`: Simultaneously proves IsoClosed, QuotientClosed, and SubgroupClosed for FCpow n by induction.
- `fcPow_isoClosed`: Extracts isomorphism-closure of FCpow n from fcPow_closed.
- `fcPow_quotientClosed`: Extracts quotient-closure of FCpow n from fcPow_closed.
- `fcPow_subgroupClosed`: Extracts subgroup-closure of FCpow n from fcPow_closed.
- `exists_countable_conjCent_eq`: Lemma 3.5: constructs a countable overgroup containing g and a countable subgroup X while preserving X ⊓ conjCent g ⊤.
- `exists_subgroup_mulEquiv_range`: Builds an isomorphism from the image of a restricted ambient quotient map to a subgroup of a quotient inside the countable overgroup, by proving equality of kernels.
- `range_mk'_comp_subtype_eq`: Shows that the image of the subgroup generated by chosen representatives is exactly the original quotient subgroup.
- `isXC_countablyRecognizable`: Theorem 3.7: proves CountablyRecognizable (IsXC X) from IsoClosed X, SubgroupClosed X, and CountablyRecognizable X.

### Direct dependencies of the main proof

`finite_countablyRecognizable` in the zero case; `isXC_countablyRecognizable`, `fcPow_isoClosed`, and `fcPow_subgroupClosed` in the successor case. The closure facts come from `fcPow_closed`, whose induction uses the three finite closure lemmas and `isXC_isoClosed`, `isXC_quotientClosed`, and `isXC_subgroupClosed`.

### Mathlib tools used in this file

- `Quotient.exists_rep`: Chooses a representative for a quotient element.
- `QuotientGroup.mk'`: The canonical quotient homomorphism.
- `QuotientGroup.eq`: Relates equality of cosets to membership of a difference in the subgroup.
- `QuotientGroup.eq_one_iff`: Relates a quotient element being the identity to subgroup membership.
- `QuotientGroup.quotientKerEquivRange`: The first isomorphism theorem, identifying the quotient by a kernel with the range.
- `QuotientGroup.quotientMulEquivOfEq`: Identifies quotients by equal normal subgroups.
- `QuotientGroup.quotientKerEquivOfSurjective`: Identifies the quotient by a kernel with the target of a surjective homomorphism.
- `QuotientGroup.map`: Builds a homomorphism induced between quotient groups.
- `QuotientGroup.lift`: Factors a homomorphism through a quotient when its kernel contains the denominator.
- `QuotientGroup.congr`: Builds an isomorphism of quotient groups from an isomorphism carrying one denominator onto the other.
- `MonoidHom.ofInjective`: Identifies the source of an injective homomorphism with its range.
- `MonoidHom.map_closure`: Computes the image of a generated subgroup.
- `MulEquiv.subgroupCongr`: Builds a group isomorphism from equality of subgroups.
- `Subgroup.subset_closure`: Places generators in the subgroup they generate.
- `Subgroup.closure_le`: Proves that a generated subgroup lies in another subgroup by checking its generators.
- `Subgroup.mem_subgroupOf`: Translates membership in a subgroup restricted to another subgroup type.
- `Subgroup.inclusion`: The homomorphism associated with an inclusion of subgroups.
- `Set.countable_range`: The range of a map from a countable type is countable.
- `Submonoid.exists_list_of_mem_closure`: Expresses membership in a generated submonoid as a finite product; used in countable_closure'.
- `Infinite.natEmbedding`: Extracts an injective sequence indexed by the natural numbers from an infinite type.
- `Infinite.of_injective`: Transfers infinitude along an injective map.

### Proof method

First establish all three closure properties simultaneously. Then use a second induction for countable recognizability: the base case is `finite_countablyRecognizable`, and the successor case applies Theorem 3.7 to `FCpow n` using its isomorphism-closure, subgroup-closure, and the induction hypothesis.

### Main theorem

- `fcPow_countablyRecognizable`: Corollary 3.8: inducts on n, using finite_countablyRecognizable at zero and Theorem 3.7 at the successor.

## Theorem 3.9 in Lean 4

Source: [Theorem 3 9.lean](Theorem%203%209.lean).

**Theorem 3.9.** The class $FC^\infty$ is countably recognizable.

### Definitions and abbreviations

- `GroupProperty`: A group class represented as a predicate on a type equipped with a group structure.
- `CountablyRecognizable`: If every countable subgroup of G satisfies the property, then G satisfies it.
- `IsoClosed`: Membership in the class is preserved by group isomorphisms.
- `conjSet`: The set of conjugates y * g * y⁻¹ with y in the specified subgroup.
- `conjCent`: The centralizer in the ambient group of that conjugate set.
- `IsXC`: For every g, the quotient by conjCent g ⊤ satisfies the given class predicate.
- `FCpow`: Defines FCpow 0 G as Finite G and FCpow (n + 1) as IsXC (FCpow n); this is the class FC^n, not the term FC_n(G) of the upper FC-central series.
- `SubgroupClosed`: Every subgroup of a group in the class is also in the class.
- `QuotientClosed`: Every quotient of a group in the class by a normal subgroup is in the class.
- `IsFCinf`: For each g, some n makes the quotient by conjCent g ⊤ belong to FCpow n; n can depend on g.

### Instances

- `conjCent`: The centralizer in the ambient group of that conjugate set.
- `conjCent_top_normal`: Provides normality of conjCent g ⊤, allowing the quotient group to be formed.

### Auxiliary lemmas and reused results

- `mem_conjCent_iff`: Expands centralizer membership into commuting with each conjugate.
- `countable_inv`: The inverse set of a countable set is countable.
- `countable_closure'`: The subgroup generated by a countable set is countable, using finite lists of generators and their inverses.
- `finite_countablyRecognizable`: Proves countable recognizability of finite groups by extracting an infinite sequence from a hypothetical infinite group and generating a countable infinite subgroup.
- `conjSet_top`: Identifies all conjugates of g with Mathlib's conjugates of the singleton {g}.
- `conjCent_top_eq`: Identifies conjCent g ⊤ with the centralizer of the normal closure of {g}.
- `conjCent_map_equiv`: An isomorphism maps the centralizer of the normal closure of g onto the corresponding centralizer of its image.
- `QuotientClosed.of_surjective`: Transfers class membership to the target of a surjective homomorphism via the quotient by its kernel; requires IsoClosed and QuotientClosed.
- `conjCent_top_subtype`: Relates the centralizer computed in a subgroup type to the ambient centralizer restricted using subgroupOf.
- `finite_subgroupClosed`: A subgroup of a finite group is finite.
- `finite_quotientClosed`: A quotient of a finite group is finite.
- `finite_isoClosed`: An isomorphic copy of a finite group is finite.
- `isXC_isoClosed`: Proves IsoClosed (IsXC X) from IsoClosed X.
- `SubgroupClosed.of_injective`: Transfers class membership from the target to the source of an injective homomorphism; requires SubgroupClosed and IsoClosed.
- `conjCent_antitone`: If Y ≤ Z, then conjCent g Z ≤ conjCent g Y.
- `isXC_quotientClosed`: Proves QuotientClosed (IsXC X) from IsoClosed X and QuotientClosed X.
- `isXC_subgroupClosed`: Proves SubgroupClosed (IsXC X) from IsoClosed X, SubgroupClosed X, and QuotientClosed X.
- `fcPow_closed`: Simultaneously proves IsoClosed, QuotientClosed, and SubgroupClosed for FCpow n by induction.
- `fcPow_isoClosed`: Extracts isomorphism-closure of FCpow n from fcPow_closed.
- `fcPow_quotientClosed`: Extracts quotient-closure of FCpow n from fcPow_closed.
- `fcPow_subgroupClosed`: Extracts subgroup-closure of FCpow n from fcPow_closed.
- `exists_countable_conjCent_eq`: Lemma 3.5: constructs a countable overgroup containing g and a countable subgroup X while preserving X ⊓ conjCent g ⊤.
- `exists_subgroup_mulEquiv_range`: Builds an isomorphism from the image of a restricted ambient quotient map to a subgroup of a quotient inside the countable overgroup, by proving equality of kernels.
- `range_mk'_comp_subtype_eq`: Shows that the image of the subgroup generated by chosen representatives is exactly the original quotient subgroup.
- `isXC_countablyRecognizable`: Theorem 3.7: proves CountablyRecognizable (IsXC X) from IsoClosed X, SubgroupClosed X, and CountablyRecognizable X.
- `fcPow_countablyRecognizable`: Corollary 3.8: inducts on n, using finite_countablyRecognizable at zero and Theorem 3.7 at the successor.
- `countable_iSup`: A join of countably many countable subgroups is countable; rewrites the join as the closure of their union.

### Direct dependencies of the main proof

`fcPow_countablyRecognizable`, `countable_closure'`, `countable_iSup`, `exists_countable_conjCent_eq`, `conjCent_antitone`, `range_mk'_comp_subtype_eq`, `exists_subgroup_mulEquiv_range`, `fcPow_isoClosed`, and `fcPow_subgroupClosed`. The other listed declarations provide the definitions and supporting proofs behind these dependencies.

### Mathlib tools used in this file

- `Quotient.exists_rep`: Chooses a representative for a quotient element.
- `QuotientGroup.mk'`: The canonical quotient homomorphism.
- `QuotientGroup.eq`: Relates equality of cosets to membership of a difference in the subgroup.
- `QuotientGroup.eq_one_iff`: Relates a quotient element being the identity to subgroup membership.
- `QuotientGroup.quotientKerEquivRange`: The first isomorphism theorem, identifying the quotient by a kernel with the range.
- `QuotientGroup.quotientMulEquivOfEq`: Identifies quotients by equal normal subgroups.
- `QuotientGroup.quotientKerEquivOfSurjective`: Identifies the quotient by a kernel with the target of a surjective homomorphism.
- `QuotientGroup.map`: Builds a homomorphism induced between quotient groups.
- `QuotientGroup.lift`: Factors a homomorphism through a quotient when its kernel contains the denominator.
- `QuotientGroup.congr`: Builds an isomorphism of quotient groups from an isomorphism carrying one denominator onto the other.
- `MonoidHom.ofInjective`: Identifies the source of an injective homomorphism with its range.
- `MonoidHom.map_closure`: Computes the image of a generated subgroup.
- `MulEquiv.subgroupCongr`: Builds a group isomorphism from equality of subgroups.
- `Subgroup.subset_closure`: Places generators in the subgroup they generate.
- `Subgroup.closure_le`: Proves that a generated subgroup lies in another subgroup by checking its generators.
- `Subgroup.mem_subgroupOf`: Translates membership in a subgroup restricted to another subgroup type.
- `Subgroup.inclusion`: The homomorphism associated with an inclusion of subgroups.
- `Subgroup.iSup_eq_closure`: Expresses a join of subgroups as the subgroup generated by their union.
- `Set.countable_range`: The range of a map from a countable type is countable.
- `Set.countable_iUnion`: A countable union of countable sets is countable.
- `Submonoid.exists_list_of_mem_closure`: Expresses membership in a generated submonoid as a finite product; used in countable_closure'.
- `Infinite.natEmbedding`: Extracts an injective sequence indexed by the natural numbers from an infinite type.
- `Infinite.of_injective`: Transfers infinitude along an injective map.

### Proof method

If the quotient associated with a fixed g lies outside every `FCpow n`, choose a countable subgroup `K n` outside each level and lift its elements to G. The Lean proof first takes the join of all generated lifts, then applies Lemma 3.5 once to obtain a countable overgroup Y. Since Y satisfies `IsFCinf`, its quotient at g belongs to `FCpow m` for some m. Kernel comparison identifies `K m` with a subgroup of this quotient, contradicting its choice.

### Main theorem

- `isFCinf_countablyRecognizable`: Theorem 3.9: proves CountablyRecognizable IsFCinf by choosing a bad countable quotient subgroup at every level and combining their lifts.

## Theorem 3.10 in Lean 4

Source: [Theorem 3 10.lean](Theorem%203%2010.lean).

**Theorem 3.10.** The class of CF-groups is countably recognizable.

### Definitions and abbreviations

- `GroupProperty`: A group class represented as a predicate on a type equipped with a group structure.
- `CountablyRecognizable`: If every countable subgroup of G satisfies the property, then G satisfies it.
- `IsoClosed`: Membership in the class is preserved by group isomorphisms.
- `IsCF`: For every subgroup X, the quotient of X by X.normalCore.subgroupOf X is finite, expressing finite index of the normal core.

### Auxiliary lemmas and reused results

- `exists_seq_of_infinite_quotient`: Extracts representatives a : ℕ → G of pairwise distinct cosets from an infinite quotient, so (a i)⁻¹ * a j ∉ N for i ≠ j.
- `countable_inv`: The inverse set of a countable set is countable.
- `countable_closure'`: The subgroup generated by a countable set is countable, using finite lists of generators and their inverses.
- `infinite_quotient_of_seq`: Proves the quotient infinite by showing that the sequence of cosets is injective.

### Direct dependencies of the main proof

`exists_seq_of_infinite_quotient`, `countable_closure'`, and `infinite_quotient_of_seq`, together with the hypothesis that every countable subgroup is CF. `IsoClosed` is declared in this file but is not used by this proof.

`X.normalCore` is the normal core in the ambient group. `X.normalCore.subgroupOf X` reinterprets it inside X. The proof also uses `Set.range`, `Subgroup.closure`, the subtype of X, and the subtype of H to keep the ambient groups explicit.

### Mathlib tools used in this file

- `Quotient.exists_rep`: Chooses a representative for a quotient element.
- `QuotientGroup.eq`: Relates equality of cosets to membership of a difference in the subgroup.
- `Subgroup.subset_closure`: Places generators in the subgroup they generate.
- `Subgroup.closure_le`: Proves that a generated subgroup lies in another subgroup by checking its generators.
- `Subgroup.mem_subgroupOf`: Translates membership in a subgroup restricted to another subgroup type.
- `Set.countable_range`: The range of a map from a countable type is countable.
- `Submonoid.exists_list_of_mem_closure`: Expresses membership in a generated submonoid as a finite product; used in countable_closure'.
- `Infinite.natEmbedding`: Extracts an injective sequence indexed by the natural numbers from an infinite type.
- `Infinite.of_injective`: Transfers infinitude along an injective map.
- `not_infinite_iff_finite`: Switches between finiteness and the negation of infinitude.

### Proof method

Assume $X/X_G$ is infinite and choose representatives `a n` of pairwise distinct cosets. For each pair of distinct indices, choose a conjugator witnessing that the difference of the representatives lies outside the normal core. Generate a countable subgroup H from all representatives and conjugators, and let K be the subgroup of H generated by the representatives. The hypothesis makes H a CF-group, so $K/K_H$ is finite. The chosen conjugators nevertheless keep all representatives distinct modulo $K_H$, and `infinite_quotient_of_seq` gives the contradiction.

This version works directly with witnesses outside X; it does not introduce the intermediate subgroup Y or require the equality $Y_G=X_G$ used in the handwritten proof.

### Main theorem

- `isCF_countablyRecognizable`: Theorem 3.10: proves CountablyRecognizable IsCF by generating a countable subgroup from representatives and conjugation witnesses.

