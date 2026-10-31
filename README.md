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

### Definitions and instances

- `IsXC X G`: for every element g, the quotient of G by the centralizer of the normal closure of g belongs to X.
- `conjSet g Y`, `conjCent g Y`: the Y-conjugates of g and their centralizer in G.
- `conjCent_top_normal`: the centralizer of the normal closure of g is normal, so the quotient is well defined.
- `QuotientClosed X`: quotients of X-groups by normal subgroups belong to X.
- `GroupProperty`, `CountablyRecognizable`, `IsoClosed`, `SubgroupClosed`: the group-class predicates introduced above.

### Auxiliary lemmas

- `mem_conjCent_iff`: membership means commuting with every relevant conjugate.
- `conjCent_antitone`: enlarging the conjugating subgroup makes the centralizer smaller.
- `conjSet_top`, `conjCent_top_eq`: identify the conjugate set and centralizer with the normal-closure formulation.
- `conjCent_map_equiv`: transports centralizers through group isomorphisms.
- `conjCent_top_subtype`: identifies the centralizer computed inside a subgroup with the corresponding `subgroupOf`.
- `countable_inv`, `countable_closure'`: countability of inverses and generated subgroups.
- `exists_countable_conjCent_eq` (Lemma 3.5): finds a countable overgroup containing g and a given countable subgroup, preserving the centralizer intersection.
- `range_mk'_comp_subtype_eq`: the subgroup generated by chosen representatives of a quotient subgroup has image exactly that subgroup.
- `exists_subgroup_mulEquiv_range`: compares the kernels of two restricted quotient maps to construct an isomorphism between their ranges.
- `SubgroupClosed.of_injective`: transfers membership along an injective homomorphism, assuming subgroup- and isomorphism-closure.
- `QuotientClosed.of_surjective`: transfers membership along a surjective homomorphism, assuming quotient- and isomorphism-closure.
- `isXC_isoClosed`: propagates isomorphism-closure from X to XC.
- `isXC_quotientClosed`: propagates quotient-closure, assuming isomorphism- and quotient-closure of X.
- `isXC_subgroupClosed`: propagates subgroup-closure, assuming isomorphism-, subgroup-, and quotient-closure of X. These closure lemmas support Corollary 3.8; quotient-closure is not a hypothesis of Theorem 3.7.

### Proof method

Assume the quotient associated with some g lies outside X. Countable recognizability supplies a countable subgroup K of this quotient outside X. Choose representatives, generate a countable subgroup X₀ of G, and apply Lemma 3.5 to obtain a countable overgroup Y. Equal kernels identify K with a subgroup of the quotient of Y by the centralizer of the normal closure of g in Y. The hypothesis on countable subgroups, subgroup-closure, and isomorphism-closure then force K into X, a contradiction.

### Main theorem

- `isXC_countablyRecognizable`: from `IsoClosed X`, `SubgroupClosed X`, and `CountablyRecognizable X`, proves `CountablyRecognizable (IsXC X)`.

## Corollary 3.8 in Lean 4

Source: [Corollary 3 8.lean](Corollary%203%208.lean).

**Corollary 3.8.** The class $FC^n$ is countably recognizable for every non-negative integer n.

### Definitions

- `FCpow n G`: recursively defines `FCpow 0` as the finite groups and `FCpow (n + 1)` as `IsXC (FCpow n)`.
- `FCpow n` denotes the class $FC^n$, distinct from the upper FC-central-series term `fcSeries G n`, denoted $FC_n(G)$.

### Auxiliary lemmas

- `finite_countablyRecognizable`: the class of finite groups is countably recognizable.
- `finite_isoClosed`, `finite_quotientClosed`, `finite_subgroupClosed`: base cases for the closure properties.
- `fcPow_closed`: simultaneously proves isomorphism-, quotient-, and subgroup-closure of `FCpow n` by induction.
- `fcPow_isoClosed`, `fcPow_quotientClosed`, `fcPow_subgroupClosed`: extract the individual closure properties.
- `isXC_isoClosed`, `isXC_quotientClosed`, `isXC_subgroupClosed`: propagate closure properties through the XC operation.
- `isXC_countablyRecognizable` (Theorem 3.7): supplies the recognizability step.

### Proof method

First establish all three closure properties simultaneously. Then use a second induction for countable recognizability: the base case is `finite_countablyRecognizable`, and the successor case applies Theorem 3.7 to `FCpow n` using its isomorphism-closure, subgroup-closure, and the induction hypothesis.

### Main theorem

- `fcPow_countablyRecognizable (n : ℕ)`: proves `CountablyRecognizable (FCpow n)`.

## Theorem 3.9 in Lean 4

Source: [Theorem 3 9.lean](Theorem%203%209.lean).

**Theorem 3.9.** The class $FC^\infty$ is countably recognizable.

### Definitions

- `IsFCinf G`: for every g, there exists n such that the quotient of G by the centralizer of the normal closure of g belongs to `FCpow n`. The bound may depend on g.

### Auxiliary lemmas and reused results

- `fcPow_countablyRecognizable` (Corollary 3.8): supplies a countable quotient subgroup outside each specified level.
- `countable_closure'`: the representatives for each quotient subgroup generate a countable subgroup.
- `countable_iSup`: a countable join of countable subgroups is countable.
- `exists_countable_conjCent_eq` (Lemma 3.5): preserves the centralizer intersection on that join inside a countable overgroup.
- `conjCent_antitone`: helps restrict that equality to an individual subgroup of the join.
- `range_mk'_comp_subtype_eq`: identifies each lifted subgroup's quotient image.
- `exists_subgroup_mulEquiv_range`: transfers that image, up to isomorphism, to a subgroup of the quotient inside the countable overgroup.
- `fcPow_isoClosed`, `fcPow_subgroupClosed`: transfer membership in `FCpow m` back to the selected quotient subgroup.

### Proof method

If the quotient associated with a fixed g lies outside every `FCpow n`, choose a countable subgroup `K n` outside each level and lift its elements to G. The Lean proof first takes the join of all generated lifts, then applies Lemma 3.5 once to obtain a countable overgroup Y. Since Y satisfies `IsFCinf`, its quotient at g belongs to `FCpow m` for some m. Kernel comparison identifies `K m` with a subgroup of this quotient, contradicting its choice.

### Main theorem

- `isFCinf_countablyRecognizable`: proves `CountablyRecognizable IsFCinf`.

## Theorem 3.10 in Lean 4

Source: [Theorem 3 10.lean](Theorem%203%2010.lean).

**Theorem 3.10.** The class of CF-groups is countably recognizable.

### Definitions and Mathlib constructions

- `IsCF G`: for every subgroup X, the quotient of X by its normal core in G is finite, expressing $|X:X_G|<\infty$.
- `X.normalCore`: the largest normal subgroup of G contained in X.
- `X.normalCore.subgroupOf X`: views that core as a subgroup of X so that the quotient can be formed.
- `CountablyRecognizable`: the same recognizability predicate used in the preceding results.

### Auxiliary lemmas

- `exists_seq_of_infinite_quotient`: an infinite quotient `G ⧸ N` admits representatives `a : ℕ → G` with `(a i)⁻¹ * a j ∉ N` whenever `i ≠ j`.
- `countable_inv`, `countable_closure'`: establish countability of the generated witness subgroup.
- `infinite_quotient_of_seq`: representatives with pairwise distinct cosets prove that `G ⧸ N` is infinite.

### Proof method

Assume $X/X_G$ is infinite and choose representatives `a n` of pairwise distinct cosets. For each pair of distinct indices, choose a conjugator witnessing that the difference of the representatives lies outside the normal core. Generate a countable subgroup H from all representatives and conjugators, and let K be the subgroup of H generated by the representatives. The hypothesis makes H a CF-group, so $K/K_H$ is finite. The chosen conjugators nevertheless keep all representatives distinct modulo $K_H$, and `infinite_quotient_of_seq` gives the contradiction.

This version works directly with witnesses outside X; it does not introduce the intermediate subgroup Y or require the equality $Y_G=X_G$ used in the handwritten proof.

### Main theorem

- `isCF_countablyRecognizable`: proves `CountablyRecognizable IsCF`.

### Key Mathlib tools used in 3.7–3.10

- `Quotient.exists_rep`: chooses representatives of quotient elements.
- `QuotientGroup.mk'`, `MonoidHom.comp`, `Subgroup.subtype`, `Subgroup.inclusion`: construct quotient maps and restricted homomorphisms.
- `QuotientGroup.quotientKerEquivRange`, `QuotientGroup.quotientMulEquivOfEq`: compare ranges using quotients by equal kernels.
- `QuotientGroup.map`, `QuotientGroup.lift`: construct induced maps between quotients.
- `MulEquiv.subgroupCongr`: transports a group property across equality of subgroups.
- `Subgroup.closure`, `Subgroup.subset_closure`, `Subgroup.closure_le`: construct generated subgroups and prove containment.
- `Set.countable_range`, `Set.countable_iUnion`: establish countability of representatives, witnesses, and unions.
- `Infinite.natEmbedding`, `Infinite.of_injective`: extract an infinite sequence and prove infinitude by injection.
- `QuotientGroup.eq`, `Subgroup.mem_subgroupOf`: translate quotient equality and subgroup membership into the conditions used in the contradictions.
