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

