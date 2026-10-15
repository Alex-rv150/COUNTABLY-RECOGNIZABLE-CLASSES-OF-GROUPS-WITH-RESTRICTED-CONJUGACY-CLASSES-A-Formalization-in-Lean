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
