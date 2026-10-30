import Mathlib

universe u v

open Subgroup

/-- A class of groups, viewed as a predicate on groups. -/
abbrev GroupProperty := (G : Type u) → [Group G] → Prop

variable {G : Type u} [Group G]


theorem exists_mem_of_mem_closure_subset {G : Type u} [Group G] {K : Subgroup G} {S : Set G}
    {P : Subgroup ↥K} (hSP : ∀ s ∈ S, ∃ p ∈ P, (p : G) = s) {y : G}
    (hy : y ∈ Subgroup.closure S) : ∃ p ∈ P, (p : G) = y := by
  have hle : Subgroup.closure S ≤ P.map K.subtype := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨p, hp, hpv⟩ := hSP s hs
    exact ⟨p, hp, hpv⟩
  exact hle hy

theorem exists_finset_of_mem_closure {G : Type u} [Group G] {s : Set G} {x : G}
    (hx : x ∈ Subgroup.closure s) :
    ∃ t : Finset G, ↑t ⊆ s ∧ x ∈ Subgroup.closure (t : Set G) := by
  classical
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact ⟨{y}, by simpa using hy, Subgroup.subset_closure (by simp)⟩
  | one => exact ⟨∅, by simp, one_mem _⟩
  | mul a b _ _ ha hb =>
      obtain ⟨t1, h1, h1'⟩ := ha
      obtain ⟨t2, h2, h2'⟩ := hb
      refine ⟨t1 ∪ t2, by simpa using Set.union_subset h1 h2, mul_mem ?_ ?_⟩
      · exact Subgroup.closure_mono (by simp) h1'
      · exact Subgroup.closure_mono (by simp) h2'
  | inv a _ ha =>
      obtain ⟨t, h, h'⟩ := ha
      exact ⟨t, h, inv_mem h'⟩



theorem exists_countable_subset_of_subset_closure
    {G : Type u} [Group G] {s : Set G} {A : Set G}
    (hA : A.Countable)
    (hAs : A ⊆ Subgroup.closure s) :
    ∃ c : Set G, c ⊆ s ∧ c.Countable ∧
      A ⊆ Subgroup.closure c := by
  classical
  choose t ht hxt using fun (x : A) =>
    exists_finset_of_mem_closure (hAs x.2)
  have hcount : Countable A := hA.to_subtype
  refine ⟨⋃ x : A, (t x : Set G),
    Set.iUnion_subset fun x => ht x,
    Set.countable_iUnion fun x => (t x).countable_toSet, ?_⟩
  intro a ha
  exact Subgroup.closure_mono
    (Set.subset_iUnion
      (fun x : A => ((t x : Finset G) : Set G))
      ⟨a, ha⟩)
    (hxt ⟨a, ha⟩)

theorem countable_inv {G : Type u} [Group G] {s : Set G} (hs : s.Countable) :
    (s⁻¹ : Set G).Countable := by
  have := hs.image (fun x => x⁻¹)
  simpa [Set.image_inv_eq_inv] using this

def CountablyRecognizable (X : GroupProperty.{u}) : Prop :=
  ∀ {G : Type u} [Group G], (∀ H : Subgroup G, Countable H → X H) → X G

theorem countable_closure {G : Type u} [Group G] {s : Set G} (hs : s.Countable) :
    (Subgroup.closure s : Set G).Countable := by
  have ht : (s ∪ s⁻¹).Countable := hs.union (countable_inv hs)
  have : Countable ↥(s ∪ s⁻¹) := ht.to_subtype
  have hsub : (Subgroup.closure s : Set G) ⊆
      Set.range (fun l : List ↥(s ∪ s⁻¹) => (l.map Subtype.val).prod) := by
    intro x hx
    rw [SetLike.mem_coe, ← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hx
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    exact ⟨l.attachWith _ hl, by simp⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

theorem countable_closure' {G : Type u} [Group G] {s : Set G} (hs : s.Countable) :
    Countable (Subgroup.closure s) :=
  (countable_closure hs).to_subtype

/-- The class `MX`: all groups in which every finite subset lies in a normal `X`-subgroup. -/
def IsMX (X : GroupProperty.{u}) (G : Type u) [Group G] : Prop :=
  ∀ s : Finset G, ∃ N : Subgroup G, N.Normal ∧ (↑s : Set G) ⊆ (N : Set G) ∧ X N

/-- The class is invariant under group isomorphism. -/
def IsoClosed (X : GroupProperty.{u}) : Prop :=
  ∀ {G H : Type u} [Group G] [Group H], (G ≃* H) → X G → X H

/-- All subgroups of a group in the class belong to the class. -/
def SubgroupClosed (X : GroupProperty.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (H : Subgroup G), X G → X H


theorem SubgroupClosed.of_le {X : GroupProperty.{u}} (hX : SubgroupClosed X)
    (hiso : IsoClosed X) {G : Type u} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (h : X K) : X H :=
  hiso (Subgroup.subgroupOfEquivOfLe hHK) (hX (H.subgroupOf K) h)

/-- For a subgroup closed class, membership in `MX` can be tested on normal closures of finite
subsets. -/
theorem isMX_iff {X : GroupProperty.{u}} (hsub : SubgroupClosed X) (hiso : IsoClosed X)
    {G : Type u} [Group G] :
    IsMX X G ↔ ∀ s : Finset G, X ↥(normalClosure (s : Set G)) := by
  constructor
  · intro hG s
    obtain ⟨N, hNnormal, hsN, hXN⟩ := hG s
    exact SubgroupClosed.of_le hsub hiso (normalClosure_le_normal hsN) hXN
  · intro hG s
    exact ⟨normalClosure (s : Set G), normalClosure_normal, subset_normalClosure, hG s⟩

/-- **Theorem 3.6.** If `X` is a subgroup closed and countably recognizable group class, then
the class `MX` is countably recognizable. -/
theorem isMX_countablyRecognizable {X : GroupProperty.{u}} (hiso : IsoClosed X)
    (hsub : SubgroupClosed X) (hcr : CountablyRecognizable X) :
    CountablyRecognizable (IsMX X) := by
  classical
  intro G _ h s
  refine ⟨normalClosure (s : Set G), normalClosure_normal, subset_normalClosure, ?_⟩
  by_contra hXn
  -- a countable subgroup of the normal closure which is not in `X`
  obtain ⟨U, hUcount, hUX⟩ : ∃ U : Subgroup ↥(normalClosure (s : Set G)),
      Countable U ∧ ¬ X U := by
    by_contra hcon
    push Not at hcon
    exact hXn (hcr (fun U hU => hcon U hU))
  set Ug : Subgroup G := U.map (normalClosure (s : Set G)).subtype with hUg
  have hUiso : (↥U : Type u) ≃* ↥Ug :=
    Subgroup.equivMapOfInjective U _ Subtype.val_injective
  have hUgcount : Countable Ug := by
    have := hUcount
    exact Countable.of_equiv _ hUiso.toEquiv
  have hUgsub : (Ug : Set G) ⊆ (normalClosure (s : Set G) : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.2
  obtain ⟨c, hcsub, hccount, hUc⟩ :=
    exists_countable_subset_of_subset_closure (Set.countable_coe_iff.mp hUgcount) hUgsub
  have : Countable c := hccount.to_subtype
  have hconj : ∀ d : c, ∃ e ∈ (s : Set G), ∃ v : G, v * e * v⁻¹ = (d : G) := by
    intro d
    obtain ⟨e, he, hde⟩ := Group.mem_conjugatesOfSet_iff.1 (hcsub d.2)
    obtain ⟨v, hv⟩ := isConj_iff.1 hde
    exact ⟨e, he, v, hv⟩
  choose e hes v hv using hconj
  -- the countable subgroup `H`
  set H : Subgroup G := Subgroup.closure ((s : Set G) ∪ Set.range v) with hH
  have hcount : Countable H :=
    countable_closure' ((s.finite_toSet.countable).union (Set.countable_range v))
  have hsH : (s : Set G) ⊆ (H : Set G) := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hvH : ∀ d, v d ∈ H := fun d => Subgroup.subset_closure (Or.inr ⟨d, rfl⟩)
  set s' : Finset ↥H := s.subtype (fun x => x ∈ H) with hs'
  obtain ⟨N, hNnormal, hsN, hXN⟩ := h H hcount s'
  have hPX : X ↥(normalClosure (s' : Set ↥H)) :=
    SubgroupClosed.of_le hsub hiso (normalClosure_le_normal hsN) hXN
  -- every element of `Ug` lies in the normal closure of `s` inside `H`
  have hmem : ∀ g ∈ Ug, ∃ p ∈ normalClosure (s' : Set ↥H), (p : G) = g := by
    intro g hg
    refine exists_mem_of_mem_closure_subset (K := H)
      (P := normalClosure (s' : Set ↥H)) ?_ (hUc hg)
    intro d hd
    have hdc : d ∈ c := hd
    have hes' : (⟨e ⟨d, hdc⟩, hsH (hes ⟨d, hdc⟩)⟩ : ↥H) ∈ (s' : Set ↥H) := by
      simpa [hs', Finset.mem_subtype] using hes ⟨d, hdc⟩
    refine ⟨(⟨v ⟨d, hdc⟩, hvH _⟩ : ↥H) * ⟨e ⟨d, hdc⟩, hsH (hes ⟨d, hdc⟩)⟩ *
      (⟨v ⟨d, hdc⟩, hvH _⟩ : ↥H)⁻¹, ?_, ?_⟩
    · exact normalClosure_normal.conj_mem _ (subset_normalClosure hes') _
    · simpa using hv ⟨d, hdc⟩
  have hUgH : Ug ≤ H := by
    intro g hg
    obtain ⟨p, _, hp⟩ := hmem g hg
    exact hp ▸ p.2
  have hle : Ug.subgroupOf H ≤ normalClosure (s' : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨p, hpP, hpv⟩ := hmem _ hx
    have hxp : x = p := Subtype.ext hpv.symm
    rw [hxp]
    exact hpP
  have hXUg : X ↥(Ug.subgroupOf H) := SubgroupClosed.of_le hsub hiso hle hPX
  exact hUX (hiso hUiso.symm (hiso (Subgroup.subgroupOfEquivOfLe hUgH) hXUg))


