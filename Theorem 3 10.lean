import Mathlib

universe u v

open Subgroup
/-- A class of groups, viewed as a predicate on groups. -/
abbrev GroupProperty := (G : Type u) → [Group G] → Prop

variable {G : Type u} [Group G]


def CountablyRecognizable (X : GroupProperty.{u}) : Prop :=
  ∀ {G : Type u} [Group G], (∀ H : Subgroup G, Countable H → X H) → X G


/-- The class is invariant under group isomorphism. -/
def IsoClosed (X : GroupProperty.{u}) : Prop :=
  ∀ {G H : Type u} [Group G] [Group H], (G ≃* H) → X G → X H

def IsCF (G : Type u) [Group G] : Prop :=
  ∀ X : Subgroup G, Finite (↥X ⧸ (X.normalCore.subgroupOf X))

theorem exists_seq_of_infinite_quotient {G : Type u} [Group G] (N : Subgroup G)
    (h : Infinite (G ⧸ N)) : ∃ a : ℕ → G, ∀ i j, i ≠ j → (a i)⁻¹ * a j ∉ N := by
  classical
  obtain ⟨f, hf⟩ := Infinite.natEmbedding (G ⧸ N)
  choose r hr using fun n : ℕ => Quotient.exists_rep (f n)
  refine ⟨r, fun i j hij hmem => hij ?_⟩
  have : f i = f j := by
    rw [← hr i, ← hr j]
    exact QuotientGroup.eq.2 hmem
  exact hf this


theorem countable_inv {G : Type u} [Group G] {s : Set G} (hs : s.Countable) :
    (s⁻¹ : Set G).Countable := by
  have := hs.image (fun x => x⁻¹)
  simpa [Set.image_inv_eq_inv] using this

theorem countable_closure' {G : Type u} [Group G] {s : Set G} (hs : s.Countable) :
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


theorem infinite_quotient_of_seq {G : Type u} [Group G] (N : Subgroup G) (a : ℕ → G)
    (ha : ∀ i j, i ≠ j → (a i)⁻¹ * a j ∉ N) : Infinite (G ⧸ N) := by
  have hinj : Function.Injective (fun n : ℕ => (a n : G ⧸ N)) := by
    intro i j hij
    by_contra hne
    exact ha i j hne (QuotientGroup.eq.1 hij)
  exact Infinite.of_injective _ hinj

theorem isCF_countablyRecognizable : CountablyRecognizable IsCF.{u} := by
  intro G _ h X
  rw [← not_infinite_iff_finite]
  intro hinf
  obtain ⟨a, ha⟩ := exists_seq_of_infinite_quotient (X.normalCore.subgroupOf X) hinf
  have hwit : ∀ p : {p : ℕ × ℕ // p.1 ≠ p.2}, ∃ z : G,
      z * (((a p.1.1 : ↥X) : G)⁻¹ * ((a p.1.2 : ↥X) : G)) * z⁻¹ ∉ X := by
    intro p
    have h1 := ha p.1.1 p.1.2 p.2
    rw [Subgroup.mem_subgroupOf] at h1
    by_contra hcon
    push Not at hcon
    refine h1 (fun b => ?_)
    simpa using hcon b
  choose z hz using hwit
  set H : Subgroup G :=
    Subgroup.closure (Set.range (fun n : ℕ => ((a n : ↥X) : G)) ∪ Set.range z) with hH
  have hcount : Countable H :=
    countable_closure' ((Set.countable_range _).union (Set.countable_range z))
  have haH : ∀ n, ((a n : ↥X) : G) ∈ H := fun n => Subgroup.subset_closure (Or.inl ⟨n, rfl⟩)
  have hzH : ∀ p, z p ∈ H := fun p => Subgroup.subset_closure (Or.inr ⟨p, rfl⟩)
  set A : ℕ → ↥H := fun n => ⟨((a n : ↥X) : G), haH n⟩ with hA
  set K : Subgroup ↥H := Subgroup.closure (Set.range A) with hK
  have hAK : ∀ n, A n ∈ K := fun n => Subgroup.subset_closure ⟨n, rfl⟩
  have hKX : K ≤ X.subgroupOf H := by
    rw [hK, Subgroup.closure_le]
    rintro _ ⟨n, rfl⟩
    exact (a n).2
  have hfin := h H hcount K
  refine (not_infinite_iff_finite.2 hfin) ?_
  refine infinite_quotient_of_seq _ (fun n => (⟨A n, hAK n⟩ : ↥K)) ?_
  intro i j hij hmem
  rw [Subgroup.mem_subgroupOf] at hmem
  have hconj := hmem ⟨z ⟨(i, j), hij⟩, hzH _⟩
  have hval := hKX hconj
  rw [Subgroup.mem_subgroupOf] at hval
  exact hz ⟨(i, j), hij⟩ (by simpa [hA, mul_assoc] using hval)
