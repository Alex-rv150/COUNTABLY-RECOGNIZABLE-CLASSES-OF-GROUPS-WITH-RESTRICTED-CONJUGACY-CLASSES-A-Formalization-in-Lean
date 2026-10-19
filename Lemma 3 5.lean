import Mathlib
universe u v

open Subgroup

variable {G : Type u} [Group G]

/-- The set of `Y`-conjugates of an element `g`; it generates the normal closure `⟨g⟩^Y`. -/
def conjSet (g : G) (Y : Subgroup G) : Set G := (fun y => y * g * y⁻¹) '' (Y : Set G)

def conjCent (g : G) (Y : Subgroup G) : Subgroup G := centralizer (conjSet g Y)

theorem mem_conjCent_iff {g x : G} {Y : Subgroup G} :
    x ∈ conjCent g Y ↔ ∀ y ∈ Y, (y * g * y⁻¹) * x = x * (y * g * y⁻¹) := by
  simp [conjCent, conjSet, mem_centralizer_iff]
  
theorem conjCent_antitone (g : G) {Y Z : Subgroup G} (h : Y ≤ Z) : conjCent g Z ≤ conjCent g Y := by
  intro x hx
  rw [mem_conjCent_iff] at *
  exact fun y hy => hx y (h hy)

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


/-- **Lemma 3.5.**  Given a countable subgroup `X` of `G` and an element `g` of `G`, there is a
countable subgroup `Y` of `G` containing `⟨g, X⟩` and such that `C_X(⟨g⟩^G) = C_X(⟨g⟩^Y)`. -/
theorem exists_countable_conjCent_eq (X : Subgroup G) (hX : Countable X) (g : G) :
    ∃ Y : Subgroup G, Countable Y ∧ g ∈ Y ∧ X ≤ Y ∧ X ⊓ conjCent g ⊤ = X ⊓ conjCent g Y := by
  classical
  have hwit : ∀ x : {x : ↥X // (x : G) ∉ conjCent g ⊤}, ∃ e : G,
      (e * g * e⁻¹) * ((x : ↥X) : G) ≠ ((x : ↥X) : G) * (e * g * e⁻¹) := by
    intro x
    have hx := x.2
    rw [mem_conjCent_iff] at hx
    push Not  at hx
    obtain ⟨y, _, hy⟩ := hx
    exact ⟨y, hy⟩
  choose e he using hwit
  have hXset : (X : Set G).Countable := Set.countable_coe_iff.mp hX
  refine ⟨Subgroup.closure (({g} ∪ (X : Set G)) ∪ Set.range e), ?_, ?_, ?_, ?_⟩
  · exact countable_closure'
      (((Set.countable_singleton g).union hXset).union (Set.countable_range e))
  · exact Subgroup.subset_closure (Or.inl (Or.inl rfl))
  · exact fun x hx => Subgroup.subset_closure (Or.inl (Or.inr hx))
  · refine le_antisymm (fun x hx => ⟨hx.1, conjCent_antitone g le_top hx.2⟩) ?_
    rintro x ⟨hxX, hxY⟩
    refine ⟨hxX, ?_⟩
    by_contra hno
    have hkey := he ⟨⟨x, hxX⟩, hno⟩
    have heY : e ⟨⟨x, hxX⟩, hno⟩ ∈ Subgroup.closure (({g} ∪ (X : Set G)) ∪ Set.range e) :=
      Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)
    exact hkey (mem_conjCent_iff.1 hxY _ heY)
