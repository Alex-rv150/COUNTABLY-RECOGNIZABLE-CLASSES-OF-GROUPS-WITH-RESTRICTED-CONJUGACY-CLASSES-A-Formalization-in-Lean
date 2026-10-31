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

/-- All subgroups of a group in the class belong to the class. -/
def SubgroupClosed (X : GroupProperty.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (H : Subgroup G), X G → X H


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
/-- `C_G(⟨g⟩^G)` is the centralizer of the normal closure of `g`, in accordance with the
definition used in the paper. -/
theorem conjSet_top (g : G) : conjSet g ⊤ = Group.conjugatesOfSet ({g} : Set G) := by
  ext x
  simp [conjSet, Group.conjugatesOfSet, conjugatesOf, isConj_iff]
theorem conjCent_top_eq (g : G) :
    conjCent g ⊤ = centralizer (normalClosure ({g} : Set G) : Set G) := by
  rw [conjCent, conjSet_top, normalClosure, centralizer_closure]
instance conjCent_top_normal (g : G) : (conjCent g (⊤ : Subgroup G)).Normal := by
  refine ⟨fun x hx a => ?_⟩
  rw [mem_conjCent_iff] at hx ⊢
  intro y _
  have hy := hx (a⁻¹ * y) (mem_top _)
  have : a⁻¹ * (y * g * y⁻¹) * a = (a⁻¹ * y) * g * (a⁻¹ * y)⁻¹ := by group
  calc y * g * y⁻¹ * (a * x * a⁻¹)
      = a * ((a⁻¹ * (y * g * y⁻¹) * a) * x) * a⁻¹ := by group
    _ = a * (x * (a⁻¹ * (y * g * y⁻¹) * a)) * a⁻¹ := by rw [this, hy]
    _ = a * x * a⁻¹ * (y * g * y⁻¹) := by group
/-- A group `G` has `X`-conjugacy classes if `G/C_G(⟨g⟩^G) ∈ X` for every `g ∈ G`. -/
def IsXC (X : GroupProperty.{u}) (G : Type u) [Group G] : Prop :=
  ∀ g : G, X (G ⧸ conjCent g (⊤ : Subgroup G))



theorem conjCent_map_equiv {G' : Type u} [Group G'] (e : G ≃* G') (g : G) :
    (conjCent g ⊤).map (e : G →* G') = conjCent (e g) ⊤ := by
  ext x'
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_conjCent_iff.2 (fun y' _ => ?_)
    obtain ⟨y, rfl⟩ := e.surjective y'
    have hy := mem_conjCent_iff.1 hx y (mem_top _)
    have := congrArg e hy
    simpa [mul_assoc] using this
  · intro hx'
    refine ⟨e.symm x', mem_conjCent_iff.2 (fun y _ => ?_), by simp⟩
    have hy := mem_conjCent_iff.1 hx' (e y) (mem_top _)
    have := congrArg e.symm hy
    simpa [mul_assoc] using this

def QuotientClosed (X : GroupProperty.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal], X G → X (G ⧸ N)


theorem QuotientClosed.of_surjective {X : GroupProperty.{u}} (hiso : IsoClosed X)
    (hquot : QuotientClosed X) {A B : Type u} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hA : X A) : X B :=
  hiso (QuotientGroup.quotientKerEquivOfSurjective f hf) (hquot f.ker hA)

theorem conjCent_top_subtype {Y : Subgroup G} (y0 : ↥Y) :
    conjCent y0 ⊤ = (conjCent (y0 : G) Y).subgroupOf Y := by
  ext x
  rw [mem_conjCent_iff, Subgroup.mem_subgroupOf, mem_conjCent_iff]
  constructor
  · intro hx y hy
    have h1 := hx ⟨y, hy⟩ (mem_top _)
    simpa using congrArg (fun z : ↥Y => (z : G)) h1
  · intro hx y _
    have h1 := hx (y : G) y.2
    exact Subtype.ext (by simpa using h1)




theorem SubgroupClosed.of_injective {X : GroupProperty.{u}} (hX : SubgroupClosed X)
    (hiso : IsoClosed X) {A B : Type u} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (h : X B) : X A :=
  hiso (MonoidHom.ofInjective hf).symm (hX f.range h)


theorem isXC_isoClosed {X : GroupProperty.{u}} (hiso : IsoClosed X) : IsoClosed (IsXC X) := by
  intro G G' _ _ e hG g'
  obtain ⟨g, rfl⟩ := e.surjective g'
  exact hiso (QuotientGroup.congr _ _ e (conjCent_map_equiv e g)) (hG g)
theorem isXC_quotientClosed {X : GroupProperty.{u}} (hiso : IsoClosed X)
    (hquot : QuotientClosed X) : QuotientClosed (IsXC X) := by
  intro G _ N _ hG q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  set B : Subgroup (G ⧸ N) := conjCent ((a : G ⧸ N)) ⊤ with hB
  set f : G →* ((G ⧸ N) ⧸ B) := (QuotientGroup.mk' B).comp (QuotientGroup.mk' N) with hf
  have hle : conjCent a ⊤ ≤ f.ker := by
    intro x hx
    have hmem : ((x : G) : G ⧸ N) ∈ B := by
      refine mem_conjCent_iff.2 ?_
      rintro y -
      obtain ⟨y0, rfl⟩ := Quotient.exists_rep y
      have h1 := mem_conjCent_iff.1 hx y0 (mem_top _)
      have := congrArg (fun z : G => (z : G ⧸ N)) h1
      simpa using this
    exact (QuotientGroup.eq_one_iff _).2 hmem
  set F : (G ⧸ conjCent a ⊤) →* ((G ⧸ N) ⧸ B) := QuotientGroup.lift _ f hle with hF
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective B z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨x, rfl⟩
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨x, hx⟩ := hfsurj z
    exact ⟨(x : G ⧸ conjCent a ⊤), hx⟩
  exact QuotientClosed.of_surjective hiso hquot F hFsurj (hG a)
theorem isXC_subgroupClosed {X : GroupProperty.{u}} (hiso : IsoClosed X)
    (hsub : SubgroupClosed X) (hquot : QuotientClosed X) : SubgroupClosed (IsXC X) := by
  intro G _ H hG h0
  set C : Subgroup G := conjCent ((h0 : G)) ⊤ with hC
  set D : Subgroup ↥H := C.subgroupOf H with hD
  have hDE : D ≤ conjCent h0 ⊤ := by
    intro x hx
    rw [conjCent_top_subtype, Subgroup.mem_subgroupOf]
    exact conjCent_antitone _ le_top (Subgroup.mem_subgroupOf.1 hx)
  -- `H/D` embeds into `G/C`
  have hcomap : D ≤ Subgroup.comap H.subtype C := le_rfl
  have hinj : Function.Injective (QuotientGroup.map D C H.subtype hcomap) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H a =>
      have h1 : QuotientGroup.map D C H.subtype hcomap (a : ↥H ⧸ D) = 1 := hx
      rw [QuotientGroup.map_mk] at h1
      have h2 : (a : G) ∈ C := (QuotientGroup.eq_one_iff _).1 h1
      exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff a).2 h2)
  have h1 : X (↥H ⧸ D) :=
    SubgroupClosed.of_injective hsub hiso _ hinj (hG (h0 : G))
  refine QuotientClosed.of_surjective hiso hquot
    (QuotientGroup.map D (conjCent h0 ⊤) (MonoidHom.id ↥H) (by simpa using hDE)) ?_ h1
  intro z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  exact ⟨(x : ↥H ⧸ D), by simp [QuotientGroup.map_mk]⟩

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



theorem exists_subgroup_mulEquiv_range (g : G) (X₀ Y : Subgroup G) (hgY : g ∈ Y)
    (hX₀Y : X₀ ≤ Y) (heq : X₀ ⊓ conjCent g ⊤ = X₀ ⊓ conjCent g Y) :
    ∃ K' : Subgroup (↥Y ⧸ conjCent (⟨g, hgY⟩ : ↥Y) ⊤),
      Nonempty (↥((QuotientGroup.mk' (conjCent g ⊤)).comp X₀.subtype).range ≃* ↥K') := by
  set g' : ↥Y := ⟨g, hgY⟩ with hg'
  set ψ : ↥X₀ →* G ⧸ conjCent g ⊤ := (QuotientGroup.mk' (conjCent g ⊤)).comp X₀.subtype with hψ
  set φ : ↥X₀ →* (↥Y ⧸ conjCent g' ⊤) :=
    (QuotientGroup.mk' (conjCent g' ⊤)).comp (Subgroup.inclusion hX₀Y) with hφ
  have hkers : φ.ker = ψ.ker := by
    ext x
    have hx : (x : G) ∈ X₀ := x.2
    constructor
    · intro hxk
      have h1 : ((Subgroup.inclusion hX₀Y) x) ∈ conjCent g' ⊤ :=
        (QuotientGroup.eq_one_iff _).1 hxk
      rw [conjCent_top_subtype, Subgroup.mem_subgroupOf] at h1
      have h2 : (x : G) ∈ X₀ ⊓ conjCent g Y := ⟨hx, h1⟩
      rw [← heq] at h2
      exact (QuotientGroup.eq_one_iff _).2 h2.2
    · intro hxk
      have h1 : ((x : G)) ∈ conjCent g ⊤ := (QuotientGroup.eq_one_iff _).1 hxk
      have h2 : (x : G) ∈ X₀ ⊓ conjCent g ⊤ := ⟨hx, h1⟩
      rw [heq] at h2
      refine (QuotientGroup.eq_one_iff _).2 ?_
      rw [conjCent_top_subtype, Subgroup.mem_subgroupOf]
      exact h2.2
  exact ⟨φ.range, ⟨(QuotientGroup.quotientKerEquivRange ψ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkers.symm).trans
      (QuotientGroup.quotientKerEquivRange φ))⟩⟩
/-- If `K` is a subgroup of `G/C` and `r` chooses a representative in `G` for each element of
`K`, then the subgroup generated by the representatives has image exactly `K`. -/
theorem range_mk'_comp_subtype_eq {C : Subgroup G} [C.Normal] (K : Subgroup (G ⧸ C))
    (r : K → G) (hr : ∀ k : K, (QuotientGroup.mk' C) (r k) = (k : G ⧸ C)) :
    ((QuotientGroup.mk' C).comp (Subgroup.closure (Set.range r)).subtype).range = K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    have hmap : Subgroup.map (QuotientGroup.mk' C) (Subgroup.closure (Set.range r)) ≤ K := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      change (QuotientGroup.mk' C) (r k) ∈ K
      rw [hr k]
      exact k.2
    exact hmap ⟨(x : G), x.2, rfl⟩
  · intro k hk
    exact ⟨⟨r ⟨k, hk⟩, Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩⟩, hr ⟨k, hk⟩⟩

theorem isXC_countablyRecognizable {X : GroupProperty.{u}} (hiso : IsoClosed X)
    (hsub : SubgroupClosed X) (hcr : CountablyRecognizable X) :
    CountablyRecognizable (IsXC X) := by
  classical
  intro G _ h g
  set C : Subgroup G := conjCent g ⊤ with hC
  by_contra hno
  -- a countable subgroup of `G/C` which is not in `X`
  obtain ⟨K, hKcount, hKX⟩ : ∃ K : Subgroup (G ⧸ C), Countable K ∧ ¬ X K := by
    by_contra hcon
    push Not at hcon
    exact hno (hcr fun K hK => hcon K hK)
  choose r hr using fun k : K => Quotient.exists_rep ((k : G ⧸ C))
  set X₀ : Subgroup G := Subgroup.closure (Set.range r) with hX₀
  have hX₀count : Countable X₀ := countable_closure' (Set.countable_range r)
  obtain ⟨Y, hYcount, hgY, hX₀Y, heq⟩ := exists_countable_conjCent_eq X₀ hX₀count g
  have hrange : ((QuotientGroup.mk' C).comp X₀.subtype).range = K :=
    range_mk'_comp_subtype_eq K r hr
  obtain ⟨K', ⟨e⟩⟩ := exists_subgroup_mulEquiv_range g X₀ Y hgY hX₀Y heq
  -- `Y` is countable, so `Y/C_Y(⟨g⟩^Y)` belongs to `X`
  have hY : X (↥Y ⧸ conjCent (⟨g, hgY⟩ : ↥Y) ⊤) := h Y hYcount ⟨g, hgY⟩
  exact hKX (hiso (MulEquiv.subgroupCongr hrange) (hiso e.symm (hsub K' hY)))
