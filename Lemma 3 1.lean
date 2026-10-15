import Mathlib
universe u v
variable {G : Type u} [Group G]

/-- The `FC`-centre of a group: the subgroup of all elements having only finitely many
conjugates. -/
def fcCenter (G : Type u) [Group G] : Subgroup G where
  carrier := {x : G | (Set.range fun g : G => g * x * g⁻¹).Finite}
  one_mem' := by
    simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    refine Set.Finite.subset (ha.mul hb) ?_
    rintro _ ⟨g, rfl⟩
    exact ⟨g * a * g⁻¹, ⟨g, rfl⟩, g * b * g⁻¹, ⟨g, rfl⟩, by group⟩
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    refine Set.Finite.subset ha.inv ?_
    rintro _ ⟨g, rfl⟩
    rw [Set.mem_inv]
    exact ⟨g, by group⟩

theorem mem_fcCenter {G : Type u} [Group G] {x : G} :
    x ∈ fcCenter G ↔ (Set.range fun g : G => g * x * g⁻¹).Finite := Iff.rfl

instance fcCenter_normal (G : Type u) [Group G] : (fcCenter G).Normal := by
  refine ⟨fun x hx a => ?_⟩
  rw [mem_fcCenter] at hx ⊢
  refine Set.Finite.subset hx ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨g * a, by group⟩

def fcSeriesAux (G : Type u) [Group G] : ℕ → { H : Subgroup G // H.Normal }
  | 0 => ⟨⊥, inferInstance⟩
  | (n + 1) =>
      let H := fcSeriesAux G n
      haveI : H.1.Normal := H.2
      ⟨(fcCenter (G ⧸ H.1)).comap (QuotientGroup.mk' H.1),
        Subgroup.Normal.comap (fcCenter_normal _) _⟩

def fcSeries (G : Type u) [Group G] (n : ℕ) : Subgroup G := (fcSeriesAux G n).1
instance fcSeries_normal (G : Type u) [Group G] (n : ℕ) : (fcSeries G n).Normal :=
  (fcSeriesAux G n).2

def FCGood (G : Type u) [Group G] (n : ℕ) (H : Subgroup G) : Prop :=
  ∀ x : ↥H, x ∈ fcSeries (↥H) n → (x : G) ∈ fcSeries G n

@[simp] theorem fcSeries_zero (G : Type u) [Group G] : fcSeries G 0 = ⊥ := rfl


theorem mem_fcSeries_succ {G : Type u} [Group G] {n : ℕ} {x : G} :
    x ∈ fcSeries G (n + 1) ↔
      (QuotientGroup.mk' (fcSeries G n) x) ∈ fcCenter (G ⧸ fcSeries G n) := Iff.rfl

/-- If `a` does not lie in `FCₙ₊₁(G)`, there is a sequence of conjugates of `a` lying in
pairwise distinct cosets of `FCₙ(G)`. -/
theorem exists_conj_seq_of_not_mem_fcSeries_succ {n : ℕ} {a : G}
    (ha : a ∉ fcSeries G (n + 1)) :
    ∃ w : ℕ → G, ∀ i j, i ≠ j →
      (w i * a * (w i)⁻¹)⁻¹ * (w j * a * (w j)⁻¹) ∉ fcSeries G n := by
  classical
  set N : Subgroup G := fcSeries G n with hN
  set ab : G ⧸ N := (QuotientGroup.mk' N) a with hab
  have hinf : (Set.range fun g : G ⧸ N => g * ab * g⁻¹).Infinite := by
    intro hfin
    exact ha (mem_fcSeries_succ.2 (mem_fcCenter.2 hfin))
  obtain ⟨e, he⟩ := hinf.natEmbedding
  choose q hq using fun i : ℕ => (e i).2
  choose w hw using fun i : ℕ => QuotientGroup.mk'_surjective N (q i)
  refine ⟨w, fun i j hij hmem => hij (he ?_)⟩
  have hconj : ∀ k : ℕ, (QuotientGroup.mk' N) (w k * a * (w k)⁻¹) = (e k : G ⧸ N) := by
    intro k
    rw [map_mul, map_mul, map_inv, hw k, ← hab]
    exact hq k
  have hEq : (QuotientGroup.mk' N) (w i * a * (w i)⁻¹) =
      (QuotientGroup.mk' N) (w j * a * (w j)⁻¹) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq.2 hmem
  rw [hconj i, hconj j] at hEq
  exact Subtype.ext hEq

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

theorem countable_iSup {G : Type u} [Group G] {ι : Type v} [Countable ι] (H : ι → Subgroup G)
    (h : ∀ i, Countable (H i)) : Countable ↥(⨆ i, H i) := by
  have hcount : (⋃ i, (H i : Set G)).Countable := by
    refine Set.countable_iUnion fun i => ?_
    have := h i
    exact Set.countable_coe_iff.mp (by simpa using h i)
  rw [Subgroup.iSup_eq_closure]
  exact countable_closure' hcount

theorem fcCenter_of_surjective {A B : Type u} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) {a : A} (h : a ∈ fcCenter A) : f a ∈ fcCenter B := by
  rw [mem_fcCenter] at h ⊢
  refine Set.Finite.subset (h.image f) ?_
  rintro _ ⟨b, rfl⟩
  obtain ⟨g, rfl⟩ := hf b
  exact ⟨g * a * g⁻¹, ⟨g, rfl⟩, by simp⟩


/-- The `FC`-centre is inherited by subgroups (and, more generally, along injective
homomorphisms). -/
theorem fcCenter_of_injective {A B : Type u} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {a : A} (h : f a ∈ fcCenter B) : a ∈ fcCenter A := by
  rw [mem_fcCenter] at h ⊢
  refine Set.Finite.of_finite_image ?_ hf.injOn
  refine Set.Finite.subset h ?_
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨f g, by simp⟩


/-- The upper `FC`-central series behaves monotonically along injective homomorphisms:
the preimage of `FCₙ(B)` is contained in `FCₙ(A)`. -/
theorem fcSeries_comap_le {A B : Type u} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (n : ℕ) : (fcSeries B n).comap f ≤ fcSeries A n := by
  induction n with
  | zero =>
      intro a ha
      have : f a = 1 := by simpa using ha
      simpa [fcSeries_zero] using hf (by simpa using this)
  | succ n ih =>
      intro a ha
      have hfa : (QuotientGroup.mk' (fcSeries B n)) (f a) ∈ fcCenter (B ⧸ fcSeries B n) :=
        mem_fcSeries_succ.1 ha
      set F : A →* B ⧸ fcSeries B n := (QuotientGroup.mk' (fcSeries B n)).comp f with hF
      have hker : F.ker ≤ fcSeries A n := by
        intro x hx
        refine ih ?_
        have hx1 : ((f x : B) : B ⧸ fcSeries B n) = 1 := hx
        exact (QuotientGroup.eq_one_iff (f x)).1 hx1
      -- `a` lies in the `FC`-centre of `A / F.ker`
      have h1 : (QuotientGroup.mk' F.ker a) ∈ fcCenter (A ⧸ F.ker) := by
        refine fcCenter_of_injective (QuotientGroup.kerLift F)
          (QuotientGroup.kerLift_injective F) ?_
        simpa [hF] using hfa
      -- push forward along the surjection `A / F.ker → A / FCₙ(A)`
      set q : (A ⧸ F.ker) →* (A ⧸ fcSeries A n) :=
        QuotientGroup.map F.ker (fcSeries A n) (MonoidHom.id A) (by simpa using hker) with hq
      have hqsurj : Function.Surjective q := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (fcSeries A n) z
        exact ⟨(QuotientGroup.mk' F.ker) x, by simp [hq, QuotientGroup.map_mk]⟩
      have h2 := fcCenter_of_surjective q hqsurj h1
      rw [mem_fcSeries_succ]
      simpa [hq, QuotientGroup.map_mk] using h2




theorem exists_countable_fcSeries (n : ℕ) {X : Subgroup G} (hX : Countable X) :
    ∃ H : Subgroup G, Countable H ∧ X ≤ H ∧ FCGood G n H := by
  classical
  induction n generalizing X with
  | zero =>
      refine ⟨X, hX, le_rfl, ?_⟩
      intro x hx
      rw [fcSeries_zero, Subgroup.mem_bot] at hx
      rw [fcSeries_zero, Subgroup.mem_bot, hx]
      rfl
  | succ n ih =>
      -- one step of the construction
      have hstep : ∀ P : {P : Subgroup G // Countable ↥P},
          ∃ Q : {P : Subgroup G // Countable ↥P},
            (P : Subgroup G) ≤ (Q : Subgroup G) ∧ FCGood G n (Q : Subgroup G) ∧
            ∀ a : G, a ∈ (P : Subgroup G) → a ∉ fcSeries G (n + 1) → ∃ w : ℕ → G,
              (∀ i, w i ∈ (Q : Subgroup G)) ∧
              ∀ i j, i ≠ j →
                (w i * a * (w i)⁻¹)⁻¹ * (w j * a * (w j)⁻¹) ∉ fcSeries G n := by
        rintro ⟨P, hP⟩
        choose w hw using fun a : {a : ↥P // (a : G) ∉ fcSeries G (n + 1)} =>
          exists_conj_seq_of_not_mem_fcSeries_succ a.2
        have hPset : (P : Set G).Countable := Set.countable_coe_iff.mp hP
        set S : Set G := (P : Set G) ∪ (⋃ a, Set.range (w a)) with hS
        have hScount : S.Countable := by
          refine hPset.union (Set.countable_iUnion fun a => Set.countable_range _)
        set P₁ : Subgroup G := Subgroup.closure S with hP₁
        have hP₁count : Countable ↥P₁ := countable_closure' hScount
        obtain ⟨R, hRcount, hP₁R, hRgood⟩ := ih hP₁count
        refine ⟨⟨R, hRcount⟩, ?_, hRgood, ?_⟩
        · exact le_trans (fun x hx => Subgroup.subset_closure (Or.inl hx)) hP₁R
        · intro a haP ha
          refine ⟨w ⟨⟨a, haP⟩, ha⟩, fun i => ?_, hw ⟨⟨a, haP⟩, ha⟩⟩
          refine hP₁R (Subgroup.subset_closure (Or.inr ?_))
          exact Set.mem_iUnion.2 ⟨⟨⟨a, haP⟩, ha⟩, ⟨i, rfl⟩⟩
      choose Z hZle hZgood hZw using hstep
      set U : ℕ → {P : Subgroup G // Countable ↥P} := fun k => Z^[k] ⟨X, hX⟩ with hU
      have hUsucc : ∀ k, U (k + 1) = Z (U k) := by
        intro k
        simp [hU, Function.iterate_succ_apply']
      have hUmono : Monotone fun k => ((U k : Subgroup G)) := by
        refine monotone_nat_of_le_succ fun k => ?_
        rw [hUsucc k]
        exact hZle (U k)
      set V : Subgroup G := ⨆ k, ((U k : Subgroup G)) with hV
      have hVcount : Countable ↥V := countable_iSup _ fun k => (U k).2
      have hdir : Directed (· ≤ ·) fun k => ((U k : Subgroup G)) := hUmono.directed_le
      have hUV : ∀ k, ((U k : Subgroup G)) ≤ V := by
        intro k
        rw [hV]
        exact le_iSup (fun k => ((U k : Subgroup G))) k
      have hmemV : ∀ x : G, x ∈ V → ∃ k, x ∈ ((U k : Subgroup G)) := by
        intro x hx
        exact (Subgroup.mem_iSup_of_directed hdir).1 hx
      -- `V` is good at level `n`
      have hgood : ∀ k, FCGood G n ((U (k + 1) : Subgroup G)) := by
        intro k
        rw [hUsucc k]
        exact hZgood (U k)
      have hVn : FCGood G n V := by
        intro x hx
        obtain ⟨k, hk0⟩ := hmemV (x : G) x.2
        have hk : (x : G) ∈ ((U (k + 1) : Subgroup G)) := hUmono (Nat.le_succ k) hk0
        have hle : ((U (k + 1) : Subgroup G)) ≤ V := hUV (k + 1)
        have hxk : (⟨(x : G), hk⟩ : ↥((U (k + 1) : Subgroup G))) ∈
            fcSeries ↥((U (k + 1) : Subgroup G)) n := by
          refine fcSeries_comap_le (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle) n ?_
          rw [Subgroup.mem_comap]
          have hx' : Subgroup.inclusion hle ⟨(x : G), hk⟩ = x := Subtype.ext rfl
          rw [hx']
          exact hx
        exact hgood k ⟨(x : G), hk⟩ hxk
      refine ⟨V, hVcount, ?_, ?_⟩
      · have h0 : ((U 0 : Subgroup G)) = X := by simp [hU]
        exact h0 ▸ hUV 0
      · intro v hv
        by_contra hvG
        obtain ⟨k, hk⟩ := hmemV (v : G) v.2
        obtain ⟨w, hwmem, hwne⟩ := hZw (U k) (v : G) hk hvG
        have hwV : ∀ i, w i ∈ V := by
          intro i
          refine hUV (k + 1) ?_
          rw [hUsucc k]
          exact hwmem i
        set w' : ℕ → ↥V := fun i => ⟨w i, hwV i⟩ with hw'
        have hfin := mem_fcCenter.1 (mem_fcSeries_succ.1 hv)
        set F : ℕ → (↥V ⧸ fcSeries (↥V) n) :=
          fun i => (QuotientGroup.mk' (fcSeries (↥V) n)) (w' i * v * (w' i)⁻¹) with hFdef
        have hFinj : Function.Injective F := by
          intro i j hij
          by_contra hne
          have h1 : ((w' i * v * (w' i)⁻¹)⁻¹ * (w' j * v * (w' j)⁻¹) : ↥V) ∈
              fcSeries (↥V) n :=
            QuotientGroup.eq.1 (by simpa [hFdef] using hij)
          have h2 := hVn _ h1
          refine hwne i j hne ?_
          simpa [hw'] using h2
        have hsub : Set.range F ⊆
            Set.range fun g : ↥V ⧸ fcSeries (↥V) n =>
              g * ((QuotientGroup.mk' (fcSeries (↥V) n)) v) * g⁻¹ := by
          rintro _ ⟨i, rfl⟩
          exact ⟨(QuotientGroup.mk' (fcSeries (↥V) n)) (w' i), by simp [hFdef]⟩
        exact Set.infinite_range_of_injective hFinj (hfin.subset hsub)
