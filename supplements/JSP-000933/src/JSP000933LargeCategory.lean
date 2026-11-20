import JSP000933LocalObstruction

open Filter
open scoped Topology

namespace JSP000933

noncomputable section

def euPrefixSmall (f : EUWeight) (ε : ℝ) : Set (Set ℕ) :=
  {X | ∀ p : ℕ, weightedSetDensity f.weight X p ≤ ε}

theorem euPrefixSmall_downward (f : EUWeight) (ε : ℝ) {X Y : Set ℕ}
    (h : X ⊆ Y) (hy : Y ∈ euPrefixSmall f ε) : X ∈ euPrefixSmall f ε := by
  intro p
  exact (weightedSetDensity_mono f.weight f.nonneg h p).trans (hy p)

theorem euPrefixSmall_union (f : EUWeight) {ε δ : ℝ} {X Y : Set ℕ}
    (hX : X ∈ euPrefixSmall f ε) (hY : Y ∈ euPrefixSmall f δ) :
    X ∪ Y ∈ euPrefixSmall f (ε + δ) := by
  intro p
  exact (weightedSetDensity_union_le f.weight f.nonneg X Y p).trans (add_le_add (hX p) (hY p))

theorem weightedNull_has_euPrefixSmall_tail (f : EUWeight) {X : Set ℕ}
    (hX : WeightedNull f.weight X) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, X \ Set.Iio N ∈ euPrefixSmall f ε := by
  obtain ⟨N,hN⟩ := hX ε hε
  refine ⟨N,fun p => ?_⟩
  by_cases hp : N ≤ p
  · exact (weightedSetDensity_mono f.weight f.nonneg (show X \ Set.Iio N ⊆ X from fun _ hx => hx.1) p).trans (hN p hp)
  · have hz : restrictSet (Finset.range p) (X \ Set.Iio N) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hmp,hmX⟩ := mem_restrictSet.mp hm
      exact hmX.2 ((Finset.mem_range.mp hmp).trans (Nat.lt_of_not_ge hp))
    simp [weightedSetDensity,hz,hε.le]

def euProfileSet (x : ℕ → Bool) : Set ℕ := {m | x m = true}

private def finiteModelWordSet (p : ℕ) (x : Fin p → Bool) : Set ℕ :=
  {m | ∃ h : m < p, x ⟨m,h⟩ = true}

private theorem density_depends_on_prefix_r10 (a : ℕ → ℝ) (p : ℕ) (x : ℕ → Bool) :
    weightedSetDensity a (euProfileSet x) p =
      weightedSetDensity a (finiteModelWordSet p (fun i => x i.1)) p := by
  have he : restrictSet (Finset.range p) (euProfileSet x) =
      restrictSet (Finset.range p) (finiteModelWordSet p (fun i => x i.1)) := by
    ext m
    simp only [mem_restrictSet,Finset.mem_range,euProfileSet,finiteModelWordSet,Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1,h.1,h.2⟩, fun h => ⟨h.1,h.2.choose_spec⟩⟩
  simp only [weightedSetDensity,he]

theorem isClosed_euPrefixSmall_profiles [TopologicalSpace Bool] [DiscreteTopology Bool]
    (f : EUWeight) (ε : ℝ) : IsClosed {x : ℕ → Bool | euProfileSet x ∈ euPrefixSmall f ε} := by
  have hc (p : ℕ) : IsClosed {x : ℕ → Bool | weightedSetDensity f.weight (euProfileSet x) p ≤ ε} := by
    let A : Set (Fin p → Bool) :=
      {x | weightedSetDensity f.weight (finiteModelWordSet p x) p ≤ ε}
    let G (x : ℕ → Bool) : Fin p → Bool := fun i => x i.1
    have hG : Continuous G := by
      apply continuous_pi
      intro i
      exact continuous_apply i.1
    have he : {x : ℕ → Bool | weightedSetDensity f.weight (euProfileSet x) p ≤ ε} = G ⁻¹' A := by
      ext x
      change weightedSetDensity f.weight (euProfileSet x) p ≤ ε ↔
        weightedSetDensity f.weight (finiteModelWordSet p (fun i => x i.1)) p ≤ ε
      rw [density_depends_on_prefix_r10]
    rw [he]
    exact (isClosed_discrete A).preimage hG
  have he : {x : ℕ → Bool | euProfileSet x ∈ euPrefixSmall f ε} =
      ⋂ p : ℕ, {x : ℕ → Bool | weightedSetDensity f.weight (euProfileSet x) p ≤ ε} := by
    ext x
    simp [euPrefixSmall]
  rw [he]
  exact isClosed_iInter hc

def profilesHavingLongBlock (A : Set ℕ) (N : ℕ) : Set (↥A → Bool) :=
  {x | ∃ i ≥ N, (justSourceBlock i : Set ℕ) ⊆ subsetOfProfile A x}

private theorem isOpen_contains_singleBlock_r10 [TopologicalSpace Bool] [DiscreteTopology Bool]
    (A : Set ℕ) (i : ℕ) :
    IsOpen {x : ↥A → Bool | (justSourceBlock i : Set ℕ) ⊆ subsetOfProfile A x} := by
  by_cases h : (justSourceBlock i : Set ℕ) ⊆ A
  · let j (m : ↥(justSourceBlock i)) : ↥A := ⟨m.1,h m.2⟩
    have he :
        {x : ↥A → Bool | (justSourceBlock i : Set ℕ) ⊆ subsetOfProfile A x} =
        ⋂ m : ↥(justSourceBlock i), (fun x : ↥A → Bool => x (j m)) ⁻¹' ({true} : Set Bool) := by
      ext x
      constructor
      · intro hx
        apply Set.mem_iInter.mpr
        intro m
        obtain ⟨hm,hx'⟩ := hx m.2
        exact Set.mem_singleton_iff.mpr hx'
      · intro hx
        intro m hm
        refine ⟨h hm,?_⟩
        exact Set.mem_singleton_iff.mp (Set.mem_iInter.mp hx ⟨m,hm⟩)
    rw [he]
    exact isOpen_iInter_of_finite (fun m => (isOpen_discrete _).preimage (continuous_apply (j m)))
  · have he : {x : ↥A → Bool | (justSourceBlock i : Set ℕ) ⊆ subsetOfProfile A x} = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (h (hx.trans (subsetOfProfile_subset A x)))
      · intro hx
        exact False.elim hx
    rw [he]
    exact isOpen_empty

theorem isOpen_profilesHavingLongBlock [TopologicalSpace Bool] [DiscreteTopology Bool]
    (A : Set ℕ) (N : ℕ) : IsOpen (profilesHavingLongBlock A N) := by
  have he : profilesHavingLongBlock A N =
      ⋃ i : ℕ, ⋃ _ : N ≤ i, {x : ↥A → Bool | (justSourceBlock i : Set ℕ) ⊆ subsetOfProfile A x} := by
    ext x
    simp [profilesHavingLongBlock]
  rw [he]
  exact isOpen_iUnion (fun i => isOpen_iUnion (fun _ => isOpen_contains_singleBlock_r10 A i))

theorem dense_profilesHavingLongBlock [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set ℕ} (hA : LongBlockLarge A) (N : ℕ) : Dense (profilesHavingLongBlock A N) := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hUn
  obtain ⟨x,hx⟩ := hUn
  have hUx : U ∈ 𝓝 x := hU.mem_nhds hx
  rw [nhds_pi] at hUx
  obtain ⟨S,V,hV,hSV⟩ := Filter.mem_pi'.mp hUx
  obtain ⟨K,hK⟩ :=
    eventually_disjoint_finset_of_pairwise justSourceBlock justSourceBlock_pairwise (S.image Subtype.val)
  obtain ⟨i,hi,hsub⟩ := hA.exists_block_from_index (max K N)
  let y (m : ↥A) : Bool := if m.1 ∈ justSourceBlock i then true else x m
  have hyS : y ∈ Set.pi (S : Set ↥A) V := by
    intro m hm
    have hout : m.1 ∉ justSourceBlock i := by
      intro hmem
      exact Finset.disjoint_left.mp (hK i ((le_max_left K N).trans hi)) hmem
        (Finset.mem_image.mpr ⟨m,hm,rfl⟩)
    change (if m.1 ∈ justSourceBlock i then true else x m) ∈ V m
    rw [ite_eq_right hout]
    exact mem_of_mem_nhds (hV m)
  have hyBlock : (justSourceBlock i : Set ℕ) ⊆ subsetOfProfile A y := by
    intro m hm
    exact ⟨hsub hm,by simp [y,Finset.mem_coe.mp hm]⟩
  exact ⟨y,hSV hyS,⟨i,(le_max_right K N).trans hi,hyBlock⟩⟩

theorem large_profiles_eq_iInter (A : Set ℕ) :
    {x : ↥A → Bool | LongBlockLarge (subsetOfProfile A x)} = ⋂ N, profilesHavingLongBlock A N := by
  classical
  ext x
  constructor
  · intro h
    change LongBlockLarge (subsetOfProfile A x) at h
    exact Set.mem_iInter.mpr (fun N => h.exists_block_from_index N)
  · intro h
    unfold LongBlockLarge
    intro hfin
    let s := hfin.toFinset
    obtain ⟨i,hi,hB⟩ := Set.mem_iInter.mp h (s.sup id + 1)
    have hin : i ∈ s := by simpa [s] using hB
    have hle : i ≤ s.sup id := Finset.le_sup (f := id) hin
    omega

theorem residual_large_subdomains [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set ℕ} [BaireSpace (↥A → Bool)] (hA : LongBlockLarge A) :
    {x : ↥A → Bool | LongBlockLarge (subsetOfProfile A x)} ∈ residual (↥A → Bool) := by
  rw [large_profiles_eq_iInter]
  have hOpen : ∀ N : ℕ, IsOpen (profilesHavingLongBlock A N) := isOpen_profilesHavingLongBlock A
  have hDense : ∀ N : ℕ, Dense (profilesHavingLongBlock A N) := dense_profilesHavingLongBlock hA
  exact residual_of_dense_Gδ (IsGδ.iInter_of_isOpen hOpen) (dense_iInter_of_isOpen hOpen hDense)

def binaryPrefixList (x : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => x i.1)

def binaryPrefixIndex (x : ℕ → Bool) (n : ℕ) : ℕ :=
  Encodable.encode (binaryPrefixList x n)

private theorem equal_binaryPrefixIndex_r10 {x y : ℕ → Bool} {n m : ℕ}
    (h : binaryPrefixIndex x n = binaryPrefixIndex y m) :
    n = m ∧ ∀ i < n, x i = y i := by
  have hL : binaryPrefixList x n = binaryPrefixList y m := Encodable.encode_injective h
  have he : n = m := by
    simpa [binaryPrefixList] using congrArg List.length hL
  subst m
  refine ⟨rfl, fun i hi => ?_⟩
  have hh := congrArg (fun l : List Bool => l[i]?) hL
  simpa [binaryPrefixList,List.getElem?_ofFn,hi] using hh

def branchLargeSet (x : ℕ → Bool) : Set ℕ :=
  glueBlocks (fun j => justSourceBlock (binaryPrefixIndex x j))

theorem branchLargeSet_large (x : ℕ → Bool) : LongBlockLarge (branchLargeSet x) := by
  unfold LongBlockLarge
  have hInj : Function.Injective (binaryPrefixIndex x) :=
    fun _ _ h => (equal_binaryPrefixIndex_r10 h).1
  apply (Set.infinite_range_of_injective hInj).mono
  rintro _ ⟨n,rfl⟩ m hm
  exact ⟨n,hm⟩

theorem branchLargeSet_almost_disjoint {x y : ℕ → Bool} (hxy : x ≠ y) :
    (branchLargeSet x ∩ branchLargeSet y).Finite := by
  classical
  have hh : ∃ d : ℕ, x d ≠ y d := by
    by_contra h
    apply hxy
    funext d
    by_contra hd
    exact h ⟨d,hd⟩
  obtain ⟨d,hd⟩ := hh
  have hfin : (⋃ n ∈ (Finset.range (d + 1) : Set ℕ),
      (justSourceBlock (binaryPrefixIndex x n) : Set ℕ)).Finite :=
    (Finset.range (d + 1)).finite_toSet.biUnion
      (fun j _ => (justSourceBlock (binaryPrefixIndex x j)).finite_toSet)
  apply hfin.subset
  rintro m ⟨⟨n,hn⟩,⟨k,hk⟩⟩
  have he : binaryPrefixIndex x n = binaryPrefixIndex y k := by
    by_contra h
    exact Finset.disjoint_left.mp (justSourceBlock_pairwise h) hn hk
  have hnd : n ≤ d := by
    by_contra h
    exact hd ((equal_binaryPrefixIndex_r10 he).2 d (Nat.lt_of_not_ge h))
  exact Set.mem_iUnion₂.mpr ⟨n,Finset.mem_range.mpr (Nat.lt_succ_of_le hnd),hn⟩

theorem LongBlockLarge.infinite_set {A : Set ℕ} (hA : LongBlockLarge A) : A.Infinite := by
  classical
  intro hf
  obtain ⟨N,hN⟩ :=
    eventually_disjoint_finset_of_pairwise justSourceBlock justSourceBlock_pairwise hf.toFinset
  obtain ⟨i,hi,hA'⟩ := hA.exists_block_from_index N
  obtain ⟨m,hm⟩ : (justSourceBlock i).Nonempty :=
    Finset.card_pos.mp ((Nat.zero_le i).trans_lt (justSourceBlock_card_growth i))
  have hfin : m ∈ hf.toFinset := by simpa using hA' hm
  exact Finset.disjoint_left.mp (hN i hi) hm hfin

theorem branchLargeSet_injective : Function.Injective branchLargeSet := by
  intro x y he
  by_contra hn
  have hfin := branchLargeSet_almost_disjoint hn
  rw [← he, Set.inter_self] at hfin
  exact (branchLargeSet_large x).infinite_set hfin

private theorem not_countable_bool_profiles : ¬ Countable (ℕ → Bool) := by
  classical
  intro hct
  letI := hct
  obtain ⟨f,hf⟩ := exists_injective_nat (ℕ → Bool)
  let e (n : ℕ) : ℕ → Bool := if h : ∃ x, f x = n then Classical.choose h else fun _ => false
  have hleft (x : ℕ → Bool) : e (f x) = x := by
    have h : ∃ y, f y = f x := ⟨x,rfl⟩
    simpa only [e,dite_eq_left h] using hf (Classical.choose_spec h)
  let y (n : ℕ) := !(e n n)
  have hc : e (f y) (f y) = !(e (f y) (f y)) := congrFun (hleft y) (f y)
  cases eq : e (f y) (f y) <;> simp [eq] at hc

theorem branchLargeSet_range_uncountable : ¬ (Set.range branchLargeSet).Countable := by
  classical
  intro h
  haveI := h.to_subtype
  have hi : Function.Injective (fun x : ℕ → Bool =>
      (⟨branchLargeSet x,⟨x,rfl⟩⟩ : ↥(Set.range branchLargeSet))) := by
    intro x y hxy
    exact branchLargeSet_injective (congrArg Subtype.val hxy)
  exact not_countable_bool_profiles (hi.countable)

theorem uncountably_many_almost_disjoint_large_domains :
    ∃ A : Set (Set ℕ), ¬ A.Countable ∧ (∀ a ∈ A, LongBlockLarge a) ∧
      ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a ∩ b).Finite := by
  classical
  refine ⟨Set.range branchLargeSet,branchLargeSet_range_uncountable,?_,?_⟩
  · rintro _ ⟨x,rfl⟩
    exact branchLargeSet_large x
  · rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ h
    exact branchLargeSet_almost_disjoint (fun hxy => h (congrArg branchLargeSet hxy))

end

end JSP000933
