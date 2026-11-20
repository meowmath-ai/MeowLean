import JSP000933OpenColor

open Filter
open scoped BigOperators Topology

namespace JSP000933

noncomputable section

def PrefixTailBound (f : EUWeight) (X : Set ℕ) (r : ℝ) : Prop :=
  ∃ N : ℕ, ∀ p ≥ N, weightedSetDensity f.weight X p ≤ r

theorem xorSet_triangle_subset_r14 (A B C : Set ℕ) :
    xorSet A C ⊆ xorSet A B ∪ xorSet B C := by
  intro m hm
  simp only [xorSet,Set.mem_union,Set.mem_sdiff] at hm ⊢
  tauto

theorem xorSet_comm_r14 (A B : Set ℕ) : xorSet A B = xorSet B A := by
  unfold xorSet
  exact Set.union_comm _ _

theorem PrefixTailBound.xor_triangle {f : EUWeight} {A B C : Set ℕ} {r s : ℝ}
    (hA : PrefixTailBound f (xorSet A B) r) (hB : PrefixTailBound f (xorSet B C) s) :
    PrefixTailBound f (xorSet A C) (r+s) := by
  obtain ⟨N,hN⟩ := hA
  obtain ⟨M,hM⟩ := hB
  refine ⟨max N M,fun p hp => ?_⟩
  exact ((weightedSetDensity_mono f.weight f.nonneg (xorSet_triangle_subset_r14 A B C) p).trans
    (weightedSetDensity_union_le f.weight f.nonneg _ _ p)).trans
      (add_le_add (hN p ((le_max_left N M).trans hp)) (hM p ((le_max_right N M).trans hp)))

theorem PrefixTailBound.of_null_union_small {f : EUWeight} {X U V : Set ℕ} {ε : ℝ}
    (hX : X ⊆ U ∪ V) (hU : WeightedNull f.weight U) (hV : V ∈ euPrefixSmall f ε)
    (hε : 0 < ε) : PrefixTailBound f X (ε + ε) := by
  obtain ⟨N,hN⟩ := hU ε hε
  refine ⟨N,fun p hp => ?_⟩
  exact ((weightedSetDensity_mono f.weight f.nonneg hX p).trans
    (weightedSetDensity_union_le f.weight f.nonneg U V p)).trans (add_le_add (hN p hp) (hV p))

private theorem rate_pos_r14 (i : ℕ) : 0 < blockErrorRate i := by
  unfold blockErrorRate
  positivity

private theorem rate_succ_r14 (i : ℕ) : blockErrorRate (i+1) = blockErrorRate i / 2 := by
  unfold blockErrorRate
  rw [pow_succ] <;> ring

private theorem finite_tail_error_sum_r14 (J p : ℕ) :
    (∑ i ∈ Finset.range p, (blockErrorRate (J+i) + blockErrorRate (J+i))) ≤ 4 * blockErrorRate J := by
  have h (l : ℕ) :
      (∑ i ∈ Finset.range l, (blockErrorRate (J+i) + blockErrorRate (J+i))) =
        4 * (blockErrorRate J - blockErrorRate (J+l)) := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Finset.sum_range_succ,ih,show J + (l+1) = J+l+1 by omega,rate_succ_r14]
      ring
  rw [h]
  linarith only [(rate_pos_r14 (J+p)).le]

private theorem weightedDensity_biUnion_range_le_r14 (f : EUWeight) (D : ℕ → Set ℕ)
    (q p : ℕ) :
    weightedSetDensity f.weight (⋃ i ∈ (Finset.range q : Set ℕ), D i) p ≤
      ∑ i ∈ Finset.range q, weightedSetDensity f.weight (D i) p := by
  induction q with
  | zero =>
    have hz : (⋃ i ∈ (Finset.range 0 : Set ℕ), D i) = ∅ := by simp
    rw [hz]
    simp [weightedSetDensity]
  | succ q ih =>
    have he : (⋃ i ∈ (Finset.range (q+1) : Set ℕ), D i) =
        (⋃ i ∈ (Finset.range q : Set ℕ), D i) ∪ D q := by
      ext m
      simp only [Set.mem_iUnion,Finset.mem_coe,Finset.mem_range,Set.mem_union]
      constructor
      · rintro ⟨i,hi,hm⟩
        by_cases h : i < q
        · exact Or.inl ⟨i,h,hm⟩
        · have he : i = q := by omega
          subst i
          exact Or.inr hm
      · rintro (⟨i,hi,hm⟩ | hm)
        · exact ⟨i,hi.trans (Nat.lt_succ_self _),hm⟩
        · exact ⟨q,Nat.lt_succ_self _,hm⟩
    rw [he,Finset.sum_range_succ]
    exact (weightedSetDensity_union_le f.weight f.nonneg _ _ p).trans (add_le_add ih le_rfl)

private theorem weightedDensity_empty_prefix_of_notMem_r14 (f : EUWeight) {S : Set ℕ} (p : ℕ)
    (h : ∀ i < p, i ∉ S) : weightedSetDensity f.weight S p = 0 := by
  have hz : restrictSet (Finset.range p) S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    obtain ⟨hmp,hmS⟩ := mem_restrictSet.mp hm
    exact h m (Finset.mem_range.mp hmp) hmS
  simp [weightedSetDensity,hz]

private theorem tailPiece_prefix_bound_r14 (f : EUWeight) {S : Set ℕ} {a : ℝ} (ha : 0 ≤ a)
    {N : ℕ} (hN : ∀ p ≥ N, weightedSetDensity f.weight S p ≤ a) :
    ∀ p, weightedSetDensity f.weight (S \ Set.Iio N) p ≤ a := by
  intro p
  by_cases hp : N ≤ p
  · exact (weightedSetDensity_mono f.weight f.nonneg (show S \ Set.Iio N ⊆ S from fun _ hm => hm.1) p).trans (hN p hp)
  · rw [weightedDensity_empty_prefix_of_notMem_r14]
    · exact ha
    · intro i hi hiS
      exact hiS.2 (hi.trans (Nat.lt_of_not_ge hp))

private theorem xor_of_sequence_has_step_r14 (S : ℕ → Set ℕ) (J m : ℕ) :
    ∀ d, m ∈ xorSet (S J) (S (J+d)) →
      ∃ i < d, m ∈ xorSet (S (J+i)) (S (J+i+1)) := by
  intro d
  induction d with
  | zero =>
    intro hm
    simp [xorSet] at hm
  | succ d ih =>
    intro hm
    have h := xorSet_triangle_subset_r14 (S J) (S (J+d)) (S (J+(d+1))) hm
    rcases h with h | h
    · obtain ⟨i,hi,hm⟩ := ih h
      exact ⟨i,hi.trans (Nat.lt_succ_self _),hm⟩
    · exact ⟨d,Nat.lt_succ_self _,by simpa only [Nat.add_assoc] using h⟩

theorem weightedNull_hybrid_of_dyadic_approx
    (f : EUWeight) (S : ℕ → Set ℕ) (X : Set ℕ) (cut band : ℕ → ℕ)
    (hcut : StrictMono cut) (hcut0 : cut 0 = 0)
    (hband : ∀ m : ℕ, cut (band m) ≤ m ∧ m < cut (band m + 1))
    (hgap : ∀ j p : ℕ, cut (j+1) ≤ p →
      weightedSetDensity f.weight (xorSet (S j) (S (j+1))) p ≤ blockErrorRate j + blockErrorRate j)
    (hclose : ∀ j, PrefixTailBound f (xorSet (S j) X) (blockErrorRate j)) :
    WeightedNull f.weight (xorSet {m | m ∈ S (band m)} X) := by
  let H : Set ℕ := {m | m ∈ S (band m)}
  let D (j : ℕ) : Set ℕ := xorSet (S j) (S (j+1)) \ Set.Iio (cut (j+1))
  have hD (j p : ℕ) :
      weightedSetDensity f.weight (D j) p ≤ blockErrorRate j + blockErrorRate j :=
    tailPiece_prefix_bound_r14 f (add_nonneg (rate_pos_r14 j).le (rate_pos_r14 j).le) (hgap j) p
  have hcut_lower (j : ℕ) : j ≤ cut j := by
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have hs : cut j < cut (j + 1) := hcut (Nat.lt_succ_self j)
      change j + 1 ≤ cut (j + 1)
      omega
  have hstepCover (J p : ℕ) :
      restrictSet (Finset.range p) (xorSet H (S J)) ⊆
        restrictSet (Finset.range p)
          ((Set.Iio (cut J) : Set ℕ) ∪ ⋃ i ∈ (Finset.range p : Set ℕ), D (J+i)) := by
    intro m hm
    obtain ⟨hmp,hmD⟩ := mem_restrictSet.mp hm
    refine mem_restrictSet.mpr ⟨hmp,?_⟩
    by_cases he : m < cut J
    · exact Or.inl he
    · have hJ : J ≤ band m := by
        by_contra hn
        have hnext : band m + 1 ≤ J := Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
        exact he ((hband m).2.trans_le (hcut.monotone hnext))
      have hD' : m ∈ xorSet (S J) (S (band m)) := by
        rw [xorSet_comm_r14]
        exact hmD
      have hdelta : J + (band m - J) = band m := Nat.add_sub_of_le hJ
      have hx : m ∈ xorSet (S J) (S (J+(band m-J))) := by simpa only [hdelta] using hD'
      obtain ⟨i,hi,hmS⟩ := xor_of_sequence_has_step_r14 S J m (band m-J) hx
      have hil : J+i+1 ≤ band m := by omega
      have hcutm : cut (J+i+1) ≤ m := (hcut.monotone hil).trans (hband m).1
      have hip : i < p := by
        have hh := (hcut_lower (J+i+1)).trans hcutm
        have hm' := Finset.mem_range.mp hmp
        omega
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨i,Finset.mem_range.mpr hip,hmS,by exact Nat.not_lt_of_ge hcutm⟩)
  have hbound (J p : ℕ) : weightedSetDensity f.weight (xorSet H (S J)) p ≤
      weightedSetDensity f.weight (Set.Iio (cut J)) p + 4 * blockErrorRate J := by
    have hcmp : weightedSetDensity f.weight (xorSet H (S J)) p ≤
        weightedSetDensity f.weight ((Set.Iio (cut J) : Set ℕ) ∪
          ⋃ i ∈ (Finset.range p : Set ℕ), D (J+i)) p := by
      unfold weightedSetDensity
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg (hstepCover J p) (fun m _ _ => f.nonneg m))
        (Finset.sum_nonneg (fun m _ => f.nonneg m))
    refine (hcmp.trans (weightedSetDensity_union_le f.weight f.nonneg _ _ p)).trans ?_
    apply add_le_add le_rfl
    exact ((weightedDensity_biUnion_range_le_r14 f (fun i => D (J+i)) p p).trans
      (Finset.sum_le_sum (fun i _ => hD (J+i) p))).trans (finite_tail_error_sum_r14 J p)
  intro ε hε
  have hlim : Tendsto blockErrorRate atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨J,hJ⟩ := Metric.tendsto_atTop.mp hlim (ε / 12) (by positivity)
  have hr := hJ J le_rfl
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (rate_pos_r14 J).le] at hr
  have hfinite : WeightedNull f.weight (Set.Iio (cut J)) := by
    have he : Set.Iio (cut J) = (Finset.range (cut J) : Set ℕ) := by
      ext m
      simp
    rw [he]
    exact weightedNull_finset_of_eu f _
  obtain ⟨N,hN⟩ := hfinite (ε / 2) (by positivity)
  obtain ⟨M,hM⟩ := hclose J
  refine ⟨max N M,fun p hp => ?_⟩
  have he := hN p ((le_max_left N M).trans hp)
  have hm := hM p ((le_max_right N M).trans hp)
  have hh := hbound J p
  have hsub := weightedSetDensity_mono f.weight f.nonneg (xorSet_triangle_subset_r14 H (S J) X) p
  have hu := weightedSetDensity_union_le f.weight f.nonneg (xorSet H (S J)) (xorSet (S J) X) p
  change weightedSetDensity f.weight (xorSet H X) p ≤ ε
  refine (hsub.trans hu).trans ((add_le_add hh hm).trans ?_)
  calc
    _ ≤ ε / 2 + 4 * (ε / 12) + ε / 12 :=
      add_le_add (add_le_add he (mul_le_mul_of_nonneg_left hr.le (by norm_num))) hr.le
    _ ≤ ε := by linarith

theorem successive_gapBound_of_dyadic_approx (f : EUWeight) (S : ℕ → Set ℕ) (X : Set ℕ)
    (hclose : ∀ j, PrefixTailBound f (xorSet (S j) X) (blockErrorRate j)) :
    ∀ j, PrefixTailBound f (xorSet (S j) (S (j+1))) (blockErrorRate j + blockErrorRate j) := by
  intro j
  have h' : PrefixTailBound f (xorSet X (S (j+1))) (blockErrorRate (j+1)) := by
    simpa only [xorSet_comm_r14 X (S (j+1))] using hclose (j+1)
  obtain ⟨N,hN⟩ := (hclose j).xor_triangle h'
  refine ⟨N,fun p hp => (hN p hp).trans ?_⟩
  have hrate : blockErrorRate (j+1) ≤ blockErrorRate j := by
    rw [rate_succ_r14]
    linarith only [rate_pos_r14 j]
  exact add_le_add le_rfl hrate

def leastGapCut (f : EUWeight) (S : ℕ → Set ℕ)
    (hgap : ∀ j, PrefixTailBound f (xorSet (S j) (S (j+1))) (blockErrorRate j + blockErrorRate j))
    (j : ℕ) : ℕ := by
  classical
  exact Nat.find (hgap j)

theorem leastGapCut_le_iff (f : EUWeight) (S : ℕ → Set ℕ)
    (hgap : ∀ j, PrefixTailBound f (xorSet (S j) (S (j+1))) (blockErrorRate j + blockErrorRate j))
    (j t : ℕ) :
    leastGapCut f S hgap j ≤ t ↔
      ∀ p ≥ t, weightedSetDensity f.weight (xorSet (S j) (S (j+1))) p ≤
        blockErrorRate j + blockErrorRate j := by
  classical
  unfold leastGapCut
  constructor
  · intro h p hp
    exact Nat.find_spec (hgap j) p (h.trans hp)
  · intro ht
    exact Nat.find_min' (hgap j) ht

def hybridCut (f : EUWeight) (S : ℕ → Set ℕ)
    (hgap : ∀ j, PrefixTailBound f (xorSet (S j) (S (j+1))) (blockErrorRate j + blockErrorRate j)) :
    ℕ → ℕ
  | 0 => 0
  | j+1 => max (hybridCut f S hgap j + 1) (leastGapCut f S hgap j)

theorem hybridCut_zero (f : EUWeight) (S : ℕ → Set ℕ) (hgap) :
    hybridCut f S hgap 0 = 0 := rfl

theorem hybridCut_succ (f : EUWeight) (S : ℕ → Set ℕ) (hgap) (j : ℕ) :
    hybridCut f S hgap (j+1) = max (hybridCut f S hgap j + 1) (leastGapCut f S hgap j) := rfl

theorem hybridCut_strictMono (f : EUWeight) (S : ℕ → Set ℕ) (hgap) :
    StrictMono (hybridCut f S hgap) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [hybridCut_succ]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem hybridCut_gap_bound (f : EUWeight) (S : ℕ → Set ℕ) (hgap) (j p : ℕ)
    (h : hybridCut f S hgap (j+1) ≤ p) :
    weightedSetDensity f.weight (xorSet (S j) (S (j+1))) p ≤ blockErrorRate j + blockErrorRate j := by
  rw [hybridCut_succ] at h
  exact (leastGapCut_le_iff f S hgap j (leastGapCut f S hgap j)).mp le_rfl p
    ((le_max_right _ _).trans h)

private theorem exceeds_natural_cut_r14 (cut : ℕ → ℕ) (hc : StrictMono cut) (m : ℕ) :
    ∃ i, m < cut i := by
  have h (i : ℕ) : i ≤ cut i := by
    induction i with
    | zero => exact Nat.zero_le _
    | succ i hi =>
      have hd : cut i < cut (i + 1) := hc (Nat.lt_succ_self i)
      change i + 1 ≤ cut (i + 1)
      omega
  exact ⟨m+1,(Nat.lt_succ_self m).trans_le (h (m+1))⟩

def hybridBand (cut : ℕ → ℕ) (hc : StrictMono cut) (m : ℕ) : ℕ :=
  Nat.find (exceeds_natural_cut_r14 cut hc m) - 1

theorem hybridBand_spec (cut : ℕ → ℕ) (hc : StrictMono cut) (h0 : cut 0 = 0) (m : ℕ) :
    cut (hybridBand cut hc m) ≤ m ∧ m < cut (hybridBand cut hc m + 1) := by
  let ex := exceeds_natural_cut_r14 cut hc m
  let N := Nat.find ex
  have hN : m < cut N := Nat.find_spec ex
  have hn : N ≠ 0 := by
    intro h
    rw [h,h0] at hN
    omega
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hpre : i < Nat.find ex := by
    change i < N
    omega
  have hL : cut i ≤ m := le_of_not_gt (Nat.find_min ex hpre)
  have hb : hybridBand cut hc m = i := by
    change N - 1 = i
    omega
  rw [hb]
  exact ⟨hL,by simpa only [hi] using hN⟩

theorem hybridBand_eq_iff (cut : ℕ → ℕ) (hc : StrictMono cut) (h0 : cut 0 = 0)
    (m j : ℕ) : hybridBand cut hc m = j ↔ cut j ≤ m ∧ m < cut (j+1) := by
  have h := hybridBand_spec cut hc h0 m
  constructor
  · intro he
    simpa only [he] using h
  · intro hj
    rcases lt_trichotomy (hybridBand cut hc m) j with hh | hh | hh
    · have hle : hybridBand cut hc m + 1 ≤ j := Nat.succ_le_of_lt hh
      exact False.elim ((not_lt_of_ge ((hc.monotone hle).trans hj.1)) h.2)
    · exact hh
    · have hle : j+1 ≤ hybridBand cut hc m := Nat.succ_le_of_lt hh
      exact False.elim ((not_lt_of_ge ((hc.monotone hle).trans h.1)) hj.2)

def canonicalSetHybrid (f : EUWeight) (S : ℕ → Set ℕ)
    (hgap : ∀ j, PrefixTailBound f (xorSet (S j) (S (j + 1))) (blockErrorRate j + blockErrorRate j)) : Set ℕ :=
  {m | m ∈ S (hybridBand (hybridCut f S hgap) (hybridCut_strictMono f S hgap) m)}

theorem canonicalSetHybrid_exact (f : EUWeight) (S : ℕ → Set ℕ) (X : Set ℕ)
    (hgap : ∀ j, PrefixTailBound f (xorSet (S j) (S (j + 1))) (blockErrorRate j + blockErrorRate j))
    (hclose : ∀ j, PrefixTailBound f (xorSet (S j) X) (blockErrorRate j)) :
    WeightedNull f.weight (xorSet (canonicalSetHybrid f S hgap) X) := by
  apply weightedNull_hybrid_of_dyadic_approx f S X (hybridCut f S hgap)
    (hybridBand (hybridCut f S hgap) (hybridCut_strictMono f S hgap))
    (hybridCut_strictMono f S hgap) (hybridCut_zero f S hgap)
  · exact hybridBand_spec _ _ (hybridCut_zero f S hgap)
  · exact hybridCut_gap_bound f S hgap
  · exact hclose

end

end JSP000933
