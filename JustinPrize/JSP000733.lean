import Mathlib


open Filter
open scoped BigOperators Topology

set_option autoImplicit false

namespace JSP000733

def subsetSum (S : Finset ℕ) : ℕ := ∑ x ∈ S, x

def nonemptySums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter fun S => S.Nonempty).image subsetSum

def PrimitiveSums (A : Finset ℕ) : Prop :=
  ∀ x ∈ nonemptySums A, ∀ y ∈ nonemptySums A, x ∣ y → x = y

def Admissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ PrimitiveSums A

noncomputable def maximumSize (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).powerset.filter PrimitiveSums).sup Finset.card

private theorem mem_nonemptySums {A S : Finset ℕ} (hS : S ⊆ A) (hne : S.Nonempty) :
    subsetSum S ∈ nonemptySums A := by
  exact Finset.mem_image.mpr
    ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hne⟩, rfl⟩

private theorem subsetSum_pos {A S : Finset ℕ}
    (hpos : ∀ a ∈ A, 0 < a) (hS : S ⊆ A) (hne : S.Nonempty) :
    0 < subsetSum S := by
  exact Finset.sum_pos (fun a ha => hpos a (hS ha)) hne

theorem card_le_maximumSize {N : ℕ} {A : Finset ℕ} (hA : Admissible N A) :
    A.card ≤ maximumSize N := by
  classical
  unfold maximumSize
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hA.1, hA.2⟩)

theorem maximumSize_attained (N : ℕ) :
    ∃ A : Finset ℕ, Admissible N A ∧ A.card = maximumSize N := by
  classical
  let F := (Finset.Icc 1 N).powerset.filter PrimitiveSums
  have hempty : (∅ : Finset ℕ) ∈ F := by
    simp [F, PrimitiveSums, nonemptySums]
  obtain ⟨A, hA, he⟩ := Finset.exists_mem_eq_sup F ⟨∅, hempty⟩ Finset.card
  obtain ⟨hA₁, hA₂⟩ := Finset.mem_filter.mp hA
  exact ⟨A, ⟨Finset.mem_powerset.mp hA₁, hA₂⟩, he.symm⟩

theorem injective_subset_sums {N : ℕ} {A : Finset ℕ} (hA : Admissible N A) :
    Set.InjOn subsetSum (↑A.powerset : Set (Finset ℕ)) := by
  classical
  intro S hS T hT hsum
  have hSA : S ⊆ A := Finset.mem_powerset.mp hS
  have hTA : T ⊆ A := Finset.mem_powerset.mp hT
  have hpos (a : ℕ) (ha : a ∈ A) : 0 < a := by
    have h := (Finset.mem_Icc.mp (hA.1 ha)).1
    omega
  let P := S \ T
  let Q := T \ S
  have hPA : P ⊆ A := fun a ha => hSA (Finset.mem_sdiff.mp ha).1
  have hQA : Q ⊆ A := fun a ha => hTA (Finset.mem_sdiff.mp ha).1
  have hs : subsetSum P + subsetSum (S ∩ T) = subsetSum S := by
    have hi : S ∩ T ⊆ S := Finset.inter_subset_left
    simpa only [P, subsetSum, Finset.sdiff_inter_self_left] using
      (Finset.sum_sdiff (f := fun a : ℕ => a) hi)
  have ht : subsetSum Q + subsetSum (S ∩ T) = subsetSum T := by
    have hi : S ∩ T ⊆ T := Finset.inter_subset_right
    simpa only [Q, subsetSum, Finset.sdiff_inter_self_right] using
      (Finset.sum_sdiff (f := fun a : ℕ => a) hi)
  have hpq : subsetSum P = subsetSum Q := by omega
  by_contra hne
  have hsome : P.Nonempty ∨ Q.Nonempty := by
    by_contra hh
    have hP : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun hp => hh (Or.inl hp))
    have hQ : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun hq => hh (Or.inr hq))
    have hST : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hP
    have hTS : T ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp hQ
    apply hne
    exact Finset.ext fun _ => ⟨fun h => hST h, fun h => hTS h⟩
  have hv : 0 < subsetSum P := by
    rcases hsome with hp | hq
    · exact subsetSum_pos hpos hPA hp
    · rw [hpq]
      exact subsetSum_pos hpos hQA hq
  have hPne : P.Nonempty := by
    by_contra hn
    simp [subsetSum, Finset.not_nonempty_iff_eq_empty.mp hn] at hv
  have hPQ : Disjoint P Q := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hUA : P ∪ Q ⊆ A := Finset.union_subset hPA hQA
  have hUne : (P ∪ Q).Nonempty := by
    obtain ⟨a, ha⟩ := hPne
    exact ⟨a, Finset.mem_union.mpr (Or.inl ha)⟩
  have hu : subsetSum (P ∪ Q) = subsetSum P * 2 := by
    unfold subsetSum
    rw [Finset.sum_union hPQ]
    change subsetSum P + subsetSum Q = subsetSum P * 2
    omega
  have he := hA.2 _ (mem_nonemptySums hPA hPne) _
    (mem_nonemptySums hUA hUne) ⟨2, hu⟩
  omega

theorem finite_upper {N : ℕ} {A : Finset ℕ} (hA : Admissible N A) :
    2 ^ A.card ≤ A.card * N + 1 := by
  classical
  have hcard : (A.powerset.image subsetSum).card = 2 ^ A.card := by
    rw [Finset.card_image_of_injOn (injective_subset_sums hA), Finset.card_powerset]
  have hsub : A.powerset.image subsetSum ⊆ Finset.range (A.card * N + 1) := by
    intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    have hSA := Finset.mem_powerset.mp hS
    have hsum : subsetSum S ≤ S.card * N := by
      calc
        _ ≤ ∑ a ∈ S, N := Finset.sum_le_sum (fun a ha => (Finset.mem_Icc.mp (hA.1 (hSA ha))).2)
        _ = _ := Finset.sum_const_nat (fun _ _ => rfl)
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (hsum.trans (Nat.mul_le_mul_right N (Finset.card_le_card hSA)))
  simpa only [hcard, Finset.card_range] using Finset.card_le_card hsub

private def bitValue (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ i

private theorem bitValue_range (m : ℕ) : bitValue (Finset.range m) + 1 = 2 ^ m := by
  induction m with
  | zero => simp [bitValue]
  | succ m ih =>
    change (∑ i ∈ Finset.range (m + 1), (2 : ℕ) ^ i) + 1 = 2 ^ (m + 1)
    rw [Finset.sum_range_succ, pow_succ]
    change bitValue (Finset.range m) + 2 ^ m + 1 = 2 ^ m * 2
    omega

private theorem bitValue_lt {m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range m) :
    bitValue S < 2 ^ m := by
  have hh : bitValue S ≤ bitValue (Finset.range m) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (by intros; exact Nat.zero_le _)
  have hh' := bitValue_range m
  omega

private def floorMass (m x : ℕ) : ℕ :=
  ∑ j ∈ Finset.range m, x / 2 ^ (j + 1)

private theorem floorMass_succ (m x : ℕ) :
    floorMass (m + 1) x = floorMass m x + x / 2 ^ (m + 1) := by
  exact Finset.sum_range_succ (fun j => x / 2 ^ (j + 1)) m

private theorem floorMass_shift (m x q : ℕ) :
    floorMass m (x + 2 ^ m * q) + q = floorMass m x + 2 ^ m * q := by
  induction m generalizing x q with
  | zero => simp [floorMass]
  | succ m ih =>
    change floorMass (m + 1) (x + 2 ^ (m + 1) * q) + q =
      floorMass (m + 1) x + 2 ^ (m + 1) * q
    rw [floorMass_succ m (x + 2 ^ (m + 1) * q), floorMass_succ m x]
    have hx : x + 2 ^ (m + 1) * q = x + 2 ^ m * (2 * q) := by
      rw [pow_succ]
      ring
    rw [Nat.add_mul_div_left x q (show 0 < (2 : ℕ) ^ (m + 1) by positivity)]
    have he := ih x (2 * q)
    rw [← hx] at he
    have hpow : 2 ^ m * (2 * q) = 2 ^ (m + 1) * q := by
      rw [pow_succ]
      ring
    rw [hpow] at he
    omega

private theorem floorMass_bitValue (m : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range m) :
    floorMass m (bitValue S) + S.card = bitValue S := by
  classical
  induction m generalizing S with
  | zero =>
    have h : S = ∅ := Finset.subset_empty.mp (by simpa using hS)
    subst S
    simp [floorMass, bitValue]
  | succ m ih =>
    change floorMass (m + 1) (bitValue S) + S.card = bitValue S
    have hb : bitValue S < 2 ^ (m + 1) := bitValue_lt hS
    rw [floorMass_succ, Nat.div_eq_of_lt hb, add_zero]
    by_cases hm : m ∈ S
    · let T := S.erase m
      have hT : T ⊆ Finset.range m := by
        intro i hi
        have h₁ := Finset.mem_erase.mp hi
        have h₂ := Finset.mem_range.mp (hS h₁.2)
        exact Finset.mem_range.mpr (by omega)
      have hc : T.card + 1 = S.card := by
        have h := Finset.card_erase_of_mem hm
        change T.card = S.card - 1 at h
        have hp : 0 < S.card := Finset.card_pos.mpr ⟨m, hm⟩
        omega
      have he : bitValue T + 2 ^ m = bitValue S :=
        Finset.sum_erase_add S (fun i => 2 ^ i) hm
      have hrec := ih T hT
      have hshift := floorMass_shift m (bitValue T) 1
      rw [mul_one, he] at hshift
      omega
    · apply ih S
      intro i hi
      have h₁ := Finset.mem_range.mp (hS hi)
      have h₂ : i ≠ m := fun h => hm (h ▸ hi)
      exact Finset.mem_range.mpr (by omega)

private theorem floorMass_mul_strict {m x c : ℕ}
    (hx : 0 < x) (hxm : x < 2 ^ m) (hc : 2 ≤ c) :
    c * floorMass m x < floorMass m (c * x) := by
  let j := Nat.log 2 x
  have hj₁ : 2 ^ j ≤ x := Nat.pow_log_le_self 2 hx.ne'
  have hj₂ : x < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  have hjm : j < m := by
    by_contra! hh
    exact (not_le_of_gt hxm)
      ((pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hh).trans hj₁)
  have hcarry : 0 < c * x / 2 ^ (j + 1) := by
    change 1 ≤ c * x / 2 ^ (j + 1)
    apply (Nat.le_div_iff_mul_le (show 0 < (2 : ℕ) ^ (j + 1) by positivity)).2
    rw [one_mul, pow_succ]
    calc
      2 ^ j * 2 = 2 * 2 ^ j := Nat.mul_comm _ _
      _ ≤ 2 * x := Nat.mul_le_mul_left 2 hj₁
      _ ≤ c * x := Nat.mul_le_mul_right x hc
  unfold floorMass
  rw [Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_range.mpr hjm, ?_⟩
  · apply (Nat.le_div_iff_mul_le (show 0 < (2 : ℕ) ^ (i + 1) by positivity)).mpr
    calc
      _ = c * (x / 2 ^ (i + 1) * 2 ^ (i + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left c (Nat.div_mul_le_self x _)
  · rwa [Nat.div_eq_of_lt hj₂, mul_zero]


private theorem bitValue_pos {S : Finset ℕ} (hS : S.Nonempty) : 0 < bitValue S := by
  exact Finset.sum_pos (fun i _ => by positivity) hS

private def constructionTerm (m i : ℕ) : ℕ := 2 ^ m - 2 ^ i

private def indexedSum (m : ℕ) (S : Finset ℕ) : ℕ := ∑ i ∈ S, constructionTerm m i

private theorem constructionTerm_pos {m i : ℕ} (hi : i < m) :
    0 < constructionTerm m i := by
  unfold constructionTerm
  exact Nat.sub_pos_of_lt (pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 2) hi)

private theorem indexedSum_pos {m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range m) (hne : S.Nonempty) : 0 < indexedSum m S := by
  exact Finset.sum_pos (fun i hi => constructionTerm_pos (Finset.mem_range.mp (hS hi))) hne

private theorem indexedSum_add_bits {m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range m) : indexedSum m S + bitValue S = 2 ^ m * S.card := by
  unfold indexedSum bitValue
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i ∈ S, (2 : ℕ) ^ m := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Nat.sub_add_cancel
        (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Finset.mem_range.mp (hS hi)).le)
    _ = _ := (Finset.sum_const_nat (fun _ _ => rfl)).trans (Nat.mul_comm _ _)

private theorem indexed_eq_of_dvd {m : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ Finset.range m) (hT : T ⊆ Finset.range m)
    (hSpos : S.Nonempty) (hTpos : T.Nonempty)
    (hdvd : indexedSum m S ∣ indexedSum m T) : indexedSum m S = indexedSum m T := by
  obtain ⟨c, hc⟩ := hdvd
  have hc₀ : c ≠ 0 := by
    intro h
    have ht := indexedSum_pos hT hTpos
    rw [hc, h, mul_zero] at ht
    exact (Nat.lt_irrefl 0) ht
  by_cases h₁ : c = 1
  · simpa only [h₁, mul_one] using hc.symm
  have hc₂ : 2 ≤ c := by omega
  have hs := indexedSum_add_bits hS
  have ht := indexedSum_add_bits hT
  have hm : indexedSum m T + bitValue S * c = (2 ^ m * S.card) * c := by
    have hh := congrArg (fun z : ℕ => z * c) hs
    change (indexedSum m S + bitValue S) * c = (2 ^ m * S.card) * c at hh
    rwa [add_mul, ← hc] at hh
  have he : c * bitValue S + 2 ^ m * T.card = bitValue T + 2 ^ m * (c * S.card) := by
    calc
      _ = (indexedSum m T + bitValue S * c) + bitValue T := by rw [← ht]; ring
      _ = _ := by rw [hm]; ring
  have hf := congrArg (floorMass m) he
  change floorMass m (c * bitValue S + 2 ^ m * T.card) =
    floorMass m (bitValue T + 2 ^ m * (c * S.card)) at hf
  have hfs := floorMass_shift m (c * bitValue S) T.card
  have hft := floorMass_shift m (bitValue T) (c * S.card)
  have hdt := floorMass_bitValue m T hT
  have hds := congrArg (fun z : ℕ => c * z) (floorMass_bitValue m S hS)
  change c * (floorMass m (bitValue S) + S.card) = c * bitValue S at hds
  rw [mul_add] at hds
  have hstrict := floorMass_mul_strict (bitValue_pos hSpos) (bitValue_lt hS) hc₂
  omega

private def construction (m : ℕ) : Finset ℕ :=
  (Finset.range m).image (constructionTerm m)

private theorem constructionTerm_injOn (m : ℕ) :
    Set.InjOn (constructionTerm m) (↑(Finset.range m) : Set ℕ) := by
  intro i hi j hj hij
  have hi' : i < m := Finset.mem_range.mp hi
  have hj' : j < m := Finset.mem_range.mp hj
  have hi₂ := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hi'.le
  have hj₂ := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hj'.le
  change 2 ^ m - 2 ^ i = 2 ^ m - 2 ^ j at hij
  have hp : (2 : ℕ) ^ i = 2 ^ j := by omega
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim ((ne_of_lt (pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 2) h)) hp)
  · exact h
  · exact False.elim ((ne_of_gt (pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 2) h)) hp)

private theorem construction_card (m : ℕ) : (construction m).card = m := by
  unfold construction
  rw [Finset.card_image_of_injOn (constructionTerm_injOn m), Finset.card_range]

private theorem construction_reindex {m : ℕ} {U : Finset ℕ}
    (hU : U ⊆ construction m) (hUne : U.Nonempty) :
    ∃ S : Finset ℕ, S ⊆ Finset.range m ∧ S.Nonempty ∧ subsetSum U = indexedSum m S := by
  classical
  let I := (Finset.range m).filter fun i => constructionTerm m i ∈ U
  have hI : I ⊆ Finset.range m := Finset.filter_subset _ _
  have hIm : I.image (constructionTerm m) = U := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hU hx)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩, rfl⟩
  have hIne : I.Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    rw [← hIm] at hx
    obtain ⟨i, hi, _⟩ := Finset.mem_image.mp hx
    exact ⟨i, hi⟩
  have hInj : Set.InjOn (constructionTerm m) (↑I : Set ℕ) :=
    fun _ hi _ hj h => constructionTerm_injOn m (hI hi) (hI hj) h
  refine ⟨I, hI, hIne, ?_⟩
  rw [← hIm, subsetSum, indexedSum, Finset.sum_image hInj]

private theorem construction_primitive (m : ℕ) : PrimitiveSums (construction m) := by
  intro x hx y hy hxy
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨U', hU's, hU'ne, hU'e⟩ := construction_reindex
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1) (Finset.mem_filter.mp hU).2
  obtain ⟨V', hV's, hV'ne, hV'e⟩ := construction_reindex
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1) (Finset.mem_filter.mp hV).2
  rw [hU'e, hV'e] at hxy ⊢
  exact indexed_eq_of_dvd hU's hV's hU'ne hV'ne hxy

private theorem construction_admissible {m N : ℕ} (hmN : 2 ^ m ≤ N) :
    Admissible N (construction m) := by
  refine ⟨?_, construction_primitive m⟩
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  have hpos : 0 < constructionTerm m i := constructionTerm_pos (Finset.mem_range.mp hi)
  have hupper : constructionTerm m i ≤ N := (Nat.sub_le _ _).trans hmN
  exact Finset.mem_Icc.mpr ⟨by omega, hupper⟩

theorem lower_bound {N : ℕ} (hN : 0 < N) :
    Real.logb 2 (N : ℝ) - 1 < (maximumSize N : ℝ) := by
  let m := Nat.log 2 N
  have hpow : 2 ^ m ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have hle : m ≤ maximumSize N := by
    simpa only [construction_card] using card_le_maximumSize (construction_admissible hpow)
  have hf : Nat.floor (Real.logb 2 (N : ℝ)) = m := by
    simpa only [Nat.cast_ofNat] using Real.natFloor_logb_natCast 2 N
  have h := Nat.lt_floor_add_one (Real.logb 2 (N : ℝ))
  rw [hf] at h
  have hm' : (m : ℝ) ≤ (maximumSize N : ℝ) := by exact_mod_cast hle
  linarith only [h, hm']

private theorem eventually_large_logb (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, B < Real.logb 2 (N : ℝ) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp hcast
  exact hlog.eventually (eventually_gt_atTop B)

private theorem eventually_ratio_gt (u : ℝ) (hu : u < 1) :
    ∀ᶠ N : ℕ in atTop, u < (maximumSize N : ℝ) / Real.logb 2 (N : ℝ) := by
  have hu' : 0 < 1 - u := sub_pos.mpr hu
  filter_upwards [eventually_large_logb (max 0 (1 / (1 - u))),
    eventually_ge_atTop (1 : ℕ)] with N hLbig hN
  let L := Real.logb 2 (N : ℝ)
  have hL : 0 < L := lt_of_le_of_lt (le_max_left _ _) hLbig
  have hprod : 1 < L * (1 - u) :=
    (div_lt_iff₀ hu').1 (lt_of_le_of_lt (le_max_right _ _) hLbig)
  have hb : L - 1 < (maximumSize N : ℝ) := lower_bound (by omega : 0 < N)
  apply (lt_div_iff₀ hL).2
  nlinarith only [hprod, hb]

private theorem log_count_bound {N : ℕ} (hN : 0 < N) (hk : 0 < maximumSize N) :
    (maximumSize N : ℝ) * Real.log 2 ≤
      Real.log 2 + (Real.log (maximumSize N : ℝ) + Real.log (N : ℝ)) := by
  have hcountNat : (2 : ℕ) ^ maximumSize N ≤ maximumSize N * N + 1 := by
    obtain ⟨A, hA, hAc⟩ := maximumSize_attained N
    simpa only [hAc] using finite_upper hA
  let k := (maximumSize N : ℝ)
  have hcount : (2 : ℝ) ^ maximumSize N ≤ k * (N : ℝ) + 1 := by
    dsimp only [k]
    exact_mod_cast hcountNat
  have hn₁ : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hk₁ : 1 ≤ k := by
    dsimp only [k]
    exact_mod_cast (show 1 ≤ maximumSize N by omega)
  have hkN : 1 ≤ k * (N : ℝ) := by
    simpa only [one_mul] using mul_le_mul hk₁ hn₁ (by norm_num : (0 : ℝ) ≤ 1)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hk₁)
  have hnpos : 0 < (N : ℝ) := lt_of_lt_of_le (by norm_num) hn₁
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk₁
  have hb : (2 : ℝ) ^ maximumSize N ≤ 2 * (k * (N : ℝ)) := by linarith only [hcount, hkN]
  have hlog := Real.log_le_log (show 0 < (2 : ℝ) ^ maximumSize N by positivity) hb
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_ne_zero hkpos.ne' hnpos.ne'),
    Real.log_mul hkpos.ne' hnpos.ne'] at hlog
  exact hlog

private theorem eventually_ratio_lt (v : ℝ) (hv : 1 < v) :
    ∀ᶠ N : ℕ in atTop, (maximumSize N : ℝ) / Real.logb 2 (N : ℝ) < v := by
  let ell := Real.log 2
  have hell : 0 < ell := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hvp : 0 < v := by linarith only [hv]
  let c := ell * (v - 1) / (2 * v)
  let D := ell * (v - 1) / 2
  let K := ell - 1 - Real.log c
  have hc : 0 < c := div_pos (mul_pos hell (sub_pos.mpr hv)) (mul_pos (by norm_num) hvp)
  have hD : 0 < D := div_pos (mul_pos hell (sub_pos.mpr hv)) (by norm_num)
  have hident : (ell - c) * v = ell + D := by
    dsimp only [c, D]
    field_simp [hvp.ne'] <;> ring
  have hellc : 0 < ell - c := by
    have hp : 0 < (ell - c) * v := by rw [hident]; exact add_pos hell hD
    by_contra hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hvp.le)) hp
  filter_upwards [eventually_large_logb (max 0 (K / D)),
    eventually_ge_atTop (1 : ℕ)] with N hLbig hN
  let L := Real.logb 2 (N : ℝ)
  let k := (maximumSize N : ℝ)
  have hL : 0 < L := lt_of_le_of_lt (le_max_left _ _) hLbig
  change k / L < v
  by_contra h
  have hcontra : v * L ≤ k := (le_div_iff₀ hL).1 (le_of_not_gt h)
  have hkp : 0 < k := (mul_pos hvp hL).trans_le hcontra
  have hkpNat : 0 < maximumSize N := by
    have hkp' : 0 < (maximumSize N : ℝ) := hkp
    exact_mod_cast hkp'
  have hlog := log_count_bound (by omega : 0 < N) hkpNat
  change k * ell ≤ ell + (Real.log k + Real.log (N : ℝ)) at hlog
  have hlogk := Real.log_le_sub_one_of_pos (mul_pos hc hkp)
  rw [Real.log_mul hc.ne' hkp.ne'] at hlogk
  have hLc : L * ell = Real.log (N : ℝ) := div_mul_cancel₀ _ hell.ne'
  have hf : (ell - c) * k ≤ L * ell + K := by
    dsimp only [K]
    nlinarith only [hlog, hlogk, hLc]
  have hlimit : K < L * D := (div_lt_iff₀ hD).1 (lt_of_le_of_lt (le_max_right _ _) hLbig)
  have hm : (ell + D) * L ≤ (ell - c) * k := by
    calc
      _ = (ell - c) * (v * L) := by rw [← hident, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hcontra hellc.le
  nlinarith only [hf, hm, hlimit]

theorem erdos_882 :
    Tendsto (fun N : ℕ => (maximumSize N : ℝ) / Real.logb 2 (N : ℝ)) atTop (𝓝 1) := by
  exact tendsto_order.2 ⟨eventually_ratio_gt, eventually_ratio_lt⟩

end JSP000733

#print axioms JSP000733.erdos_882
