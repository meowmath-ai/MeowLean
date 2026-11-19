import Mathlib


open Finset Filter
open scoped BigOperators Topology

namespace Erdos1205

def hits (K : ℕ) (a : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (range K).filter fun i => m % (i + 1) = a i

def coverage (K : ℕ) (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  (hits K a m).card

def Valid (K : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ i < K, a i < i + 1

theorem mem_hits_iff_modEq {K : ℕ} {a : ℕ → ℕ} (ha : Valid K a) (i m : ℕ) :
    i ∈ hits K a m ↔ i < K ∧ Nat.ModEq (i + 1) m (a i) := by
  simp only [hits, mem_filter, mem_range]
  constructor
  · rintro ⟨hi, hm⟩
    exact ⟨hi, by simpa only [Nat.ModEq, Nat.mod_eq_of_lt (ha i hi)] using hm⟩
  · rintro ⟨hi, hm⟩
    exact ⟨hi, by simpa only [Nat.ModEq, Nat.mod_eq_of_lt (ha i hi)] using hm⟩

def Feasible (N k : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, Valid N a ∧ ∀ m ∈ Icc 1 N, k ≤ coverage N a m

noncomputable def F (N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Feasible N) N

private theorem zero_feasible (N : ℕ) : Feasible N 0 := by
  exact ⟨fun _ => 0, fun _ _ => Nat.succ_pos _, fun _ _ => Nat.zero_le _⟩

theorem F_feasible (N : ℕ) : Feasible N (F N) := by
  classical
  unfold F
  exact Nat.findGreatest_spec (Nat.zero_le N) (zero_feasible N)

theorem le_F_of_feasible {N k : ℕ} (hN : 0 < N) (h : Feasible N k) : k ≤ F N := by
  classical
  unfold F
  apply Nat.le_findGreatest _ h
  obtain ⟨a, _, ha⟩ := h
  have h1 : 1 ∈ Icc (1 : ℕ) N := mem_Icc.mpr ⟨le_rfl, hN⟩
  exact (ha 1 h1).trans (by
    unfold coverage hits
    simpa using (Finset.card_le_card (Finset.filter_subset
      (fun i => 1 % (i + 1) = a i) (range N))))

theorem F_isGreatest (N : ℕ) (hN : 0 < N) :
    IsGreatest {k : ℕ | Feasible N k} (F N) :=
  ⟨F_feasible N, fun _ hk => le_F_of_feasible hN hk⟩

private theorem coverage_mono_of_agree {K N : ℕ} {a b : ℕ → ℕ}
    (hKN : K ≤ N) (h : ∀ i < K, b i = a i) (m : ℕ) :
    coverage K a m ≤ coverage N b m := by
  unfold coverage hits
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiK, hiA⟩ := mem_filter.mp hi
  exact mem_filter.mpr
    ⟨mem_range.mpr ((mem_range.mp hiK).trans_le hKN),
     hiA.trans (h i (mem_range.mp hiK)).symm⟩

private theorem coverage_update (K : ℕ) (a : ℕ → ℕ) (r m : ℕ) :
    coverage (K + 1) (Function.update a K r) m =
      coverage K a m + (if m % (K + 1) = r then 1 else 0) := by
  classical
  have htail : hits K (Function.update a K r) m = hits K a m := by
    unfold hits
    apply Finset.filter_congr
    intro i hi
    have hne : i ≠ K := Nat.ne_of_lt (mem_range.mp hi)
    simp only [Function.update_of_ne hne]
  have hnot : K ∉ hits K a m := by
    intro h
    exact (Nat.lt_irrefl K) (mem_range.mp (mem_filter.mp h).1)
  unfold coverage
  have hsplit : hits (K + 1) (Function.update a K r) m =
      if m % (K + 1) = r then insert K (hits K a m) else hits K a m := by
    have hsplit' : hits (K + 1) (Function.update a K r) m =
        if m % (K + 1) = r then insert K (hits K (Function.update a K r) m)
        else hits K (Function.update a K r) m := by
      unfold hits
      rw [Finset.range_add_one, Finset.filter_insert, Function.update_self]
    simpa only [htail] using hsplit'
  rw [hsplit]
  by_cases hm : m % (K + 1) = r
  · simp [hm, Finset.card_insert_of_notMem hnot]
  · simp [hm]

private theorem real_card_filter (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((s.filter p).card : ℝ) = ∑ x ∈ s, (if p x then (1 : ℝ) else 0) := by
  rw [← Finset.sum_filter]
  simp [nsmul_eq_mul]

private theorem harmonic_as_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ i ∈ range N, ((i + 1 : ℕ) : ℝ)⁻¹ := by
  simp [harmonic]

private theorem cardinal_class_bound (N i r : ℕ) :
    ((Icc 1 N).filter fun m => m % (i + 1) = r).card ≤ N / (i + 1) + 1 := by
  rw [← Finset.card_range (N / (i + 1) + 1)]
  apply Finset.card_le_card_of_injOn (fun m : ℕ => m / (i + 1))
  · intro x hx
    have hxx : x ∈ (Icc 1 N).filter (fun m => m % (i + 1) = r) := hx
    have hxN : x ≤ N := (mem_Icc.mp (mem_filter.mp hxx).1).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hxN))
  · intro x hx y hy hxy
    change x / (i + 1) = y / (i + 1) at hxy
    have hxx : x ∈ (Icc 1 N).filter (fun m => m % (i + 1) = r) := hx
    have hyy : y ∈ (Icc 1 N).filter (fun m => m % (i + 1) = r) := hy
    have hrem : x % (i + 1) = y % (i + 1) :=
      (mem_filter.mp hxx).2.trans (mem_filter.mp hyy).2.symm
    calc
      x = x % (i + 1) + (i + 1) * (x / (i + 1)) := (Nat.mod_add_div x (i + 1)).symm
      _ = y % (i + 1) + (i + 1) * (y / (i + 1)) := by rw [hrem, hxy]
      _ = y := Nat.mod_add_div y (i + 1)

theorem F_le_harmonic_add_one {N : ℕ} (hN : 0 < N) :
    (F N : ℝ) ≤ (harmonic N : ℝ) + 1 := by
  classical
  obtain ⟨a, _, ha⟩ := F_feasible N
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount : (N : ℝ) * (F N : ℝ) ≤ (N : ℝ) * (harmonic N : ℝ) + N := calc
    _ = ∑ _m ∈ Icc 1 N, (F N : ℝ) := by simp [nsmul_eq_mul]
    _ ≤ ∑ m ∈ Icc 1 N, (coverage N a m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact_mod_cast ha m hm
    _ = ∑ m ∈ Icc 1 N, ∑ i ∈ range N,
        (if m % (i + 1) = a i then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact real_card_filter _ _
    _ = ∑ i ∈ range N, ∑ m ∈ Icc 1 N,
        (if m % (i + 1) = a i then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ i ∈ range N, (((Icc 1 N).filter
        (fun m => m % (i + 1) = a i)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (real_card_filter _ _).symm
    _ ≤ ∑ i ∈ range N, ((N : ℝ) / ((i + 1 : ℕ) : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hquot : ((N / (i + 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((i + 1 : ℕ) : ℝ) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ))).2
        exact_mod_cast Nat.div_mul_le_self N (i + 1)
      have hc : (((Icc 1 N).filter (fun m => m % (i + 1) = a i)).card : ℝ) ≤
          ((N / (i + 1) : ℕ) : ℝ) + 1 := by
        exact_mod_cast cardinal_class_bound N i (a i)
      linarith
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [div_eq_mul_inv, ← Finset.mul_sum, ← harmonic_as_sum]
      simp [nsmul_eq_mul]
  by_contra! h
  have hlt := mul_lt_mul_of_pos_left h hNp
  nlinarith only [hcount, hlt]

theorem F_le_log_add_two {N : ℕ} (hN : 0 < N) :
    (F N : ℝ) ≤ Real.log (N : ℝ) + 2 := by
  linarith only [F_le_harmonic_add_one hN, harmonic_le_one_add_log N]


def bad (N K k : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun m => coverage K a m < k

theorem feasible_of_bad_card {N K k : ℕ} {a : ℕ → ℕ}
    (hKN : K ≤ N) (ha : Valid K a)
    (hcard : (bad N K k a).card * k ≤ N - K) :
    Feasible N k := by
  classical
  let B := bad N K k a
  have hh : Fintype.card (↥B × Fin k) ≤ Fintype.card (Fin (N - K)) := by
    simpa [B, Fintype.card_prod] using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hh
  let d : ↥B × Fin k → ℕ := fun p => K + (e p : ℕ)
  have hd_inj : Function.Injective d := by
    intro p p' h
    apply e.injective
    apply Fin.ext
    exact Nat.add_left_cancel h
  have hd_ge (p : ↥B × Fin k) : K ≤ d p := by
    dsimp only [d]
    omega
  have hd_lt (p : ↥B × Fin k) : d p < N := by
    have h := (e p).isLt
    dsimp only [d]
    omega
  let b : ℕ → ℕ := fun i =>
    if i < K then a i
    else
      match Function.partialInv d i with
      | none => 0
      | some p => (p.1 : ℕ) % (i + 1)
  have hb_early (i : ℕ) (hi : i < K) : b i = a i := by
    simp [b, hi]
  have hb_late (p : ↥B × Fin k) : b (d p) = (p.1 : ℕ) % (d p + 1) := by
    dsimp only [b]
    rw [ite_eq_right (not_lt_of_ge (hd_ge p)), Function.partialInv_left hd_inj p]
  refine ⟨b, ?_, ?_⟩
  · intro i hi
    by_cases hiK : i < K
    · rw [hb_early i hiK]
      exact ha i hiK
    · dsimp only [b]
      rw [ite_eq_right hiK]
      cases Function.partialInv d i with
      | none => exact Nat.succ_pos _
      | some p => exact Nat.mod_lt _ (Nat.succ_pos _)
  · intro m hm
    by_cases hm' : coverage K a m < k
    · let x : ↥B := ⟨m, Finset.mem_filter.mpr ⟨hm, hm'⟩⟩
      let f : Fin k → ↥(hits N b m) := fun j => ⟨d (x,j), by
        unfold hits
        exact Finset.mem_filter.mpr
          ⟨mem_range.mpr (hd_lt (x,j)), (hb_late (x,j)).symm⟩⟩
      have hf : Function.Injective f := by
        intro i j h
        have hv : d (x,i) = d (x,j) := congrArg Subtype.val h
        exact congrArg Prod.snd (hd_inj hv)
      simpa [coverage] using Fintype.card_le_of_injective f hf
    · exact (le_of_not_gt hm').trans (coverage_mono_of_agree hKN hb_early m)

noncomputable def potential (N K : ℕ) (q : ℝ) (a : ℕ → ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, q ^ coverage K a m

theorem exists_small_potential (N K : ℕ) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ a : ℕ → ℕ, Valid K a ∧
      potential N K q a ≤ (N : ℝ) * Real.exp (-(1 - q) * (harmonic K : ℝ)) := by
  classical
  induction K with
  | zero =>
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i hi
      exact (Nat.not_lt_zero i hi).elim
    · simp [potential, coverage, hits, nsmul_eq_mul]
  | succ K ih =>
    obtain ⟨a, ha, hpot⟩ := ih
    let w : ℕ → ℝ := fun m => q ^ coverage K a m
    let W : ℝ := potential N K q a
    let mass : ℕ → ℝ := fun r =>
      ∑ m ∈ (Icc 1 N).filter (fun m => m % (K + 1) = r), w m
    let D : ℝ := ((K + 1 : ℕ) : ℝ)
    have hD : 0 < D := by dsimp [D]; positivity
    have hp : 0 ≤ W := by
      change 0 ≤ ∑ m ∈ Icc 1 N, w m
      exact Finset.sum_nonneg (fun m hm => pow_nonneg hq.le _)
    have hall : (∑ r ∈ range (K + 1), mass r) = W := by
      dsimp [mass, W, potential, w]
      exact Finset.sum_fiberwise_of_maps_to
        (fun m _ => mem_range.mpr (Nat.mod_lt m (Nat.succ_pos K))) _
    have hne : (range (K + 1)).Nonempty := ⟨0, mem_range.mpr (Nat.succ_pos K)⟩
    obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image (range (K + 1)) mass hne
    have hmul : W ≤ mass r * D := calc
      W = ∑ x ∈ range (K + 1), mass x := hall.symm
      _ ≤ ∑ _x ∈ range (K + 1), mass r := Finset.sum_le_sum hmax
      _ = mass r * D := by simp [D, nsmul_eq_mul, mul_comm]
    have havg : W / D ≤ mass r := (div_le_iff₀ hD).2 hmul
    let b : ℕ → ℕ := Function.update a K r
    have hb : Valid (K + 1) b := by
      intro i hi
      change Function.update a K r i < i + 1
      by_cases hk : i = K
      · subst i
        simpa only [Function.update_self] using mem_range.mp hr
      · rw [Function.update_of_ne hk]
        exact ha i (by omega)
    refine ⟨b, hb, ?_⟩
    have hchange : potential N (K + 1) q b = W - (1 - q) * mass r := calc
      _ = ∑ m ∈ Icc 1 N, (w m - (1 - q) * (if m % (K + 1) = r then w m else 0)) := by
        unfold potential
        apply Finset.sum_congr rfl
        intro m hm
        change q ^ coverage (K + 1) (Function.update a K r) m = _
        rw [coverage_update]
        by_cases hh : m % (K + 1) = r
        · simp only [hh, ite_true, pow_succ]
          dsimp [w]
          ring
        · simp [hh, w]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter] <;> rfl
    have hexp : 1 - (1 - q) / D ≤ Real.exp (-(1 - q) / D) := by
      simpa only [neg_div] using Real.one_sub_le_exp_neg ((1 - q) / D)
    have hH : (harmonic (K + 1) : ℝ) = (harmonic K : ℝ) + D⁻¹ := by
      dsimp only [D]
      simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv_nat]
    calc
      _ = W - (1 - q) * mass r := hchange
      _ ≤ W - (1 - q) * (W / D) :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left havg (sub_nonneg.mpr hq1)) W
      _ = W * (1 - (1 - q) / D) := by ring
      _ ≤ W * Real.exp (-(1 - q) / D) := mul_le_mul_of_nonneg_left hexp hp
      _ ≤ ((N : ℝ) * Real.exp (-(1 - q) * (harmonic K : ℝ))) *
          Real.exp (-(1 - q) / D) :=
        mul_le_mul_of_nonneg_right hpot (Real.exp_nonneg _)
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add, hH]
        congr 2
        ring

private theorem weight_exp {q : ℝ} (hq : 0 < q) (j : ℕ) :
    q ^ j = Real.exp ((j : ℝ) * Real.log q) := by
  rw [Real.exp_nat_mul, Real.exp_log hq]

theorem bad_card_mul_weight_le_potential (N K k : ℕ) (a : ℕ → ℕ)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ((bad N K k a).card : ℝ) * q ^ k ≤ potential N K q a := by
  classical
  calc
    _ = ∑ _m ∈ bad N K k a, q ^ k := by simp [nsmul_eq_mul]
    _ ≤ ∑ m ∈ bad N K k a, q ^ coverage K a m := by
      apply Finset.sum_le_sum
      intro m hm
      have hmk : coverage K a m ≤ k := (Finset.mem_filter.mp hm).2.le
      rw [weight_exp hq k, weight_exp hq (coverage K a m)]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_right (by exact_mod_cast hmk) (Real.log_nonpos hq.le hq1)
    _ ≤ potential N K q a := by
      unfold potential
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun m hm hb => pow_nonneg hq.le _)

theorem feasible_of_potential_bound {N K k : ℕ} {q : ℝ}
    (hKN : K ≤ N) (hq : 0 < q) (hq1 : q ≤ 1)
    (hbudget : (N : ℝ) * Real.exp (-(1 - q) * (harmonic K : ℝ)
        - (k : ℝ) * Real.log q) * (k : ℝ) ≤ (↑(N - K) : ℝ)) :
    Feasible N k := by
  obtain ⟨a, ha, hw⟩ := exists_small_potential N K hq hq1
  have hb := (bad_card_mul_weight_le_potential N K k a hq hq1).trans hw
  have hqk : 0 < q ^ k := pow_pos hq _
  have hB : ((bad N K k a).card : ℝ) ≤
      (N : ℝ) * Real.exp (-(1 - q) * (harmonic K : ℝ) - (k : ℝ) * Real.log q) := by
    have hb' := (le_div_iff₀ hqk).2 hb
    rw [weight_exp hq k, mul_div_assoc, ← Real.exp_sub] at hb'
    exact hb'
  apply feasible_of_bad_card hKN ha
  have h := (mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg k)).trans hbudget
  exact_mod_cast h

private theorem log_sub_log_two_le_harmonic_half (N : ℕ) (hN : 0 < N) :
    Real.log (N : ℝ) - Real.log 2 ≤ (harmonic (N / 2) : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hnat : N ≤ 2 * (N / 2 + 1) := by omega
  have hreal : (N : ℝ) ≤ 2 * ((N / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  have he := Real.log_le_log hNpos hreal
  rw [Real.log_mul (by norm_num) (by positivity)] at he
  linarith only [he, log_add_one_le_harmonic (N / 2)]

private theorem log_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem lower_of_parameter (N : ℕ) (hN : 0 < N) {t : ℝ}
    (ht : 0 < t) (ht2 : t < 1 / 2)
    (hbudget : Real.exp (t * Real.log 2) *
      (Real.log (N : ℝ) * Real.exp (-(t ^ 2 / (1 - t)) * Real.log (N : ℝ))) ≤ 1 / 2) :
    (1 - 2 * t) * Real.log (N : ℝ) < (F N : ℝ) + 1 := by
  let q : ℝ := 1 - t
  let c : ℝ := t ^ 2 / q
  let L : ℝ := Real.log (N : ℝ)
  let K : ℕ := N / 2
  let k : ℕ := ⌊(1 - 2 * t) * L⌋₊
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hqeq : 1 - q = t := by dsimp [q]; ring
  have htq : 0 ≤ t / q := div_nonneg ht.le hq.le
  have hlogq : -(t / q) ≤ Real.log q := by
    have heq : 1 - q⁻¹ = -(t / q) := by
      have h' : q - 1 = -t := by dsimp [q]; ring
      calc
        1 - q⁻¹ = (q - 1) / q := by field_simp [ne_of_gt hq] <;> ring
        _ = _ := by rw [h', neg_div]
    rw [← heq]
    exact Real.one_sub_inv_le_log_of_pos hq
  have hc : t - (1 - 2 * t) * (t / q) = c := by
    dsimp only [c, q]
    have hq' : (1 - t) ≠ 0 := by linarith
    field_simp [hq'] <;> ring
  have hL : 0 ≤ L := Real.log_natCast_nonneg N
  have hk : (k : ℝ) ≤ (1 - 2 * t) * L :=
    Nat.floor_le (mul_nonneg (by linarith) hL)
  have hkL : (k : ℝ) ≤ L := by
    nlinarith only [hk, mul_nonneg ht.le hL]
  have harg : -(1 - q) * (harmonic K : ℝ) - (k : ℝ) * Real.log q ≤
      t * Real.log 2 - c * L := by
    have hH : t * (L - Real.log 2) ≤ t * (harmonic K : ℝ) :=
      mul_le_mul_of_nonneg_left (log_sub_log_two_le_harmonic_half N hN) ht.le
    have hlogterm := mul_le_mul_of_nonneg_left hlogq (Nat.cast_nonneg k)
    have hkterm := mul_le_mul_of_nonneg_right hk htq
    rw [hqeq, ← hc]
    ring_nf at hH hlogterm hkterm ⊢
    linarith only [hH, hlogterm, hkterm]
  have hKN : K ≤ N := Nat.div_le_self N 2
  have hspace : (N : ℝ) / 2 ≤ (↑(N - K) : ℝ) := by
    have hnat : N ≤ 2 * (N - K) := by
      dsimp only [K]
      omega
    have hreal : (N : ℝ) ≤ 2 * (↑(N - K) : ℝ) := by exact_mod_cast hnat
    linarith only [hreal]
  have hrepair : (N : ℝ) * Real.exp (-(1 - q) * (harmonic K : ℝ) -
        (k : ℝ) * Real.log q) * (k : ℝ) ≤ (↑(N - K) : ℝ) := calc
    _ ≤ (N : ℝ) * Real.exp (t * Real.log 2 - c * L) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (Nat.cast_nonneg N))
        (Nat.cast_nonneg k)
    _ ≤ (N : ℝ) * Real.exp (t * Real.log 2 - c * L) * L :=
      mul_le_mul_of_nonneg_left hkL (by positivity)
    _ = (N : ℝ) * (Real.exp (t * Real.log 2) * (L * Real.exp (-c * L))) := by
      rw [show t * Real.log 2 - c * L = t * Real.log 2 + (-c) * L by ring, Real.exp_add]
      ring
    _ ≤ (N : ℝ) * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg N)
    _ = (N : ℝ) / 2 := by ring
    _ ≤ _ := hspace
  have hKf : (k : ℝ) ≤ (F N : ℝ) := by
    exact_mod_cast (le_F_of_feasible hN (feasible_of_potential_bound hKN hq hq1 hrepair))
  exact (Nat.lt_floor_add_one ((1 - 2 * t) * L)).trans_le (add_le_add hKf (le_rfl : (1 : ℝ) ≤ 1))

private theorem lower_eventually_for_parameter {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, (1 - 2 * t) * Real.log (N : ℝ) < (F N : ℝ) + 1 := by
  let c : ℝ := t ^ 2 / (1 - t)
  let C : ℝ := Real.exp (t * Real.log 2)
  have hc : 0 < c := by dsimp [c]; exact div_pos (pow_pos ht _) (by linarith)
  have hC : 0 < C := Real.exp_pos _
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ) *
      Real.exp (-c * Real.log (N : ℝ))) atTop (𝓝 0) := by
    have hEq :
        ((fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-c * x)) ∘
          (fun N : ℕ => Real.log (N : ℝ))) =
        (fun N : ℕ => Real.log (N : ℝ) * Real.exp (-c * Real.log (N : ℝ))) := by
      funext N
      change Real.log (N : ℝ) ^ (1 : ℝ) * Real.exp (-c * Real.log (N : ℝ)) =
        Real.log (N : ℝ) * Real.exp (-c * Real.log (N : ℝ))
      rw [Real.rpow_one]
    rw [← hEq]
    exact (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) c hc).comp
      log_nat_tendsto_atTop
  have hsmall := (tendsto_order.mp hl).2 (1 / (2 * C)) (by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with N hsmallN hN
  apply lower_of_parameter N (by omega) ht ht2
  have hmul := mul_lt_mul_of_pos_left hsmallN hC
  have hCbudget : C * (1 / (2 * C)) = 1 / 2 := by
    field_simp [ne_of_gt hC] <;> ring
  rw [hCbudget] at hmul
  exact hmul.le

theorem erdos1205_nat :
    Tendsto (fun N : ℕ => (F N : ℝ) / Real.log (N : ℝ)) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro u hu
    let t : ℝ := min (1 / 4) ((1 - u) / 4)
    have ht : 0 < t := lt_min_iff.mpr ⟨by norm_num, by linarith⟩
    have htle : t ≤ (1 / 4 : ℝ) := min_le_left _ _
    have htu : t ≤ (1 - u) / 4 := min_le_right _ _
    have ht2 : t < 1 / 2 := by linarith
    let d := 1 - 2 * t - u
    have hd : 0 < d := by dsimp only [d]; linarith
    have hgrow := (tendsto_atTop.mp log_nat_tendsto_atTop) (2 / d)
    filter_upwards [lower_eventually_for_parameter ht ht2, hgrow,
      eventually_ge_atTop (2 : ℕ)] with N hlow hL hN
    have hLp : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hdL := (div_le_iff₀ hd).mp hL
    change (2 : ℝ) ≤ Real.log (N : ℝ) * d at hdL
    dsimp only [d] at hdL
    apply (lt_div_iff₀ hLp).mpr
    nlinarith only [hlow, hdL]
  · intro u hu
    let d := u - 1
    have hd : 0 < d := sub_pos.mpr hu
    have hgrow := (tendsto_atTop.mp log_nat_tendsto_atTop) (3 / d)
    filter_upwards [hgrow, eventually_ge_atTop (2 : ℕ)] with N hL hN
    have hLp : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hdL := (div_le_iff₀ hd).mp hL
    change (3 : ℝ) ≤ Real.log (N : ℝ) * d at hdL
    dsimp only [d] at hdL
    apply (div_lt_iff₀ hLp).mpr
    nlinarith only [F_le_log_add_two (show 0 < N by omega), hdL]

private theorem log_div_self_tendsto :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)

theorem F_lower_sharp :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      L - (2 * Real.sqrt (2 * L * Real.log L) + 1) ≤ (F N : ℝ) := by
  have hdiv : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) /
      Real.log (N : ℝ)) atTop (𝓝 0) :=
    log_div_self_tendsto.comp log_nat_tendsto_atTop
  have hsmall := (tendsto_order.mp hdiv).2 (1 / 8) (by norm_num)
  have hlarge := (tendsto_atTop.mp log_nat_tendsto_atTop) 4
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℕ)] with N hs hL4 hN
  let L : ℝ := Real.log (N : ℝ)
  have hLp : 0 < L := by change 4 ≤ L at hL4; linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by change 4 ≤ L at hL4; linarith)
  let Z : ℝ := 2 * Real.log L / L
  have hZp : 0 < Z := by dsimp only [Z]; positivity
  have hZsmall : Z < 1 / 4 := by
    change Real.log L / L < 1 / 8 at hs
    dsimp only [Z]
    rw [mul_div_assoc]
    linarith only [hs]
  let t := Real.sqrt Z
  have ht : 0 < t := Real.sqrt_pos.2 hZp
  have ht2 : t < 1 / 2 :=
    (Real.sqrt_lt hZp.le (by norm_num)).2 (by linarith only [hZsmall])
  have htsq : t ^ 2 = Z := Real.sq_sqrt hZp.le
  have hq : 0 < 1 - t := by linarith
  have hc : t ^ 2 ≤ t ^ 2 / (1 - t) := by
    apply (le_div_iff₀ hq).2
    nlinarith only [mul_nonneg (sq_nonneg t) ht.le]
  have hcL : 2 * Real.log L ≤ (t ^ 2 / (1 - t)) * L := calc
    2 * Real.log L = t ^ 2 * L := by
      rw [htsq]
      dsimp only [Z]
      field_simp [ne_of_gt hLp]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hLp.le
  have hC : Real.exp (t * Real.log 2) ≤ 2 := calc
    _ ≤ Real.exp (Real.log 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hq.le (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    _ = 2 := Real.exp_log (by norm_num)
  have hE : Real.exp (-(t ^ 2 / (1 - t)) * L) ≤ (L ^ 2)⁻¹ := calc
    _ ≤ Real.exp (-(2 * Real.log L)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hcL]
    _ = (L ^ 2)⁻¹ := by
      have hpow : Real.exp (2 * Real.log L) = L ^ 2 := by
        simp [weight_exp hLp 2]
      rw [Real.exp_neg, hpow]
  have hbudget : Real.exp (t * Real.log 2) *
     (L * Real.exp (-(t ^ 2 / (1 - t)) * L)) ≤ 1 / 2 := calc
    _ ≤ Real.exp (t * Real.log 2) * (L * (L ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hLp.le) (Real.exp_nonneg _)
    _ = Real.exp (t * Real.log 2) * L⁻¹ := by
      have he : L * (L ^ 2)⁻¹ = L⁻¹ := by field_simp [ne_of_gt hLp]
      rw [he]
    _ ≤ 2 * L⁻¹ := mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hLp.le)
    _ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hLp).2
      change 4 ≤ L at hL4
      linarith only [hL4]
  have hr : Real.sqrt (2 * L * Real.log L) = t * L := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    calc
      2 * L * Real.log L = t ^ 2 * L ^ 2 := by
        rw [htsq]
        dsimp only [Z]
        field_simp [ne_of_gt hLp]
      _ = (t * L) ^ 2 := by ring
  have hF := lower_of_parameter N (by omega) ht ht2 hbudget
  change (1 - 2 * t) * L < (F N : ℝ) + 1 at hF
  change L - (2 * Real.sqrt (2 * L * Real.log L) + 1) ≤ (F N : ℝ)
  rw [hr]
  nlinarith only [hF]

private theorem log_nat_floor_comparison {x : ℝ} (hx : 2 ≤ x) :
    Real.log x - 1 ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) ∧
      Real.log ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log x := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simp only [Nat.cast_one]; linarith)
  have hNr : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN
  have hNp : (0 : ℝ) < ((⌊x⌋₊ : ℕ) : ℝ) := by linarith
  have hxp : 0 < x := by linarith
  have hxf : x ≤ 2 * ((⌊x⌋₊ : ℕ) : ℝ) := by
    linarith only [Nat.lt_floor_add_one x, hNr]
  have hlog := Real.log_le_log hxp hxf
  rw [Real.log_mul (by norm_num) (ne_of_gt hNp)] at hlog
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  exact ⟨by linarith only [hlog, h2],
    Real.log_le_log hNp (Nat.floor_le hxp.le)⟩

private theorem log_nat_floor_ratio :
    Tendsto (fun x : ℝ => Real.log ((⌊x⌋₊ : ℕ) : ℝ) / Real.log x) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro u hu
    let d := 1 - u
    have hd : 0 < d := sub_pos.mpr hu
    have hgrow := (tendsto_atTop.mp Real.tendsto_log_atTop) (2 / d)
    filter_upwards [hgrow, eventually_ge_atTop (2 : ℝ)] with x hL hx
    have hLp : 0 < Real.log x := Real.log_pos (by linarith)
    have hdL := (div_le_iff₀ hd).mp hL
    change (2 : ℝ) ≤ Real.log x * d at hdL
    dsimp only [d] at hdL
    apply (lt_div_iff₀ hLp).mpr
    nlinarith only [hdL, (log_nat_floor_comparison hx).1]
  · intro u hu
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hLp : 0 < Real.log x := Real.log_pos (by linarith)
    have hbound : Real.log ((⌊x⌋₊ : ℕ) : ℝ) / Real.log x ≤ 1 := by
      apply (div_le_iff₀ hLp).mpr
      simpa using (log_nat_floor_comparison hx).2
    exact hbound.trans_lt hu

theorem erdos1205 :
    Tendsto (fun x : ℝ => (F ⌊x⌋₊ : ℝ) / Real.log x) atTop (𝓝 1) := by
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have hf : Tendsto (fun x : ℝ => (F ⌊x⌋₊ : ℝ) / Real.log ((⌊x⌋₊ : ℕ) : ℝ))
      atTop (𝓝 1) := erdos1205_nat.comp hfloor
  have hprod : Tendsto (fun x : ℝ => ((F ⌊x⌋₊ : ℝ) / Real.log ((⌊x⌋₊ : ℕ) : ℝ)) *
      (Real.log ((⌊x⌋₊ : ℕ) : ℝ) / Real.log x)) atTop (𝓝 1) := by
    simpa only [one_mul] using hf.mul log_nat_floor_ratio
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hNlog : 0 < Real.log ((⌊x⌋₊ : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < ⌊x⌋₊ by omega))
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  change ((F ⌊x⌋₊ : ℝ) / Real.log ((⌊x⌋₊ : ℕ) : ℝ)) *
    (Real.log ((⌊x⌋₊ : ℕ) : ℝ) / Real.log x) = (F ⌊x⌋₊ : ℝ) / Real.log x
  field_simp [ne_of_gt hNlog, ne_of_gt hxlog]

end Erdos1205

#print axioms Erdos1205.erdos1205
#print axioms Erdos1205.F_lower_sharp
