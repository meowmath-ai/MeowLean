import Mathlib
import ErdosProblems.Erdos27

open scoped BigOperators
open Set MeasureTheory
open Erdos27

namespace JSP000060

noncomputable section

local instance jspSmallPeriodNeZero (Q : ℕ) (A : ResidueSystem) :
    NeZero (smallPeriod Q A) := ⟨(smallPeriod_pos Q A).ne'⟩

local instance jspRoughPeriodNeZero (Q : ℕ) (A : ResidueSystem) :
    NeZero (roughPeriod Q A) := ⟨(roughPeriod_pos Q A).ne'⟩

def InFFKPYWindow (A : ResidueSystem) (K N : ℝ) : Prop :=
  ∀ m ∈ A.moduli, N < (m : ℝ) ∧ (m : ℝ) ≤ K * N

private theorem period_factorization (Q : ℕ) (A : ResidueSystem) :
    A.period = smallPeriod Q A * roughPeriod Q A := by
  refine Nat.dvd_antisymm ?_ ?_
  · change A.moduli.lcm id ∣ smallPeriod Q A * roughPeriod Q A
    refine Finset.lcm_dvd ?_
    intro n hn
    change n ∣ smallPeriod Q A * roughPeriod Q A
    rw [← smallPart_mul_roughPart (Q := Q) (A.modulus_pos n hn).ne']
    exact Nat.mul_dvd_mul (small_dvd_smallPeriod Q A hn) (rough_dvd_roughPeriod Q A hn)
  · have hs : smallPeriod Q A ∣ A.period := by
      change A.moduli.lcm (smallPart Q) ∣ A.period
      exact Finset.lcm_dvd fun n hn =>
        (smallPart_dvd (Q := Q) (A.modulus_pos n hn)).trans (A.dvd_period hn)
    have hr : roughPeriod Q A ∣ A.period := by
      change A.moduli.lcm (roughPart Q) ∣ A.period
      exact Finset.lcm_dvd fun n hn =>
        (roughPart_dvd (Q := Q) (A.modulus_pos n hn)).trans (A.dvd_period hn)
    rw [← (smallPeriod_coprime_roughPeriod Q A).lcm_eq_mul]
    exact Nat.lcm_dvd hs hr

private abbrev survives (Q : ℕ) (A : ResidueSystem) (h : ZMod (smallPeriod Q A)) :
    Set (ZMod (roughPeriod Q A)) :=
  Erdos277.residual (activeIndices Q A h) (roughEvent Q A)

private theorem representative_survives (Q : ℕ) (A : ResidueSystem)
    (h : ZMod (smallPeriod Q A)) (y : ZMod (roughPeriod Q A))
    (hy : y ∈ survives Q A h) :
    (((ZMod.chineseRemainder (smallPeriod_coprime_roughPeriod Q A)).symm (h, y)).val : ℤ)
      ∈ A.uncovered := by
  classical
  let M := smallPeriod Q A
  let R := roughPeriod Q A
  letI : NeZero (M * R) := ⟨(Nat.mul_pos (smallPeriod_pos Q A) (roughPeriod_pos Q A)).ne'⟩
  let e := ZMod.chineseRemainder (smallPeriod_coprime_roughPeriod Q A)
  let x : ZMod (M * R) := e.symm (h, y)
  let hMd : M ∣ M * R := ⟨R, rfl⟩
  let hRd : R ∣ M * R := ⟨M, Nat.mul_comm M R⟩
  have hpair : e x = (h, y) := e.apply_symm_apply (h, y)
  have hleft : ZMod.castHom hMd (ZMod M) x = h := by
    have hi := congrArg (fun w : ZMod M × ZMod R => w.1) hpair
    change (e x).1 = h at hi
    simpa only [e, chineseRemainder_fst] using hi
  have hright : ZMod.castHom hRd (ZMod R) x = y := by
    have hi := congrArg (fun w : ZMod M × ZMod R => w.2) hpair
    change (e x).2 = y at hi
    simpa only [e, chineseRemainder_snd] using hi
  have hx : (x.val : ZMod (M * R)) = x := ZMod.natCast_zmod_val x
  have hm : (x.val : ZMod M) = h := by
    simpa only [map_natCast] using
      (congrArg (ZMod.castHom hMd (ZMod M)) hx).trans hleft
  have hr : (x.val : ZMod R) = y := by
    simpa only [map_natCast] using
      (congrArg (ZMod.castHom hRd (ZMod R)) hx).trans hright
  change (x.val : ℤ) ∈ A.uncovered
  intro n hn heq
  have heq' : (x.val : ZMod n) = A.residue n := by
    simpa only [Int.cast_natCast] using heq
  let i : ModIndex A := ⟨n, hn⟩
  have hs : active Q A h i := by
    change ZMod.castHom (small_dvd_smallPeriod Q A hn) (ZMod (smallPart Q n)) h =
      ZMod.castHom (smallPart_dvd (Q := Q) (A.modulus_pos n hn))
        (ZMod (smallPart Q n)) (A.residue n)
    rw [← hm, map_natCast]
    simpa only [map_natCast] using
      congrArg (ZMod.castHom (smallPart_dvd (Q := Q) (A.modulus_pos n hn))
        (ZMod (smallPart Q n))) heq'
  have ha : i ∈ activeIndices Q A h := by
    unfold activeIndices
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
  have hb : y ∈ roughEvent Q A i := by
    change ZMod.castHom (rough_dvd_roughPeriod Q A hn) (ZMod (roughPart Q n)) y =
      ZMod.castHom (roughPart_dvd (Q := Q) (A.modulus_pos n hn))
        (ZMod (roughPart Q n)) (A.residue n)
    rw [← hr, map_natCast]
    simpa only [map_natCast] using
      congrArg (ZMod.castHom (roughPart_dvd (Q := Q) (A.modulus_pos n hn))
        (ZMod (roughPart Q n))) heq'
  have hav : ∀ j, j ∈ activeIndices Q A h → y ∉ roughEvent Q A j := by
    simpa only [survives, Erdos277.residual, Set.mem_compl_iff, Set.mem_iUnion,
      not_exists] using hy
  exact hav i ha hb

private theorem summed_survival_le_density (Q : ℕ) (A : ResidueSystem) :
    (∑ h : ZMod (smallPeriod Q A),
      (Erdos277.residueMeasure (roughPeriod Q A)).real (survives Q A h)) ≤
      (smallPeriod Q A : ℝ) * A.uncoveredDensity := by
  classical
  let M := smallPeriod Q A
  let R := roughPeriod Q A
  have hm : 0 < M := smallPeriod_pos Q A
  have hr : 0 < R := roughPeriod_pos Q A
  have hmR : (0 : ℝ) < M := by exact_mod_cast hm
  have hrR : (0 : ℝ) < R := by exact_mod_cast hr
  letI : NeZero M := ⟨hm.ne'⟩
  letI : NeZero R := ⟨hr.ne'⟩
  letI : NeZero (M * R) := ⟨(Nat.mul_pos hm hr).ne'⟩
  let e := ZMod.chineseRemainder (smallPeriod_coprime_roughPeriod Q A)
  let F : ZMod M → Finset (ZMod R) := fun h => Finset.univ.filter (· ∈ survives Q A h)
  have hF (h : ZMod M) : (F h : Set (ZMod R)) = survives Q A h := by
    ext y
    simp [F]
  let S : Finset (Σ _ : ZMod M, ZMod R) :=
    (Finset.univ : Finset (ZMod M)).sigma F
  let enc : (Σ _ : ZMod M, ZMod R) → ℕ := fun a => (e.symm (a.1, a.2)).val
  have hp : A.period = M * R := period_factorization Q A
  have hi : Function.Injective enc := by
    rintro ⟨h, y⟩ ⟨h', y'⟩ he
    have ht : (h, y) = (h', y') := e.symm.injective ((ZMod.val_injective (M * R)) he)
    have hh : h = h' := congrArg (fun w : ZMod M × ZMod R => w.1) ht
    have hy : y = y' := congrArg (fun w : ZMod M × ZMod R => w.2) ht
    subst h'
    subst y'
    rfl
  have hg : Set.MapsTo enc (S : Set (Σ _ : ZMod M, ZMod R))
      (A.uncoveredMod : Set ℕ) := by
    intro a ha
    have hmemb : a ∈ (Finset.univ : Finset (ZMod M)).sigma F := by
      exact ha
    have hfy : a.2 ∈ F a.1 := (Finset.mem_sigma.mp hmemb).2
    have hsy : a.2 ∈ survives Q A a.1 := by
      rw [← hF a.1]
      exact hfy
    change enc a ∈ A.uncoveredMod
    unfold ResidueSystem.uncoveredMod
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, representative_survives Q A a.1 a.2 hsy⟩
    rw [hp]
    exact ZMod.val_lt _
  have hcard : S.card ≤ A.uncoveredMod.card :=
    Finset.card_le_card_of_injOn enc hg hi.injOn
  have hcards : (∑ h : ZMod M, (F h).card) ≤ A.uncoveredMod.card := by
    simpa only [S, Finset.card_sigma] using hcard
  have hcasts : ((∑ h : ZMod M, (F h).card : ℕ) : ℝ) ≤
      (A.uncoveredMod.card : ℝ) := by exact_mod_cast hcards
  have hcardsR : (∑ h : ZMod M, ((F h).card : ℝ)) ≤ (A.uncoveredMod.card : ℝ) := by
    simpa only [Nat.cast_sum] using hcasts
  change (∑ h : ZMod M, (Erdos277.residueMeasure R).real (survives Q A h)) ≤
      (M : ℝ) * A.uncoveredDensity
  calc
    (∑ h : ZMod M, (Erdos277.residueMeasure R).real (survives Q A h)) =
        ∑ h : ZMod M, ((F h).card : ℝ) / R := by
      refine Finset.sum_congr rfl ?_
      intro h _
      rw [← hF h]
      exact residueMeasure_finset_real hr (F h)
    _ = (∑ h : ZMod M, ((F h).card : ℝ)) / R := by rw [Finset.sum_div]
    _ ≤ (A.uncoveredMod.card : ℝ) / R := div_le_div_of_nonneg_right hcardsR hrR.le
    _ = (M : ℝ) * A.uncoveredDensity := by
      rw [ResidueSystem.uncoveredDensity, hp, Nat.cast_mul]
      field_simp [hmR.ne', hrR.ne']

private def threshold (Q K : ℕ) : ℕ :=
  (4 * 2 ^ (Q + 1).primesBelow.card) ^ 2 * K + 1

private theorem smooth_sparse_eventually (Q K N : ℕ) (hN : threshold Q K ≤ N) :
    4 * (Nat.smoothNumbersUpTo (K * N) (Q + 1)).card ≤ N := by
  let P : ℕ := 2 ^ (Q + 1).primesBelow.card
  let s : ℕ := (K * N).sqrt
  have hcount : (Nat.smoothNumbersUpTo (K * N) (Q + 1)).card ≤ P * s :=
    Nat.smoothNumbersUpTo_card_le (K * N) (Q + 1)
  have hs : s ^ 2 ≤ K * N := Nat.sqrt_le' _
  have hB : (4 * P) ^ 2 * K ≤ N := by
    change (4 * P) ^ 2 * K + 1 ≤ N at hN
    exact (Nat.le_succ _).trans hN
  have hb : (4 * P * s) ^ 2 ≤ N ^ 2 := by
    calc
      (4 * P * s) ^ 2 = (4 * P) ^ 2 * s ^ 2 := by ring
      _ ≤ (4 * P) ^ 2 * (K * N) := Nat.mul_le_mul_left _ hs
      _ = ((4 * P) ^ 2 * K) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right _ hB
      _ = N ^ 2 := by ring
  have hbs : 4 * P * s ≤ N := by
    have hb' : 4 * P * s ≤ (N ^ 2).sqrt := Nat.le_sqrt'.mpr hb
    simpa only [Nat.sqrt_eq'] using hb'
  calc
    4 * (Nat.smoothNumbersUpTo (K * N) (Q + 1)).card ≤ 4 * (P * s) :=
      Nat.mul_le_mul_left 4 hcount
    _ = 4 * P * s := by ring
    _ ≤ N := hbs

theorem uniform_nat_window (K : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N ≥ N₀, ∀ A : ResidueSystem, A.InNatWindow K N → δ ≤ A.uncoveredDensity := by
  obtain ⟨Q, hQ, hcut⟩ := exists_large_cutoff K
  let b : ℝ := 2 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q
  let a : ℝ := Real.exp (-8 * (K + 1 : ℝ))
  let δ : ℝ := a / 2 - b
  have hdouble : 2 * b = 4 * eulerConstant27 * (K : ℝ) ^ 2 * Real.log Q / Q := by
    dsimp only [b]
    ring
  have hb : 2 * b < a := by
    rw [hdouble]
    exact hcut
  have hδ : 0 < δ := by
    change 0 < a / 2 - b
    apply sub_pos.mpr
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    rwa [mul_comm]
  have ht : 0 < threshold Q K := by
    unfold threshold
    positivity
  refine ⟨δ, hδ, threshold Q K, ht, ?_⟩
  intro N hN A hw
  have hn := ht.trans_le hN
  have hA := sum_fibreAlpha_lower Q A hn hw (smooth_sparse_eventually Q K N hN)
  change (smallPeriod Q A : ℝ) * a ≤
    2 * (∑ h : ZMod (smallPeriod Q A), fibreAlpha Q A h) at hA
  have hB :=
    (sum_fibreBeta_le_pairKernel Q A).trans
      (mul_le_mul_of_nonneg_left (pairKernel_le_log_div Q A hQ hn hw) (by positivity))
  change (∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h) ≤
    (smallPeriod Q A : ℝ) * b at hB
  have hbridge : (smallPeriod Q A : ℝ) * δ ≤
      ∑ h : ZMod (smallPeriod Q A),
        (Erdos277.residueMeasure (roughPeriod Q A)).real (survives Q A h) := by
    calc
      (smallPeriod Q A : ℝ) * δ =
          ((smallPeriod Q A : ℝ) * a) / 2 - (smallPeriod Q A : ℝ) * b := by
        dsimp only [δ]
        ring
      _ ≤ (∑ h : ZMod (smallPeriod Q A), fibreAlpha Q A h) -
          (∑ h : ZMod (smallPeriod Q A), fibreBeta Q A h) := by
        exact sub_le_sub (by linarith only [hA]) hB
      _ = ∑ h : ZMod (smallPeriod Q A), (fibreAlpha Q A h - fibreBeta Q A h) :=
        by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ h : ZMod (smallPeriod Q A),
          (Erdos277.residueMeasure (roughPeriod Q A)).real (survives Q A h) :=
        Finset.sum_le_sum (fun h _ => fibre_residual_measure_lower Q A h)
  have hp : 0 < (smallPeriod Q A : ℝ) := by
    exact_mod_cast smallPeriod_pos Q A
  exact (mul_le_mul_iff_right₀ hp).mp (hbridge.trans (summed_survival_le_density Q A))

theorem erdos27_fixed_ratio_uniform (K : ℝ) (hK : 1 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℝ, (N₀ : ℝ) ≤ N →
        ∀ A : ResidueSystem, InFFKPYWindow A K N →
          δ ≤ A.uncoveredDensity ∧ Erdos281.HasIntDensity A.uncovered A.uncoveredDensity := by
  let J : ℕ := ⌈K⌉₊
  obtain ⟨δ, hδ, N₀, hN₀, hbound⟩ := uniform_nat_window J
  refine ⟨δ, hδ, N₀, hN₀, ?_⟩
  intro N hN A hA
  let L : ℕ := ⌈N⌉₊
  have hNL : N ≤ (L : ℝ) := Nat.le_ceil N
  have hJL : K ≤ (J : ℝ) := Nat.le_ceil K
  have hNL' : N₀ ≤ L := by exact_mod_cast hN.trans hNL
  have hw : A.InNatWindow J L := by
    intro m hm
    obtain ⟨hlo, hhi⟩ := hA m hm
    constructor
    · change ⌈N⌉₊ ≤ m
      exact Nat.ceil_le.mpr hlo.le
    · have hh : (m : ℝ) ≤ (J : ℝ) * (L : ℝ) :=
        calc
          (m : ℝ) ≤ K * N := hhi
          _ ≤ K * (L : ℝ) := mul_le_mul_of_nonneg_left hNL (by linarith)
          _ ≤ (J : ℝ) * (L : ℝ) := mul_le_mul_of_nonneg_right hJL (by positivity)
      exact_mod_cast hh
  exact ⟨hbound L hNL' A hw, uncovered_hasIntDensity A⟩

#print axioms uniform_nat_window
#print axioms erdos27_fixed_ratio_uniform

end
end JSP000060
