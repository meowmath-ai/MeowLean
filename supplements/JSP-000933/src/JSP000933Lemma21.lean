import Mathlib

open scoped BigOperators

namespace JSP000933

noncomputable section

abbrev Word (ι : Type*) := ι → Bool

def totalWeight {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ := ∑ i, w i

def weightedDist {ι : Type*} [Fintype ι] (w : ι → ℝ) (x y : Word ι) : ℝ :=
  ∑ i, if x i = y i then 0 else w i

private theorem small_symmetric_exp {z : ℝ} (hz : |z| ≤ 1) :
    Real.exp z + Real.exp (-z) ≤ 2 * Real.exp (z ^ 2) := by
  have hz' : |-z| ≤ 1 := by simpa only [abs_neg] using hz
  have hp := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hz)).2
  have hm := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hz')).2
  have he := Real.add_one_le_exp (z ^ 2)
  nlinarith only [hp, hm, he]

theorem expMoment_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (y : Word ι) (t : ℝ) :
    (∑ x : Word ι, Real.exp (t * (totalWeight w / 2 - weightedDist w x y))) =
      ∏ i, (Real.exp (t * (w i / 2)) + Real.exp (-(t * (w i / 2)))) := by
  classical
  have hexp (x : Word ι) :
      t * (totalWeight w / 2 - weightedDist w x y) =
        ∑ i, t * (if x i = y i then w i / 2 else -(w i / 2)) := by
    unfold totalWeight weightedDist
    rw [Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  calc
    _ = ∑ x : Word ι, ∏ i, Real.exp (t * (if x i = y i then w i / 2 else -(w i / 2))) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hexp, Real.exp_sum]
    _ = ∏ i, ∑ b : Bool, Real.exp (t * (if b = y i then w i / 2 else -(w i / 2))) :=
      (Fintype.prod_sum (fun i (b : Bool) => Real.exp
        (t * (if b = y i then w i / 2 else -(w i / 2))))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      cases hi : y i <;> simp [Fintype.sum_bool, hi, mul_neg, add_comm]

theorem expMoment_le_budget {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (y : Word ι) (t : ℝ) (ht : ∀ i, |t * (w i / 2)| ≤ 1) :
    (∑ x : Word ι, Real.exp (t * (totalWeight w / 2 - weightedDist w x y))) ≤
      (Fintype.card (Word ι) : ℝ) * Real.exp (∑ i, (t * (w i / 2)) ^ 2) := by
  rw [expMoment_eq_product]
  calc
    _ ≤ ∏ i : ι, (2 : ℝ) * Real.exp ((t * (w i / 2)) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        exact small_symmetric_exp (ht i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      simp [Fintype.card_fun] <;> norm_cast

theorem far_word_of_exp_budget {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (C : Finset (Word ι)) (ε t : ℝ) (ht0 : 0 ≤ t)
    (ht : ∀ i, |t * (w i / 2)| ≤ 1)
    (hbudget : (C.card : ℝ) * Real.exp (∑ i, (t * (w i / 2)) ^ 2) <
      Real.exp (t * (totalWeight w / 2 - ε))) :
    ∃ x : Word ι, ∀ y ∈ C, ε < weightedDist w x y := by
  classical
  by_contra hno
  have hcov (x : Word ι) : ∃ y ∈ C, weightedDist w x y ≤ ε := by
    by_contra hbad
    apply hno
    refine ⟨x, ?_⟩
    intro y hy
    exact lt_of_not_ge (fun hle => hbad ⟨y, hy, hle⟩)
  let E := Real.exp (t * (totalWeight w / 2 - ε))
  let Q := ∑ i, (t * (w i / 2)) ^ 2
  let f (x y : Word ι) := Real.exp (t * (totalWeight w / 2 - weightedDist w x y))
  let M : ℝ := Fintype.card (Word ι)
  have hrow (x : Word ι) : E ≤ ∑ y ∈ C, f x y := by
    obtain ⟨y, hy, hd⟩ := hcov x
    have hm : E ≤ f x y := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (by linarith) ht0
    exact hm.trans (Finset.single_le_sum
      (fun j _ => Real.exp_nonneg (t * (totalWeight w / 2 - weightedDist w x j))) hy)
  have hlower : M * E ≤ ∑ x : Word ι, ∑ y ∈ C, f x y := by
    calc
      M * E = ∑ _x : Word ι, E := by simp [M, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => hrow x)
  have hupper : (∑ x : Word ι, ∑ y ∈ C, f x y) ≤ M * ((C.card : ℝ) * Real.exp Q) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _y ∈ C, M * Real.exp Q :=
        Finset.sum_le_sum (fun y _ => expMoment_le_budget w y t ht)
      _ = _ := by simp [nsmul_eq_mul] <;> ring
  have hM : 0 < M := by
    letI : Nonempty (Word ι) := ⟨fun _ => false⟩
    have hn : 0 < Fintype.card (Word ι) := Fintype.card_pos
    change (0 : ℝ) < (Fintype.card (Word ι) : ℝ)
    exact_mod_cast hn
  have hstrict : M * ((C.card : ℝ) * Real.exp Q) < M * E :=
    mul_lt_mul_of_pos_left hbudget hM
  exact (not_le_of_gt hstrict) (hlower.trans hupper)

theorem far_word_quarter {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (C : Finset (Word ι)) {A : ℝ} (hA : 0 < A)
    (hw0 : ∀ i, 0 ≤ w i) (hwA : ∀ i, w i ≤ A)
    (hsize : (C.card : ℝ) < Real.exp (totalWeight w / (16 * A))) :
    ∃ x : Word ι, ∀ y ∈ C, totalWeight w / 4 < weightedDist w x y := by
  let t : ℝ := 1 / (2 * A)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htA : t * A = 1 / 2 := by
    dsimp [t]
    field_simp [ne_of_gt hA] <;> ring
  have hcap (i : ι) : 0 ≤ t * (w i / 2) ∧ t * (w i / 2) ≤ 1 / 4 := by
    refine ⟨mul_nonneg ht0.le (div_nonneg (hw0 i) (by norm_num)), ?_⟩
    have h := mul_le_mul_of_nonneg_left (hwA i) ht0.le
    linarith only [h, htA, show t * (w i / 2) = (t * w i) / 2 by ring]
  have ht (i : ι) : |t * (w i / 2)| ≤ 1 := by
    rw [abs_of_nonneg (hcap i).1]
    linarith [(hcap i).2]
  have hQ : (∑ i, (t * (w i / 2)) ^ 2) ≤ t * totalWeight w / 8 := by
    calc
      _ ≤ ∑ i, (t / 8) * w i := by
        apply Finset.sum_le_sum
        intro i _
        have hh := mul_le_mul_of_nonneg_left (hcap i).2 (hcap i).1
        nlinarith only [hh]
      _ = t * totalWeight w / 8 := by
        rw [← Finset.mul_sum, totalWeight]
        ring
  have he : totalWeight w / (16 * A) = t * totalWeight w / 8 := by
    dsimp [t]
    field_simp [ne_of_gt hA] <;> ring
  apply far_word_of_exp_budget w C (totalWeight w / 4) t ht0.le ht
  calc
    _ < Real.exp (totalWeight w / (16 * A)) * Real.exp (∑ i, (t * (w i / 2)) ^ 2) :=
      mul_lt_mul_of_pos_right hsize (Real.exp_pos _)
    _ = Real.exp (totalWeight w / (16 * A) + (∑ i, (t * (w i / 2)) ^ 2)) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [he]
      linarith only [hQ, show t * (totalWeight w / 2 - totalWeight w / 4) =
        t * totalWeight w / 4 by ring]

def harmonicAtom (m : ℕ) : ℝ := ((m : ℝ) + 1)⁻¹

def harmonicSum (p : ℕ) : ℝ := ∑ m ∈ Finset.range p, harmonicAtom m

def prefixBlock (w : Finset ℕ) (p : ℕ) : Finset ℕ := w.filter fun m => m < p

def logPrefixMass (w : Finset ℕ) (p : ℕ) : ℝ :=
  ∑ m ∈ prefixBlock w p, harmonicAtom m

def logPrefixDensity (w : Finset ℕ) (p : ℕ) : ℝ :=
  logPrefixMass w p / harmonicSum p

def xorFinset (z y : Finset ℕ) : Finset ℕ := (z \ y) ∪ (y \ z)

private theorem harmonicAtom_nonneg (m : ℕ) : 0 ≤ harmonicAtom m := by
  unfold harmonicAtom
  positivity

private theorem one_le_harmonicSum {p : ℕ} (hp : 0 < p) : 1 ≤ harmonicSum p := by
  unfold harmonicSum
  have h :=
    Finset.single_le_sum (f := harmonicAtom) (fun m _ => harmonicAtom_nonneg m)
      (Finset.mem_range.mpr hp)
  simpa [harmonicAtom] using h

private def restrictWord (S y : Finset ℕ) : Word ↥S := fun i => decide (i.1 ∈ y)

private def wordSet (S : Finset ℕ) (x : Word ↥S) : Finset ℕ := by
  classical
  exact S.filter (fun m => if h : m ∈ S then x ⟨m, h⟩ = true else False)

private theorem wordSet_subset (S : Finset ℕ) (x : Word ↥S) : wordSet S x ⊆ S := by
  classical
  unfold wordSet
  exact Finset.filter_subset _ _

private theorem restrictWord_wordSet (S : Finset ℕ) (x : Word ↥S) :
    restrictWord S (wordSet S x) = x := by
  classical
  funext i
  cases hi : x i <;> simp [restrictWord, wordSet, i.2, hi]

private theorem totalWeight_harmonic (S : Finset ℕ) :
    totalWeight (fun i : ↥S => harmonicAtom i.1) = ∑ m ∈ S, harmonicAtom m := by
  unfold totalWeight
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach S harmonicAtom

private theorem weightedDist_harmonic (w z y : Finset ℕ) (p : ℕ) (hz : z ⊆ w)
    (hy : y ⊆ w) :
    weightedDist (fun i : ↥(prefixBlock w p) => harmonicAtom i.1)
      (restrictWord (prefixBlock w p) z) (restrictWord (prefixBlock w p) y) =
      logPrefixMass (xorFinset z y) p := by
  have hsub : xorFinset z y ⊆ w := by
    intro m hm
    simp only [xorFinset, Finset.mem_union, Finset.mem_sdiff] at hm
    rcases hm with h | h
    · exact hz h.1
    · exact hy h.1
  have hfilter : prefixBlock (xorFinset z y) p =
      (prefixBlock w p).filter (fun m => m ∈ xorFinset z y) := by
    ext m
    simp only [prefixBlock, Finset.mem_filter]
    exact ⟨fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩
  unfold logPrefixMass weightedDist
  rw [hfilter, Finset.sum_filter, Finset.univ_eq_attach]
  calc
    _ = ∑ i ∈ (prefixBlock w p).attach,
          (if i.1 ∈ xorFinset z y then harmonicAtom i.1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hz' : i.1 ∈ z <;> by_cases hy' : i.1 ∈ y <;>
        simp [restrictWord, xorFinset, Finset.mem_union, Finset.mem_sdiff, hz', hy']
    _ = _ := Finset.sum_attach (prefixBlock w p)
      (fun m => if m ∈ xorFinset z y then harmonicAtom m else 0)

def STPrefix : Prop :=
  ∃ γ μ : ℝ, 0 < γ ∧ 0 < μ ∧
    ∀ ε : ℝ, 0 < ε → ∀ l : ℕ,
      ∃ (n : ℕ) (w : Finset ℕ) (C : Finset (Finset ℕ)),
        l < n ∧
        (∀ m ∈ w, Real.exp ((n : ℝ) * γ) < (m : ℝ)) ∧
        (∃ p, μ < logPrefixDensity w p) ∧
        C.card ≤ 2 ^ n ∧
        (∀ y ∈ C, y ⊆ w) ∧
        ∀ z : Finset ℕ, z ⊆ w → ∃ y ∈ C,
          ∀ p, logPrefixDensity (xorFinset z y) p ≤ ε

private theorem exp_rate {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ) :
    ∃ l : ℕ, ∀ n > l, (n : ℝ) < (μ / 16) * Real.exp ((n : ℝ) * γ) := by
  have hden : 0 < μ * γ ^ 2 := by positivity
  obtain ⟨l, hl⟩ := exists_nat_gt ((32 : ℝ) / (μ * γ ^ 2))
  refine ⟨l, ?_⟩
  intro n hn
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast ((Nat.zero_le l).trans_lt hn)
  have hln : (l : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul : 32 < (n : ℝ) * (μ * γ ^ 2) := (div_lt_iff₀ hden).mp (hl.trans hln)
  calc
    (n : ℝ) < (μ / 16) * (((n : ℝ) * γ) ^ 2 / 2) := by
      have hmul' := mul_lt_mul_of_pos_left hmul hn0
      nlinarith only [hmul']
    _ ≤ (μ / 16) * Real.exp ((n : ℝ) * γ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hx : 0 ≤ (n : ℝ) * γ := mul_nonneg hn0.le hγ.le
      exact (by linarith only [hx] :
        ((n : ℝ) * γ) ^ 2 / 2 ≤ 1 + (n : ℝ) * γ + ((n : ℝ) * γ) ^ 2 / 2).trans
        (Real.quadratic_le_exp_of_nonneg hx)

theorem not_STPrefix : ¬ STPrefix := by
  classical
  unfold STPrefix
  rintro ⟨γ, μ, hγ, hμ, hST⟩
  obtain ⟨l, hl⟩ := exp_rate hγ hμ
  obtain ⟨n, w, C, hln, hmin, ⟨p, hp⟩, hCcard, hCsub, hcover⟩ :=
    hST (μ / 4) (by positivity) l
  have hp0 : 0 < p := by
    by_contra hn
    have hpz : p = 0 := by omega
    subst p
    have hzero : μ < 0 := by simpa [logPrefixDensity, harmonicSum] using hp
    exact (not_lt_of_ge hμ.le) hzero
  have hH1 := one_le_harmonicSum hp0
  have hH : 0 < harmonicSum p := zero_lt_one.trans_le hH1
  let S := prefixBlock w p
  let a : ↥S → ℝ := fun i => harmonicAtom i.1
  let A := Real.exp (-((n : ℝ) * γ))
  let D : Finset (Word ↥S) := C.image (restrictWord S)
  have hM : μ * harmonicSum p < totalWeight a := by
    have h := (lt_div_iff₀ hH).mp hp
    simpa only [a, totalWeight_harmonic, S, logPrefixMass] using h
  have hA : 0 < A := Real.exp_pos _
  have hAatom (i : ↥S) : a i ≤ A := by
    have hsub : S ⊆ w := Finset.filter_subset _ _
    have hi : i.1 ∈ w := hsub i.2
    have hm := hmin i.1 hi
    have hh : Real.exp ((n : ℝ) * γ) ≤ (i.1 : ℝ) + 1 := by linarith only [hm]
    change ((i.1 : ℝ) + 1)⁻¹ ≤ Real.exp (-((n : ℝ) * γ))
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hh
  have hbound : (n : ℝ) < totalWeight a / (16 * A) := by
    have hμM : μ < totalWeight a := by
      calc
        μ = μ * 1 := (mul_one μ).symm
        _ ≤ μ * harmonicSum p := mul_le_mul_of_nonneg_left hH1 hμ.le
        _ < _ := hM
    have hcompare :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hμM.le (by norm_num : (0 : ℝ) ≤ 16))
        (Real.exp_pos ((n : ℝ) * γ)).le
    apply (hl n hln).trans_le
    calc
      _ ≤ (totalWeight a / 16) * Real.exp ((n : ℝ) * γ) := hcompare
      _ = _ := by
        dsimp [A]
        rw [Real.exp_neg]
        field_simp [ne_of_gt (Real.exp_pos ((n : ℝ) * γ))] <;> ring
  have hDnat : D.card ≤ 2 ^ n := by
    have himage : D.card ≤ C.card := Finset.card_image_le
    exact himage.trans hCcard
  have hDreal : (D.card : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hDnat
  have hpower : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1 : ℝ) using 1 <;> norm_num
    calc
      _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) he n
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  have hD : (D.card : ℝ) < Real.exp (totalWeight a / (16 * A)) :=
    (hDreal.trans hpower).trans_lt (Real.exp_lt_exp.mpr hbound)
  obtain ⟨x, hx⟩ := far_word_quarter a D hA (fun i => harmonicAtom_nonneg i.1) hAatom hD
  let z := wordSet S x
  have hz : z ⊆ w := (wordSet_subset S x).trans (Finset.filter_subset _ _)
  obtain ⟨y, hy, hclose⟩ := hcover z hz
  have hyD : restrictWord S y ∈ D := by
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hfar := hx (restrictWord S y) hyD
  have hxy : weightedDist a x (restrictWord S y) = logPrefixMass (xorFinset z y) p := by
    have h := weightedDist_harmonic w z y p hz (hCsub y hy)
    have hr : restrictWord S z = x := restrictWord_wordSet S x
    change weightedDist a (restrictWord S z) (restrictWord S y) = _ at h
    simpa only [hr] using h
  have hnear : logPrefixMass (xorFinset z y) p ≤ (μ / 4) * harmonicSum p :=
    (div_le_iff₀ hH).mp (hclose p)
  rw [hxy] at hfar
  linarith only [hM, hfar, hnear]

def logConcentration (w : Finset ℕ) : ℝ :=
  sSup (Set.range (logPrefixDensity w))

private theorem logPrefixDensity_le_one (w : Finset ℕ) (p : ℕ) :
    logPrefixDensity w p ≤ 1 := by
  by_cases hp : p = 0
  · subst p
    simp [logPrefixDensity, harmonicSum]
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    have hpos : 0 < harmonicSum p := zero_lt_one.trans_le (one_le_harmonicSum hp0)
    have hsub : prefixBlock w p ⊆ Finset.range p := by
      intro m hm
      exact Finset.mem_range.mpr ((Finset.mem_filter.mp hm).2)
    apply (div_le_iff₀ hpos).mpr
    rw [one_mul]
    unfold logPrefixMass harmonicSum
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => harmonicAtom_nonneg m)

theorem logConcentration_le_iff (w : Finset ℕ) (a : ℝ) :
    logConcentration w ≤ a ↔ ∀ p, logPrefixDensity w p ≤ a := by
  unfold logConcentration
  have hb : BddAbove (Set.range (logPrefixDensity w)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact logPrefixDensity_le_one w p
  constructor
  · intro h p
    exact (le_csSup hb ⟨p, rfl⟩).trans h
  · intro h
    refine csSup_le (s := Set.range (logPrefixDensity w)) ⟨logPrefixDensity w 0, ⟨0, rfl⟩⟩ ?_
    rintro _ ⟨p, rfl⟩
    exact h p

theorem lt_logConcentration_iff (w : Finset ℕ) (a : ℝ) :
    a < logConcentration w ↔ ∃ p, a < logPrefixDensity w p := by
  classical
  constructor
  · intro h
    by_contra hn
    apply (not_le_of_gt h)
    exact (logConcentration_le_iff w a).mpr
      (fun p => le_of_not_gt (fun hp => hn ⟨p, hp⟩))
  · rintro ⟨p, hp⟩
    by_contra hn
    exact (not_le_of_gt hp) ((logConcentration_le_iff w a).mp (le_of_not_gt hn) p)

def STByConcentration : Prop :=
  ∃ γ μ : ℝ, 0 < γ ∧ 0 < μ ∧
    ∀ ε : ℝ, 0 < ε → ∀ l : ℕ,
      ∃ (n : ℕ) (w : Finset ℕ) (C : Finset (Finset ℕ)),
        l < n ∧
        (∀ m ∈ w, Real.exp ((n : ℝ) * γ) < (m : ℝ)) ∧
        μ < logConcentration w ∧
        C.card ≤ 2 ^ n ∧
        (∀ y ∈ C, y ⊆ w) ∧
        ∀ z : Finset ℕ, z ⊆ w → ∃ y ∈ C,
          logConcentration (xorFinset z y) ≤ ε

theorem STByConcentration_iff : STByConcentration ↔ STPrefix := by
  unfold STByConcentration STPrefix
  constructor
  · rintro ⟨γ, μ, hγ, hμ, h⟩
    refine ⟨γ, μ, hγ, hμ, ?_⟩
    intro ε hε l
    obtain ⟨n, w, C, hln, hmin, hmass, hcard, hsub, hc⟩ := h ε hε l
    refine ⟨n, w, C, hln, hmin, (lt_logConcentration_iff w μ).mp hmass, hcard, hsub, ?_⟩
    intro z hz
    obtain ⟨y, hy, hclose⟩ := hc z hz
    exact ⟨y, hy, (logConcentration_le_iff (xorFinset z y) ε).mp hclose⟩
  · rintro ⟨γ, μ, hγ, hμ, h⟩
    refine ⟨γ, μ, hγ, hμ, ?_⟩
    intro ε hε l
    obtain ⟨n, w, C, hln, hmin, hmass, hcard, hsub, hc⟩ := h ε hε l
    refine ⟨n, w, C, hln, hmin, (lt_logConcentration_iff w μ).mpr hmass, hcard, hsub, ?_⟩
    intro z hz
    obtain ⟨y, hy, hclose⟩ := hc z hz
    exact ⟨y, hy, (logConcentration_le_iff (xorFinset z y) ε).mpr hclose⟩

theorem not_STByConcentration : ¬ STByConcentration :=
  fun h => not_STPrefix (STByConcentration_iff.mp h)

end

end JSP000933
