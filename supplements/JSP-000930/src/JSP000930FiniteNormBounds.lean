import JSP000930ActualDenseCohenPalettes

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checked_distanceLe {m : B} (x y : ℂ) (e : ℚ)
    (h : dist x y ≤ (e : ℝ)) :
    m ≤ distanceLe (ComplexBits.checked x) (ComplexBits.checked y) e := by
  by_contra hf
  obtain ⟨s,hs,hsM,hSep⟩ := cut_order_fail_survives
    (proper_distanceCut (ComplexBits.checked_cutOn x m) (ComplexBits.checked_cutOn y m)) hf
  let p : ℕ → B := fun _ => s
  have hP : Antitone p := fun _ _ _ => le_rfl
  have hNZ : ∀ n,p n ≠ ⊥ := fun _ => hs
  have hStrict := hSep hP hNZ (fun _ => le_rfl)
    (trace_distanceCut hP (fun _ => hsM) (ComplexBits.checked_cutOn x m)
      (ComplexBits.checked_cutOn y m) (checked_complex_traces p x) (checked_complex_traces p y))
    (checkedRealBits_traces p ((e : ℝ)^2))
  exact (not_le_of_gt hStrict) (pow_le_pow_left₀ dist_nonneg h 2)

theorem distanceLe_symm_mono {m : B} {x y : ComplexBits B}
    (hx : x.CutOn m) (hy : y.CutOn m) {e f : ℚ} (he : 0 ≤ e) (hef : e ≤ f)
    (h : m ≤ distanceLe x y e) : m ≤ distanceLe y x f := by
  let u : Bool → ComplexBits B := fun i => if i then y else x
  have hu : ∀ i, (u i).CutOn m := by
    intro i
    cases i
    · exact hx
    · exact hy
  refine distanceLe_of_finite_metric_law u m hu true false f ?_
  intro p w hp hnz hpm ht
  have hXY : dist (w false) (w true) ≤ (e : ℝ) :=
    trace_distanceLe hp hnz hpm hx hy (ht false) (ht true) he h
  have hEF : (e : ℝ) ≤ (f : ℝ) := by exact_mod_cast hef
  rw [dist_comm (w true) (w false)]
  exact pow_le_pow_left₀ dist_nonneg (hXY.trans hEF) 2

theorem distanceLe_mono {m : B} {x y : ComplexBits B}
    (hx : x.CutOn m) (hy : y.CutOn m) {e f : ℚ} (he : 0 ≤ e) (hef : e ≤ f)
    (h : m ≤ distanceLe x y e) : m ≤ distanceLe x y f :=
  distanceLe_symm_mono hy hx he hef (distanceLe_symm_mono hx hy he le_rfl h)

theorem exists_local_normBound (z : ComplexBits B) (m : B) (hm : m ≠ ⊥)
    (hz : z.CutOn m) :
    ∃ (s : B) (L : ℚ), s ≠ ⊥ ∧ s ≤ m ∧ 0 ≤ L ∧
      s ≤ distanceLe z (ComplexBits.checked (0 : ℂ)) L := by
  obtain ⟨a,b,c,d,s,hs,hsM,hab,hcd,hW₁,hW₂,he,hi⟩ :=
    exists_thin_complex_enclosure z m hm hz 1 (by norm_num)
  let L := |a.value| + |b.value| + |c.value| + |d.value|
  have hL : 0 ≤ L := by positivity
  have hZS : z.CutOn s := ⟨properCutOn_mono hsM hz.1,properCutOn_mono hsM hz.2⟩
  let u : Bool → ComplexBits B := fun j => if j then ComplexBits.checked (0 : ℂ) else z
  have hu : ∀ j, (u j).CutOn s := by
    intro j
    cases j
    · exact hZS
    · exact ComplexBits.checked_cutOn 0 s
  refine ⟨s,L,hs,hsM,hL,distanceLe_of_finite_metric_law u s hu false true L ?_⟩
  intro p w hp hnz hps ht
  have htZ : ComplexDecisionTrace p z (w false) := ht false
  have htO : ComplexDecisionTrace p (ComplexBits.checked (0 : ℂ)) (w true) := ht true
  have hZero := trace_complex_eq hp hnz hps htO (checked_complex_traces p 0)
    (le_top.trans bSet.bv_refl)
  have hRe := trace_enclosure_bounds hp hnz hps htZ.1 he
  have hIm := trace_enclosure_bounds hp hnz hps htZ.2 hi
  have hB {x l r : ℝ} (hl : l ≤ x) (hr : x ≤ r) : |x| ≤ |l| + |r| := by
    refine abs_le.mpr ⟨?_,?_⟩
    · linarith [neg_abs_le l, abs_nonneg r]
    · linarith [le_abs_self r, abs_nonneg l]
  have hN : ‖w false‖ ≤ (L : ℝ) := by
    have hbL := add_le_add (hB hRe.1 hRe.2) (hB hIm.1 hIm.2)
    apply (norm_le_re_im_abs _).trans
    simp only [L,Rat.cast_add,Rat.cast_abs]
    linarith
  have hD : dist (w false) (w true) ≤ (L : ℝ) := by
    rw [hZero,dist_zero_right]
    exact hN
  exact pow_le_pow_left₀ dist_nonneg hD 2

theorem exists_finite_normBound {V : Type} (u : V → ComplexBits B) (old : List V)
    (m : B) (hm : m ≠ ⊥) (hu : ∀ i, (u i).CutOn m) :
    ∃ (s : B) (L : ℚ), s ≠ ⊥ ∧ s ≤ m ∧ 0 ≤ L ∧
      ∀ i ∈ old, s ≤ distanceLe (u i) (ComplexBits.checked (0 : ℂ)) L := by
  induction old generalizing m with
  | nil => exact ⟨m,0,hm,le_rfl,le_rfl,fun i hi => (List.not_mem_nil hi).elim⟩
  | cons a old ih =>
    obtain ⟨s,L,hs,hsM,hL,hA⟩ := exists_local_normBound (u a) m hm (hu a)
    have huS : ∀ i, (u i).CutOn s := fun i =>
      ⟨properCutOn_mono hsM (hu i).1, properCutOn_mono hsM (hu i).2⟩
    obtain ⟨t,K,ht,hts,hK,hT⟩ := ih s hs huS
    refine ⟨t,max L K,ht,hts.trans hsM,hL.trans (le_max_left _ _),?_⟩
    intro i hi
    have huT : (u i).CutOn t :=
      ⟨properCutOn_mono hts (huS i).1,properCutOn_mono hts (huS i).2⟩
    have h0 := ComplexBits.checked_cutOn (B := B) 0 t
    rcases List.mem_cons.mp hi with he|he
    · exact distanceLe_mono huT h0 hL (le_max_left _ _)
        (he.symm ▸ (hts.trans hA))
    · exact distanceLe_mono huT h0 hK (le_max_right _ _) (hT i he)

end JSP000930.Negative
