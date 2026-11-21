import JSP000930AnalyticEvaluationTail

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem prefix_proper {a : ℕ → ComplexBits B} {z : ComplexBits B} {p : B}
    (ha : ∀ j,(a j).CutOn p) (hz : z.CutOn p) (n : ℕ) :
    (taylorPrefixBits a z n).CutOn p :=
  taylorPrefixBits_cutOn hz (m := n) (fun j _ => ha j) n le_rfl

private theorem tailAt {u : ℕ → RatPresentation → B} {v : RatPresentation → B}
    {p : B} {ε : ℚ} {N i : ℕ} (h : p ≤ cutConvergesTail u v ε N) (hi : N ≤ i) :
    p ≤ cutNear (u i) v ε := h.trans (iInf_le _ (⟨i,hi⟩ : {n : ℕ // N ≤ n}))

theorem taylorLimitBits_evalNative (a : ℕ → ComplexBits B) (z : ComplexBits B)
    (p : B) (ha : ∀ j,(a j).CutOn p) (hz : z.CutOn p) (hg : GrowthOn p a) :
    EvalNativeOn p a z (taylorLimitBits a z) := by
  intro k hk
  let ε : ℚ := 1/(4*(k : ℚ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsmall : 2*(ε : ℝ) < 1/(k : ℝ) := by
    have hc : (ε : ℝ) = 1/(4*(k : ℝ)) := by simp [ε]
    rw [hc]
    apply (lt_div_iff₀ hkr).2
    have hProd : 2*(1/(4*(k : ℝ)))*(k : ℝ) = 1/2 := by
      field_simp [ne_of_gt hkr] <;> ring
    rw [hProd]
    norm_num
  let w := taylorLimitBits a z
  let R (N : ℕ) : B := cutConvergesTail (fun n => (taylorPrefixBits a z n).coord false)
    (w.coord false) ε N
  let I (N : ℕ) : B := cutConvergesTail (fun n => (taylorPrefixBits a z n).coord true)
    (w.coord true) ε N
  have hR : p ≤ ⨆ N : ℕ,R N := taylorLimitBits_converges a z p ha hz hg false ε hε
  have hI : p ≤ ⨆ N : ℕ,I N := taylorLimitBits_converges a z p ha hz hg true ε hε
  have hW : w.CutOn p := taylorLimitBits_cutOn a z p ha hz hg
  apply (le_inf le_rfl (le_inf hR hI)).trans
  rw [iSup_inf_eq,inf_iSup_eq]
  refine iSup_le fun Nr => ?_
  rw [inf_iSup_eq,inf_iSup_eq]
  refine iSup_le fun Ni => ?_
  let s := p ⊓ (R Nr ⊓ I Ni)
  let N := max Nr Ni
  apply le_iSup_of_le N
  apply EvalErrorTail_intro
  intro n hn
  have hsp : s ≤ p := inf_le_left
  have hu := JSP000930.AnalyticSyntax.complexCutOn_mono hsp (prefix_proper ha hz n)
  have hw := JSP000930.AnalyticSyntax.complexCutOn_mono hsp hW
  refine force_evalError_from_coord (ε := ε) hu hw hk ?_ hsmall
  intro b
  cases b
  · exact tailAt (u := fun n => (taylorPrefixBits a z n).coord false)
      (v := w.coord false) (ε := ε) (N := Nr) (i := n)
      (inf_le_right.trans inf_le_left) ((le_max_left Nr Ni).trans hn)
  · exact tailAt (u := fun n => (taylorPrefixBits a z n).coord true)
      (v := w.coord true) (ε := ε) (N := Ni) (i := n)
      (inf_le_right.trans inf_le_right) ((le_max_right Nr Ni).trans hn)

theorem evalNative_coordinate_converges {a : ℕ → ComplexBits B} {z w : ComplexBits B}
    {p : B} (ha : ∀ j,(a j).CutOn p) (hz : z.CutOn p) (hw : w.CutOn p)
    (h : EvalNativeOn p a z w) (b : Bool) (ε : ℚ) (hε : 0 < ε) :
    p ≤ ⨆ N : ℕ, cutConvergesTail (fun n => (taylorPrefixBits a z n).coord b) (w.coord b) ε N := by
  have her : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨k,hk⟩ := exists_nat_gt (1/(ε : ℝ))
  have hk0' : (0 : ℝ) < (k : ℝ) := (one_div_pos.mpr her).trans hk
  have hk0 : 0 < k := by exact_mod_cast hk0'
  have hbig : 1/(k : ℝ) < (ε : ℝ) := by
    apply (div_lt_iff₀ hk0').2
    have hh := (div_lt_iff₀ her).1 hk
    simpa [mul_comm] using hh
  apply (le_inf le_rfl (h k hk0)).trans
  rw [inf_iSup_eq]
  refine iSup_le fun N => ?_
  apply le_iSup_of_le N
  show p ⊓ EvalErrorTail a z w k N ≤
    cutConvergesTail (fun n => (taylorPrefixBits a z n).coord b) (w.coord b) ε N
  unfold cutConvergesTail
  refine le_iInf fun i => ?_
  let s := p ⊓ EvalErrorTail a z w k N
  have hsp : s ≤ p := inf_le_left
  exact force_coord_from_evalError (JSP000930.AnalyticSyntax.complexCutOn_mono hsp (prefix_proper ha hz i.val))
    (JSP000930.AnalyticSyntax.complexCutOn_mono hsp hw) hk0
    (EvalErrorTail_project inf_le_right i.property) hbig b

theorem evalNative_unique {a : ℕ → ComplexBits B} {z w : ComplexBits B} {p : B}
    (ha : ∀ j,(a j).CutOn p) (hz : z.CutOn p) (hw : w.CutOn p)
    (hg : GrowthOn p a) (h : EvalNativeOn p a z w) :
    p ≤ w.name =ᴮ (taylorLimitBits a z).name := by
  let lim := taylorLimitBits a z
  have hlim := taylorLimitBits_cutOn a z p ha hz hg
  have hBit (b : Bool) : p ≤ weightedRationalSet (w.coord b) =ᴮ weightedRationalSet (lim.coord b) := by
    let u (n : ℕ) := (taylorPrefixBits a z n).coord b
    have hW : ProperCutOn p (w.coord b) := by
      cases b
      · exact hw.1
      · exact hw.2
    have hL : ProperCutOn p (lim.coord b) := by
      cases b
      · exact hlim.1
      · exact hlim.2
    exact cutConverges_unique_name u (w.coord b) (lim.coord b) p
      (fun e he => evalNative_coordinate_converges ha hz hw h b e he)
      (fun e he => taylorLimitBits_converges a z p ha hz hg b e he) hW.2.2.2 hL.2.2.2
  rw [ComplexBits.name_eq]
  exact le_inf (hBit false) (hBit true)

end JSP000930.BooleanAnalysis
