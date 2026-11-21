import JSP000930NegativeActualFineTower

open Lattice Filter
open scoped Flypitch bSet Topology

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem cutoffNear {u : ℕ → RatPresentation → B} {v : RatPresentation → B}
    {p : B} {ε : ℚ} {N i : ℕ} (h : p ≤ cutConvergesTail u v ε N) (hi : N ≤ i) :
    p ≤ cutNear (u i) v ε := h.trans (iInf_le _ (⟨i,hi⟩ : {n : ℕ // N ≤ n}))

theorem distanceLe_of_named_cut_limit (u : ℕ → ComplexBits B) (l v : ComplexBits B) (m : B)
    (hu : ∀ t,(u t).CutOn m) (hl : l.CutOn m) (hv : v.CutOn m)
    (hLim : ∀ b : Bool,∀ e : ℚ,0 < e → m ≤ ⨆ N : ℕ,
      cutConvergesTail (fun t => (u t).coord b) (l.coord b) e N)
    (e : ℚ) (he : 0 ≤ e) (N : ℕ) (hDist : ∀ t ≥ N,m ≤ distanceLe (u t) v e) :
    m ≤ distanceLe l v e := by
  by_contra hBad
  obtain ⟨q,r,s,hs,hsm,hqr,hLo,hHi⟩ :=
    nonzero_cut_order_countercell (proper_distanceCut hl hv) hBad
  let name (i : Option (Option ℕ)) : ComplexBits B := match i with
    | none => l
    | some none => v
    | some (some t) => u t
  let β (i : Option (Option ℕ) × Bool) := (name i.1).coord i.2
  have hName (i : Option (Option ℕ)) : (name i).CutOn m := by
    cases i with
    | none => exact hl
    | some i =>
      cases i with
      | none => exact hv
      | some t => exact hu t
  have hβ (i : Option (Option ℕ) × Bool) : ProperCutOn s (β i) := by
    have h := JSP000930.AnalyticSyntax.complexCutOn_mono hsm (hName i.1)
    rcases i with ⟨i,b⟩
    cases b
    · exact h.1
    · exact h.2
  let δ (k : ℕ) : ℚ := (1/2)^k
  let V (b : Bool) (k K : ℕ) :=
    cutConvergesTail (fun t => (u t).coord b) (l.coord b) (δ k) K
  let W (k : ℕ) (i : ℕ × ℕ) := V false k i.1 ⊓ V true k i.2
  have hW (k : ℕ) : s ≤ ⨆ i,W k i := by
    have hR := hLim false (δ k) (by dsimp [δ]; positivity)
    have hI := hLim true (δ k) (by dsimp [δ]; positivity)
    unfold W
    rw [← iSup_inf_iSup]
    exact le_inf (hsm.trans hR) (hsm.trans hI)
  obtain ⟨p,cut,x,hp,hn,hps,hKeep,hT⟩ :=
    mixed_cut_decision_completion β s hs hβ W hW
  have hpm (n : ℕ) : p n ≤ m := (hps n).trans hsm
  let ground (i : Option (Option ℕ)) : ℂ := ⟨x (i,false),x (i,true)⟩
  have hTrace (i : Option (Option ℕ)) : ComplexDecisionTrace p (name i) (ground i) :=
    ⟨hT (i,false),hT (i,true)⟩
  let w (t : ℕ) : ℂ := ground (some (some t))
  let L := ground none
  let Y := ground (some none)
  have ht (t : ℕ) : ComplexDecisionTrace p (u t) (w t) := hTrace (some (some t))
  have hL : ComplexDecisionTrace p l L := hTrace none
  have hY : ComplexDecisionTrace p v Y := hTrace (some none)
  have hOrd (t : ℕ) (htN : N ≤ t) : dist (w t) Y ≤ (e : ℝ) :=
    trace_distanceLe hp hn hpm (hu t) hv (ht t) hY he (hDist t htN)
  have hWconv : Tendsto w atTop (𝓝 L) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε/2 by positivity)
      (show (1/2 : ℝ) < 1 by norm_num)
    let C := cut k
    refine ⟨max C.1 C.2,fun t ht0 => ?_⟩
    let p' (i : ℕ) := p (i+k)
    have hP' : Antitone p' := fun _ _ h => hp (Nat.add_le_add_right h k)
    have hpm' (i : ℕ) : p' i ≤ p k := hp (by omega)
    have hDist' : ‖w t-L‖ ≤ 2*(δ k : ℝ) :=
      trace_coord_distance_le hP' (fun i => hn (i+k)) hpm'
        ⟨(ht t).1.tail hp k,(ht t).2.tail hp k⟩
        ⟨hL.1.tail hp k,hL.2.tail hp k⟩
        (fun b => by
          cases b
          · exact cutoffNear ((hKeep k).trans inf_le_left) ((le_max_left _ _).trans ht0)
          · exact cutoffNear ((hKeep k).trans inf_le_right) ((le_max_right _ _).trans ht0))
    rw [dist_eq_norm]
    have hδ : (δ k : ℝ) < ε/2 := by simpa [δ] using hk
    linarith
  have hDistConv : Tendsto (fun t => dist (w t) Y) atTop (𝓝 (dist L Y)) :=
    ((continuous_id.dist continuous_const).continuousAt.tendsto).comp hWconv
  have hDistLim : dist L Y ≤ (e : ℝ) :=
    le_of_tendsto hDistConv (eventually_atTop.mpr ⟨N,hOrd⟩)
  have hNum := trace_distanceCut hp hpm hl hv hL hY
  have hLow := trace_forcedMember_le hp hn hNum r ⟨0,(hps 0).trans hLo⟩
  have hHigh := trace_forcedAbsent_ge hp hn (checkedRealBits_traces p ((e : ℝ)^2)) q
    ⟨0,(hps 0).trans hHi⟩
  have hqr' : (q.value : ℝ) < (r.value : ℝ) := by exact_mod_cast hqr
  exact (not_le_of_gt ((hHigh.trans_lt hqr').trans_le hLow))
    (pow_le_pow_left₀ dist_nonneg hDistLim 2)

theorem NamedPolynomialTower.limitCoeff_distance (T : NamedPolynomialTower B) (m : B)
    (h : T.On m) (R : ℕ) (hR : 0 < R) (e : ℚ) (he : 0 < e) :
    ∃ N : ℕ,∀ t ≥ N,∀ k : ℕ,
      m ≤ distanceLe (T.limitCoefficients k) (T.coefficient t k) (e/(R : ℚ)^k) := by
  obtain ⟨N,hN⟩ := T.coeffDistance m h R hR e he
  refine ⟨N,fun t ht k => ?_⟩
  exact distanceLe_of_named_cut_limit (fun n => T.coefficient n k)
    (T.limitCoefficients k) (T.coefficient t k) m
    (fun n => T.coefficient_proper m h n k) (T.limit_coeff_proper m h k)
    (T.coefficient_proper m h t k) (fun b a ha => T.limit_coeff_converges m h k b a ha)
    (e/(R : ℚ)^k) (by positivity) N (fun n hn => hN n t hn ht k)

end JSP000930.Negative
