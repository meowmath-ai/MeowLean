import JSP000930AnalyticTaylorPrefixUnique

open Lattice Filter
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def ComplexBits.sub (u v : ComplexBits B) : ComplexBits B := u.add v.neg

theorem ComplexBits.sub_cutOn {u v : ComplexBits B} {p : B}
    (hu : u.CutOn p) (hv : v.CutOn p) : (u.sub v).CutOn p :=
  ComplexBits.add_cutOn hu (ComplexBits.neg_cutOn hv)

noncomputable def evalErrorNumerator (u v : ComplexBits B) (k : ℕ) : RatPresentation → B :=
  mulCutBits (u.sub v).normSq (checkedRealBits ((k : ℝ)^2))

noncomputable def evalErrorBits (u v : ComplexBits B) (k : ℕ) : B :=
  let x := weightedRationalSet (evalErrorNumerator u v k)
  let one := weightedRationalSet (checkedRealBits (B := B) 1)
  (x ⊆ᴮ one) ⊓ (x =ᴮ one)ᶜ

theorem evalErrorNumerator_cutOn {u v : ComplexBits B} {p : B}
    (hu : u.CutOn p) (hv : v.CutOn p) (k : ℕ) :
    ProperCutOn p (evalErrorNumerator u v k) :=
  mulCutBits_properCut _ _ p (ComplexBits.normSq_cutOn (ComplexBits.sub_cutOn hu hv))
    (properCutOn_mono le_top (checkedRealBits_properCut _))

theorem evalErrorNumerator_trace {p : ℕ → B} (hp : Antitone p)
    {m : B} (hpm : ∀ n,p n ≤ m) {u v : ComplexBits B} {x y : ℂ}
    (hu : u.CutOn m) (hv : v.CutOn m)
    (hx : ComplexDecisionTrace p u x) (hy : ComplexDecisionTrace p v y) (k : ℕ) :
    CutDecisionTrace p (evalErrorNumerator u v k) ((k : ℝ)^2 * Complex.normSq (x-y)) := by
  have hs : ComplexDecisionTrace p (u.sub v) (x-y) := by
    simpa [ComplexBits.sub,sub_eq_add_neg] using hx.add hp hpm (hy.neg hpm hv) hu
      (ComplexBits.neg_cutOn hv)
  simpa only [evalErrorNumerator,mul_comm] using
    (hs.normSq hp hpm (ComplexBits.sub_cutOn hu hv)).mul hp hpm
      (checkedRealBits_traces p ((k : ℝ)^2))
      (ComplexBits.normSq_cutOn (ComplexBits.sub_cutOn hu hv))
      (properCutOn_mono le_top (checkedRealBits_properCut _))

theorem twoComplex_decisionCompletion (u v : ComplexBits B) (m : B)
    (hm : m ≠ ⊥) (hu : u.CutOn m) (hv : v.CutOn m) :
    ∃ (p : ℕ → B) (x y : ℂ),Antitone p ∧ (∀ n,p n ≠ ⊥) ∧ (∀ n,p n ≤ m) ∧
      ComplexDecisionTrace p u x ∧ ComplexDecisionTrace p v y := by
  let β : Bool × Bool → RatPresentation → B := fun i =>
    (if i.1 then v else u).coord i.2
  have hβ (i : Bool × Bool) : ProperCutOn m (β i) := by
    rcases i with ⟨i,j⟩
    cases i <;> cases j
    · exact hu.1
    · exact hu.2
    · exact hv.1
    · exact hv.2
  obtain ⟨p,sel,z,hp,hn,hpm,hSel,hz⟩ :=
    mixed_cut_decision_completion β m hm hβ (fun _ (_ : Unit) => ⊤)
      (by intro; exact le_iSup_of_le () le_top)
  exact ⟨p,⟨z (false,false),z (false,true)⟩,⟨z (true,false),z (true,true)⟩,
    hp,hn,hpm,⟨hz (false,false),hz (false,true)⟩,⟨hz (true,false),hz (true,true)⟩⟩

theorem trace_coord_distance_le {p : ℕ → B} (hp : Antitone p) (hn : ∀ n,p n ≠ ⊥)
    {m : B} (hpm : ∀ n,p n ≤ m) {u v : ComplexBits B} {x y : ℂ}
    (hx : ComplexDecisionTrace p u x) (hy : ComplexDecisionTrace p v y) {ε : ℚ}
    (he : ∀ i : Bool,m ≤ cutNear (u.coord i) (v.coord i) ε) :
    ‖x-y‖ ≤ 2*(ε : ℝ) := by
  have hr := trace_cutNear hp hn hpm (hx.coordinate false) (hy.coordinate false) (he false)
  have hi := trace_cutNear hp hn hpm (hx.coordinate true) (hy.coordinate true) (he true)
  have h := Complex.norm_le_abs_re_add_abs_im (x-y)
  simp [complexCoord] at hr hi
  rw [Complex.sub_re,Complex.sub_im] at h
  linarith

private theorem norm_lt_errorThreshold {x y : ℂ} {k : ℕ} (hk : 0 < k)
    (h : ‖x-y‖ < 1/(k : ℝ)) :
    (k : ℝ)^2 * Complex.normSq (x-y) < 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : ‖x-y‖ * (k : ℝ) < 1 := (lt_div_iff₀ hk').mp h
  have ht : 0 ≤ ‖x-y‖ * (k : ℝ) := by positivity
  rw [Complex.normSq_eq_norm_sq,← mul_pow]
  have hs' : (k : ℝ)*‖x-y‖ < 1 := by simpa [mul_comm] using hs
  have ht' : 0 ≤ (k : ℝ)*‖x-y‖ := by positivity
  nlinarith

private theorem norm_le_errorThreshold {x y : ℂ} {k : ℕ} (hk : 0 < k)
    (h : (k : ℝ)^2 * Complex.normSq (x-y) ≤ 1) :
    ‖x-y‖ ≤ 1/(k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply (le_div_iff₀ hk').2
  rw [Complex.normSq_eq_norm_sq,← mul_pow] at h
  have ht : 0 ≤ (k : ℝ)*‖x-y‖ := by positivity
  have hle : (k : ℝ)*‖x-y‖ ≤ 1 := by nlinarith
  simpa [mul_comm] using hle

theorem force_evalError_from_coord {u v : ComplexBits B} {m : B} {k : ℕ} {ε : ℚ}
    (hu : u.CutOn m) (hv : v.CutOn m) (hk : 0 < k)
    (he : ∀ i : Bool,m ≤ cutNear (u.coord i) (v.coord i) ε)
    (hsmall : 2*(ε : ℝ) < 1/(k : ℝ)) :
    m ≤ evalErrorBits u v k := by
  let A := evalErrorNumerator u v k
  let O := checkedRealBits (B := B) 1
  have hOne (s : B) (hs : s ≠ ⊥) (hsm : s ≤ m) :
      ∃ (p : ℕ → B) (x : ℝ), Antitone p ∧ (∀ n,p n ≠ ⊥) ∧
        (∀ n,p n ≤ s) ∧ CutDecisionTrace p A x ∧ x < 1 := by
    have hu' : u.CutOn s := ⟨properCutOn_mono hsm hu.1,properCutOn_mono hsm hu.2⟩
    have hv' : v.CutOn s := ⟨properCutOn_mono hsm hv.1,properCutOn_mono hsm hv.2⟩
    obtain ⟨p,x,y,hp,hn,hps,hx,hy⟩ := twoComplex_decisionCompletion u v s hs hu' hv'
    have hm' := trace_coord_distance_le hp hn hps hx hy (fun i => hsm.trans (he i))
    have hN : ‖x-y‖ < 1/(k : ℝ) := hm'.trans_lt hsmall
    exact ⟨p,_,hp,hn,hps,evalErrorNumerator_trace hp hps hu' hv' hx hy k,
      norm_lt_errorThreshold hk hN⟩
  apply le_inf
  · by_contra hBad
    obtain ⟨q,r,s,hs,hsm,hqr,hl,hh⟩ := nonzero_cut_order_countercell
      (evalErrorNumerator_cutOn hu hv k) hBad
    obtain ⟨p,x,hp,hn,hps,hx,hlt⟩ := hOne s hs hsm
    have hr := trace_forcedMember_le hp hn hx r ⟨0,(hps 0).trans hl⟩
    have hq := trace_forcedAbsent_ge hp hn (checkedRealBits_traces p 1) q ⟨0,(hps 0).trans hh⟩
    have hGap : (q.value : ℝ) < (r.value : ℝ) := by exact_mod_cast hqr
    linarith
  · by_contra hBad
    let s : B := m ⊓ (weightedRationalSet A =ᴮ weightedRationalSet O)
    have hs : s ≠ ⊥ := by
      intro heq
      exact hBad (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr (le_of_eq heq)))
    obtain ⟨p,x,hp,hn,hps,hx,hlt⟩ := hOne s hs inf_le_left
    have hEq : x = 1 := trace_cut_eq hp hn hps hx (checkedRealBits_traces p 1) inf_le_right
    exact (ne_of_lt hlt) hEq

theorem force_coord_from_evalError {u v : ComplexBits B} {m : B} {k : ℕ} {ε : ℚ}
    (hu : u.CutOn m) (hv : v.CutOn m) (hk : 0 < k) (he : m ≤ evalErrorBits u v k)
    (hbig : 1/(k : ℝ) < (ε : ℝ)) (i : Bool) :
    m ≤ cutNear (u.coord i) (v.coord i) ε := by
  have hs (rev : Bool) :
      m ≤ (if rev then directedNear (v.coord i) (u.coord i) ε else
        directedNear (u.coord i) (v.coord i) ε) := by
    by_contra hb
    let U := if rev then v else u
    let V := if rev then u else v
    have hb' : ¬ m ≤ directedNear (U.coord i) (V.coord i) ε := by
      cases rev <;> exact hb
    obtain ⟨q,r,s,hs,hsm,hqr,hl,hh⟩ := directedNear_countercell hb'
    have hu' : u.CutOn s := ⟨properCutOn_mono hsm hu.1,properCutOn_mono hsm hu.2⟩
    have hv' : v.CutOn s := ⟨properCutOn_mono hsm hv.1,properCutOn_mono hsm hv.2⟩
    obtain ⟨p,x,y,hp,hn,hps,htx,hty⟩ := twoComplex_decisionCompletion u v s hs hu' hv'
    have hE := evalErrorNumerator_trace hp hps hu' hv' htx hty k
    have hR := trace_subset_le hp hn hps hE (checkedRealBits_traces p 1)
      (hsm.trans (he.trans inf_le_left))
    have hD := norm_le_errorThreshold hk hR
    have hcoord (a b : ℂ) : |complexCoord a i-complexCoord b i| ≤ ‖a-b‖ := by
      cases i
      · simpa [complexCoord,Complex.sub_re] using Complex.abs_re_le_norm (a-b)
      · simpa [complexCoord,Complex.sub_im] using Complex.abs_im_le_norm (a-b)
    cases rev
    · have hgap := trace_directedNear_failure_forces_gap hp hn (htx.coordinate i)
        (hty.coordinate i) q r hqr ⟨0,(hps 0).trans hl⟩ ⟨0,(hps 0).trans hh⟩
      exact (not_le_of_gt hbig) (hgap.trans ((le_abs_self _).trans ((hcoord x y).trans hD)))
    · have hgap := trace_directedNear_failure_forces_gap hp hn (hty.coordinate i)
        (htx.coordinate i) q r hqr ⟨0,(hps 0).trans hl⟩ ⟨0,(hps 0).trans hh⟩
      have hrD : ‖y-x‖ ≤ 1/(k : ℝ) := by rwa [norm_sub_rev]
      exact (not_le_of_gt hbig) (hgap.trans ((le_abs_self _).trans ((hcoord y x).trans hrD)))
  exact le_inf (hs false) (hs true)

end JSP000930.BooleanAnalysis
