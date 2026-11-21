import JSP000930OldPinDenominatorTransport

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion JSP000933.CantorCodes

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

structure OldTracePinGuard (p : PolyTrace B J) (site : J → ComplexBits B) (z : J) (m : B) where
  L : ℚ
  r : ℚ
  d : RatPresentation
  L_nonneg : 0 ≤ L
  r_pos : 0 < r
  d_sq : r^2 ≤ d.value
  old_norm : ∀ i ∈ p.pins,m ≤ distanceLe (site i) (ComplexBits.checked (0 : ℂ)) L
  denominator : m ≤ ((traceDenominator p).eval (traceEnv p site z (ComplexBits.checked 0))).normSq d

def OldTracePinGuard.mono {p : PolyTrace B J} {site : J → ComplexBits B} {z : J} {m s : B}
    (G : OldTracePinGuard p site z m) (h : s ≤ m) : OldTracePinGuard p site z s :=
  ⟨G.L,G.r,G.d,G.L_nonneg,G.r_pos,G.d_sq,fun i hi => h.trans (G.old_norm i hi),h.trans G.denominator⟩

def OldTracePinGuard.congr_site {p : PolyTrace B J} {site : J → ComplexBits B}
    {z z' : J} {m : B} (G : OldTracePinGuard p site z m) (h : z = z') :
    OldTracePinGuard p site z' m := h ▸ G

theorem OldTracePinGuard.congr_site_L {p : PolyTrace B J} {site : J → ComplexBits B}
    {z z' : J} {m : B} (G : OldTracePinGuard p site z m) (h : z = z') :
    (G.congr_site h).L = G.L := by cases h; rfl

theorem OldTracePinGuard.congr_site_r {p : PolyTrace B J} {site : J → ComplexBits B}
    {z z' : J} {m : B} (G : OldTracePinGuard p site z m) (h : z = z') :
    (G.congr_site h).r = G.r := by cases h; rfl

theorem exists_oldTracePinGuard (p : PolyTrace B J) (site : J → ComplexBits B) (z : J)
    (m : B) (hm : m ≠ ⊥) (hCoeff : m ≤ coeffValue p.coeff)
    (hSite : ∀ i,(site i).CutOn m)
    (hApart : ∀ i ∈ p.pins,m ≤ ((site z).name =ᴮ (site i).name)ᶜ) :
    ∃ s : B,s ≠ ⊥ ∧ s ≤ m ∧ Nonempty (OldTracePinGuard p site z s) := by
  let O : ComplexBits B := ComplexBits.checked 0
  let u := traceEnv p site z O
  let a := oldSiteAtoms p
  let iz := newSiteAtom p
  let D := traceDenominator p
  haveI : Countable (TraceAtoms p) := inferInstance
  haveI : Nonempty (TraceAtoms p) := ⟨iz⟩
  have hu : ∀ i,(u i).CutOn m :=
    traceEnv_cutOn p site z O hCoeff hSite (ComplexBits.checked_cutOn 0 m)
  have hApart' : ∀ i ∈ a,m ≤ ((u iz).name =ᴮ (u i).name)ᶜ := by
    intro i hi
    obtain ⟨j,rfl⟩ := oldSiteAtoms_mem p hi
    exact hApart j.1 j.2
  have hD : m ≤ positiveCutValue (D.eval u).normSq :=
    named_vanishing_positive u iz a m hu hApart'
  obtain ⟨k,L,hk,hkM,hL,hOld⟩ := exists_finite_normBound u a m hm hu
  obtain ⟨d,s,hs,hsK,hSD⟩ := exists_nonzero_below_choice_r135 k hk
    (fun d : {d : RatPresentation // 0 < d.value} => (D.eval u).normSq d.1) (hkM.trans hD)
  let r : ℚ := min 1 d.1.value
  have hr : 0 < r := lt_min zero_lt_one d.2
  have hrSq : r^2 ≤ d.1.value := by
    have hr1 : r ≤ 1 := min_le_left _ _
    have hr2 : r^2 ≤ r := by
      rw [pow_two]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 hr.le
    exact hr2.trans (min_le_right _ _)
  exact ⟨s,hs,hsK.trans hkM,⟨⟨L,r,d.1,hL,hr,hrSq,
    fun i hi => hsK.trans (hOld (siteAtom p ⟨i,hi⟩) (mem_oldSiteAtoms p ⟨i,hi⟩)),hSD⟩⟩⟩

noncomputable def OldTracePinGuard.map (F : CompleteValueMap B C)
    (p : PolyTrace B J) (site : J → ComplexBits B) (site' : J → ComplexBits C)
    (z : J) (m : B) (G : OldTracePinGuard p site z m)
    (hS : ∀ j ∈ p.pins,(site j).map F = site' j)
    (hZ : (site z).map F = site' z) :
    OldTracePinGuard (p.map F) site' z (F.toFun m) := by
  refine ⟨G.L,G.r,G.d,G.L_nonneg,G.r_pos,G.d_sq,?_,?_⟩
  · intro i hi
    simpa only [map_distanceLe,ComplexBits.map_checked,hS i hi] using F.monotone (G.old_norm i hi)
  · let O : ComplexBits B := ComplexBits.checked 0
    let V : ComplexBits C := ComplexBits.checked 0
    have h : F.toFun m ≤ mapCut F ((traceDenominator p).eval (traceEnv p site z O)).normSq G.d :=
      F.monotone G.denominator
    rw [ComplexBits.map_normSq,pinOnlyDenominator_map F p site site' z hS hZ O V] at h
    exact h

theorem OldTracePinGuard.denominator_target {p : PolyTrace B J} {site : J → ComplexBits B}
    {z : J} {m : B} (G : OldTracePinGuard p site z m) (target : ComplexBits B) :
    m ≤ ((traceDenominator p).eval (traceEnv p site z target)).normSq G.d := by
  rw [traceEnv_denominator_target_irrelevant p site z target (ComplexBits.checked 0)]
  exact G.denominator

theorem OldTracePinGuard.tolerance {p : PolyTrace B J} {site : J → ComplexBits B}
    {z : J} {m : B} (G : OldTracePinGuard p site z m) (ε : ℚ) (hε : 0 < ε) :
    ∃ e : ℚ,0 < e ∧ e ≤ ε ∧
      (e+e)*((p.radius : ℚ)+G.L)^(oldSiteAtoms p).length ≤ (p.budget-p.budget/2)*G.r := by
  let M : ℚ := ((p.radius : ℚ)+G.L)^(oldSiteAtoms p).length
  let H : ℚ := (p.budget-p.budget/2)*G.r
  have hM : 0 ≤ M := pow_nonneg (add_nonneg (Nat.cast_nonneg _) G.L_nonneg) _
  have hH : 0 < H := mul_pos (by linarith [p.budget_pos]) G.r_pos
  have h2 : 0 < 2*(M+1) := mul_pos (by norm_num) (by linarith)
  let e : ℚ := min ε (H/(2*(M+1)))
  have hE : 0 < e := lt_min hε (div_pos hH h2)
  have hEcap : e ≤ H/(2*(M+1)) := min_le_right _ _
  have hB : e*(2*(M+1)) ≤ H := (le_div_iff₀ h2).mp hEcap
  change ∃ e:ℚ,0<e ∧ e≤ε ∧ (e+e)*M≤H
  refine ⟨e,hE,min_le_left _ _,?_⟩
  calc
    (e+e)*M ≤ (e+e)*(M+1) := mul_le_mul_of_nonneg_left (by linarith) (add_nonneg hE.le hE.le)
    _ = e*(2*(M+1)) := by ring
    _ ≤ H := hB

end JSP000930.Negative
