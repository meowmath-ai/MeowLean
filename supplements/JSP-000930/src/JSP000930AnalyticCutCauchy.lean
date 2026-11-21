import JSP000930AnalyticRoundedLimit

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def directedNear (u v : RatPresentation → B) (ε : ℚ) : B :=
  ⨅ q : RatPresentation, ⨅ r : RatPresentation, ⨅ (_ : ε ≤ r.value-q.value),
    imp (u r) (v q)

noncomputable def cutNear (u v : RatPresentation → B) (ε : ℚ) : B :=
  directedNear u v ε ⊓ directedNear v u ε

noncomputable def cutCauchyTail (u : ℕ → RatPresentation → B) (ε : ℚ) (N : ℕ) : B :=
  ⨅ i : {n : ℕ // N ≤ n}, ⨅ j : {n : ℕ // N ≤ n}, cutNear (u i.val) (u j.val) ε

noncomputable def cutConvergesTail (u : ℕ → RatPresentation → B) (v : RatPresentation → B)
    (ε : ℚ) (N : ℕ) : B :=
  ⨅ i : {n : ℕ // N ≤ n}, cutNear (u i.val) v ε

theorem directedNear_project {u v : RatPresentation → B} {ε : ℚ} {p : B}
    (hp : p ≤ directedNear u v ε) (q r : RatPresentation) (h : ε ≤ r.value-q.value) :
    p ⊓ u r ≤ v q := by
  rw [deduction]
  exact hp.trans ((iInf_le _ q).trans ((iInf_le _ r).trans (iInf_le _ h)))

theorem directedNear_intro {u v : RatPresentation → B} {ε : ℚ} {p : B}
    (hp : ∀ q r : RatPresentation, ε ≤ r.value-q.value → p ⊓ u r ≤ v q) :
    p ≤ directedNear u v ε := by
  unfold directedNear
  refine le_iInf fun q => le_iInf fun r => le_iInf fun h => ?_
  rw [← deduction]
  exact hp q r h

theorem cutCauchyTail_project {u : ℕ → RatPresentation → B} {ε : ℚ} {N i j : ℕ} {p : B}
    (hp : p ≤ cutCauchyTail u ε N) (hi : N ≤ i) (hj : N ≤ j) :
    p ≤ directedNear (u i) (u j) ε := by
  unfold cutCauchyTail at hp
  have h := hp.trans (iInf_le _ (⟨i,hi⟩ : {n : ℕ // N ≤ n}))
  exact (h.trans (iInf_le _ (⟨j,hj⟩ : {n : ℕ // N ≤ n}))).trans inf_le_left

theorem le_roundedLiminfBits_of_eventually {u : ℕ → RatPresentation → B}
    {p : B} {q r : RatPresentation} (hqr : q.value < r.value) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → p ≤ u n r) :
    p ≤ roundedLiminfBits u q := by
  unfold roundedLiminfBits
  exact (le_iInf (fun n : {n : ℕ // N ≤ n} => hN n.val n.property)).trans
    ((le_iSup (fun M : ℕ => ⨅ n : {n : ℕ // M ≤ n}, u n.val r) N).trans
      ((le_iSup (fun _ : q.value < r.value => ⨆ M : ℕ, ⨅ n : {n : ℕ // M ≤ n}, u n.val r) hqr).trans
        (le_iSup (fun t : RatPresentation => ⨆ (_ : q.value < t.value), ⨆ N : ℕ,
          ⨅ n : {n : ℕ // N ≤ n}, u n.val t) r)))

theorem cutCauchyTail_converges_roundedLiminf (u : ℕ → RatPresentation → B)
    {p : B} {ε : ℚ} (he : 0 < ε) {N : ℕ}
    (hp : p ≤ cutCauchyTail u (ε/2) N) :
    p ≤ cutConvergesTail u (roundedLiminfBits u) ε N := by
  unfold cutConvergesTail
  apply le_iInf
  intro i
  apply le_inf
  · apply directedNear_intro
    intro q r hqr
    obtain ⟨s,hs⟩ := ratPresentation_value_surjective (q.value+ε/4)
    have hqs : q.value < s.value := by rw [hs]; linarith
    have hsr : ε/2 ≤ r.value-s.value := by rw [hs]; linarith
    apply le_roundedLiminfBits_of_eventually hqs N
    intro j hj
    exact directedNear_project (cutCauchyTail_project hp i.property hj) s r hsr
  · apply directedNear_intro
    intro q r hqr
    rw [roundedLiminfBits, inf_iSup_eq]
    apply iSup_le
    intro s
    rw [inf_iSup_eq]
    apply iSup_le
    intro hrs
    rw [inf_iSup_eq]
    apply iSup_le
    intro M
    let j : {n : ℕ // M ≤ n} := ⟨max N M, le_max_right N M⟩
    have hN : N ≤ j.val := le_max_left N M
    have hqs : ε/2 ≤ s.value-q.value := by linarith
    exact (inf_le_inf_left p (iInf_le _ j)).trans
      (directedNear_project (cutCauchyTail_project hp hN i.property) q s hqs)

theorem cutCauchy_roundedLiminf_converges (u : ℕ → RatPresentation → B) (p : B)
    (hu : ∀ ε : ℚ, 0 < ε → p ≤ ⨆ N : ℕ, cutCauchyTail u ε N) :
    ∀ ε : ℚ, 0 < ε → p ≤ ⨆ N : ℕ, cutConvergesTail u (roundedLiminfBits u) ε N := by
  intro ε hε
  have hh : 0 < ε/2 := by linarith
  apply (hu (ε/2) hh).trans
  apply iSup_le
  intro N
  exact (cutCauchyTail_converges_roundedLiminf u hε le_rfl).trans (le_iSup _ N)

theorem cutCauchyTail_limit_nonempty (u : ℕ → RatPresentation → B)
    (p : B) (N : ℕ) (hp : p ≤ cutCauchyTail u 1 N)
    (hu : p ≤ ⨆ r : RatPresentation, u N r) :
    p ≤ ⨆ q : RatPresentation, roundedLiminfBits u q := by
  apply (le_inf le_rfl hu).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro r
  obtain ⟨s,hs⟩ := ratPresentation_value_surjective (r.value-1)
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (r.value-2)
  have hqs : q.value < s.value := by rw [hq,hs]; linarith
  have hsr : (1 : ℚ) ≤ r.value-s.value := by rw [hs]; linarith
  apply le_trans _ (le_iSup _ q)
  apply le_roundedLiminfBits_of_eventually hqs N
  intro j hj
  exact directedNear_project (cutCauchyTail_project hp (Nat.le_refl N) hj) s r hsr

theorem cutCauchyTail_limit_proper (u : ℕ → RatPresentation → B)
    (p : B) (N : ℕ) (hp : p ≤ cutCauchyTail u 1 N)
    (hu : p ≤ ⨆ r : RatPresentation, (u N r)ᶜ) :
    p ≤ ⨆ q : RatPresentation, (roundedLiminfBits u q)ᶜ := by
  apply (le_inf le_rfl hu).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro r
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective (r.value+1)
  apply le_trans _ (le_iSup _ q)
  apply roundedLiminfBits_proper_below u (p ⊓ (u N r)ᶜ) q N
  intro s hs j hj
  have hsr : (1 : ℚ) ≤ s.value-r.value := by rw [hq] at hs; linarith
  have hu' := directedNear_project (cutCauchyTail_project hp hj (Nat.le_refl N)) r s hsr
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff_inf_le]
  have h₁ : (p ⊓ (u N r)ᶜ) ⊓ u j s ≤ u N r :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hu'
  have h₂ : (p ⊓ (u N r)ᶜ) ⊓ u j s ≤ (u N r)ᶜ := inf_le_left.trans inf_le_right
  exact (le_inf h₁ h₂).trans (by simp)

theorem cutCauchy_limit_proper_nonempty (u : ℕ → RatPresentation → B) (p : B)
    (hc : p ≤ ⨆ N : ℕ, cutCauchyTail u 1 N)
    (hn : ∀ n : ℕ, p ≤ ⨆ r : RatPresentation, u n r)
    (hp : ∀ n : ℕ, p ≤ ⨆ r : RatPresentation, (u n r)ᶜ) :
    (p ≤ ⨆ q : RatPresentation, roundedLiminfBits u q) ∧
      (p ≤ ⨆ q : RatPresentation, (roundedLiminfBits u q)ᶜ) := by
  constructor
  · apply (le_inf le_rfl hc).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro N
    exact cutCauchyTail_limit_nonempty u _ N inf_le_right (inf_le_left.trans (hn N))
  · apply (le_inf le_rfl hc).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro N
    exact cutCauchyTail_limit_proper u _ N inf_le_right (inf_le_left.trans (hp N))

theorem convergence_directed {u : ℕ → RatPresentation → B} {p : B} {v : RatPresentation → B}
    {ε : ℚ} {N i : ℕ} (h : p ≤ cutConvergesTail u v ε N) (hi : N ≤ i) :
    (p ≤ directedNear (u i) v ε) ∧ (p ≤ directedNear v (u i) ε) := by
  unfold cutConvergesTail at h
  have hi' := h.trans (iInf_le _ (⟨i,hi⟩ : {n : ℕ // N ≤ n}))
  exact ⟨hi'.trans inf_le_left,hi'.trans inf_le_right⟩

theorem cutConverges_unique_inclusion (u : ℕ → RatPresentation → B)
    (v w : RatPresentation → B) (p : B)
    (hv : ∀ e : ℚ, 0 < e → p ≤ ⨆ N : ℕ, cutConvergesTail u v e N)
    (hw : ∀ e : ℚ, 0 < e → p ≤ ⨆ N : ℕ, cutConvergesTail u w e N)
    (hrou : ∀ q : RatPresentation, p ⊓ v q ≤
      ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), v r) :
    p ≤ weightedRationalSet v ⊆ᴮ weightedRationalSet w := by
  rw [weightedRationalSet_subset]
  apply le_iInf
  intro q
  rw [← deduction]
  apply (le_inf inf_le_left (hrou q)).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro r
  rw [inf_iSup_eq]
  apply iSup_le
  intro hqr
  let e : ℚ := (r.value-q.value)/3
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨s,hs⟩ := ratPresentation_value_surjective ((q.value+r.value)/2)
  have hsr : e ≤ r.value-s.value := by dsimp [e]; rw [hs]; linarith
  have hqs : e ≤ s.value-q.value := by dsimp [e]; rw [hs]; linarith
  have haug : p ⊓ v r ≤ (p ⊓ v r) ⊓ (⨆ N : ℕ, cutConvergesTail u v e N) :=
    le_inf le_rfl (inf_le_left.trans (hv e he))
  apply haug.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro N
  have haug' : (p ⊓ v r) ⊓ cutConvergesTail u v e N ≤
      ((p ⊓ v r) ⊓ cutConvergesTail u v e N) ⊓ (⨆ M : ℕ, cutConvergesTail u w e M) :=
    le_inf le_rfl (inf_le_left.trans (inf_le_left.trans (hw e he)))
  apply haug'.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro M
  let t : B := ((p ⊓ v r) ⊓ cutConvergesTail u v e N) ⊓ cutConvergesTail u w e M
  have htV : t ≤ cutConvergesTail u v e N := inf_le_left.trans inf_le_right
  have htW : t ≤ cutConvergesTail u w e M := inf_le_right
  have hvr : t ≤ v r := inf_le_left.trans (inf_le_left.trans inf_le_right)
  let i := max N M
  have hvu := (convergence_directed htV (i := i) (le_max_left N M)).2
  have huw := (convergence_directed htW (i := i) (le_max_right N M)).1
  have hs' : t ≤ u i s := (le_inf le_rfl hvr).trans (directedNear_project hvu s r hsr)
  exact (le_inf le_rfl hs').trans (directedNear_project huw q s hqs)

theorem cutConverges_unique_name (u : ℕ → RatPresentation → B)
    (v w : RatPresentation → B) (p : B)
    (hv : ∀ e : ℚ, 0 < e → p ≤ ⨆ N : ℕ, cutConvergesTail u v e N)
    (hw : ∀ e : ℚ, 0 < e → p ≤ ⨆ N : ℕ, cutConvergesTail u w e N)
    (hvr : ∀ q : RatPresentation, p ⊓ v q ≤
      ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), v r)
    (hwr : ∀ q : RatPresentation, p ⊓ w q ≤
      ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), w r) :
    p ≤ weightedRationalSet v =ᴮ weightedRationalSet w := by
  apply bSet.subset_ext
  · exact cutConverges_unique_inclusion u v w p hv hw hvr
  · exact cutConverges_unique_inclusion u w v p hw hv hwr

end JSP000930.BooleanAnalysis
