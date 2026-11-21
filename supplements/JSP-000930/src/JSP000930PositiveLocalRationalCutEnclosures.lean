import JSP000930PositiveLocalFiniteCertificateCompactness

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000933.CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def RationalEncloses (β : RatPresentation → B) (q r : RatPresentation) (p : B) : Prop :=
  p ≤ β q ∧ p ≤ (β r)ᶜ

theorem enclosure_positive_width
    {β : RatPresentation → B} {m p : B} (h : ProperCutOn m β)
    (hp : p ≤ m) (hNZ : p ≠ ⊥) {q r : RatPresentation}
    (he : RationalEncloses β q r p) : q.value < r.value := by
  by_contra hn
  have hDown := h.2.2.1 r q (le_of_not_gt hn)
  have hR : p ≤ β r := (le_inf hp he.1).trans hDown
  exact hNZ (disjoint_compl_right.out _ hR he.2)

theorem exists_rational_enclosure
    {β : RatPresentation → B} {m p : B} (h : ProperCutOn m β)
    (hp : p ≤ m) (hNZ : p ≠ ⊥) :
    ∃ (q r : RatPresentation) (d : B),d ≠ ⊥ ∧ d ≤ p ∧
      RationalEncloses β q r d ∧ q.value < r.value := by
  obtain ⟨q,c,hc,hcp,hq⟩ := exists_nonzero_below_choice_r135 p hNZ β (hp.trans h.1)
  obtain ⟨r,d,hd,hdc,hr⟩ := exists_nonzero_below_choice_r135 c hc
    (fun r => (β r)ᶜ) (hcp.trans (hp.trans h.2.1))
  have he : RationalEncloses β q r d := ⟨hdc.trans hq,hr⟩
  exact ⟨q,r,d,hd,hdc.trans hcp,he,enclosure_positive_width h
    (hdc.trans (hcp.trans hp)) hd he⟩

theorem half_rational_enclosure
    {β : RatPresentation → B} {m p : B} (h : ProperCutOn m β)
    (hp : p ≤ m) (hNZ : p ≠ ⊥) {q r : RatPresentation}
    (he : RationalEncloses β q r p) :
    ∃ (a b : RatPresentation) (d : B),d ≠ ⊥ ∧ d ≤ p ∧
      RationalEncloses β a b d ∧
      b.value-a.value = (r.value-q.value)/2 := by
  obtain ⟨t,ht⟩ := ratPresentation_value_surjective ((q.value+r.value)/2)
  by_cases hd : p ⊓ β t = ⊥
  · have hN : p ≤ (β t)ᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hd.le)
    exact ⟨q,t,p,hNZ,le_rfl,⟨he.1,hN⟩,by rw [ht]; ring⟩
  · exact ⟨t,r,p ⊓ β t,hd,inf_le_left,
      ⟨inf_le_right,inf_le_left.trans he.2⟩,by rw [ht]; ring⟩

theorem shrink_rational_enclosure
    {β : RatPresentation → B} {m p : B} (h : ProperCutOn m β)
    (hp : p ≤ m) (hNZ : p ≠ ⊥) {q r : RatPresentation}
    (he : RationalEncloses β q r p) (n : ℕ) :
    ∃ (a b : RatPresentation) (d : B),d ≠ ⊥ ∧ d ≤ p ∧
      RationalEncloses β a b d ∧
      b.value-a.value = (r.value-q.value) * (1/2 : ℚ)^n := by
  induction n generalizing p q r with
  | zero => exact ⟨q,r,p,hNZ,le_rfl,he,by simp⟩
  | succ n ih =>
    obtain ⟨q',r',p',hp',hp'p,he',hW'⟩ := half_rational_enclosure h hp hNZ he
    obtain ⟨a,b,d,hd,hdp,hab,hW⟩ := ih (hp'p.trans hp) hp' he'
    refine ⟨a,b,d,hd,hdp.trans hp'p,hab,?_⟩
    rw [hW,hW',pow_succ]
    ring

theorem rational_enclosure_dense
    {β : RatPresentation → B} {m : B} (h : ProperCutOn m β)
    (ε : ℚ) (he : 0 < ε) :
    m ≤ ⨆ qr : {qr : RatPresentation × RatPresentation //
        qr.1.value < qr.2.value ∧ qr.2.value-qr.1.value < ε},
      β qr.val.1 ⊓ (β qr.val.2)ᶜ := by
  let W := ⨆ qr : {qr : RatPresentation × RatPresentation //
        qr.1.value < qr.2.value ∧ qr.2.value-qr.1.value < ε},
      β qr.val.1 ⊓ (β qr.val.2)ᶜ
  change m ≤ W
  by_contra hn
  let p := m ⊓ Wᶜ
  have hp : p ≠ ⊥ := fun e => hn
    (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr e.le))
  obtain ⟨q,r,c,hc,hcp,hqr,hwidth⟩ := exists_rational_enclosure h inf_le_left hp
  have hPos : 0 < r.value-q.value := sub_pos.mpr hwidth
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (div_pos he hPos)
    (show (1/2 : ℚ) < 1 by norm_num)
  obtain ⟨a,b,d,hd,hdc,hab,hW⟩ := shrink_rational_enclosure h
    (hcp.trans inf_le_left) hc hqr n
  have hAB : a.value < b.value := enclosure_positive_width h
    (hdc.trans (hcp.trans inf_le_left)) hd hab
  have hWidth : b.value-a.value < ε := by
    rw [hW,mul_comm]
    exact (lt_div_iff₀ hPos).mp hn
  have hdW : d ≤ W := le_iSup_of_le ⟨(a,b),hAB,hWidth⟩ (le_inf hab.1 hab.2)
  exact hd (disjoint_compl_right.out _ hdW (hdc.trans (hcp.trans inf_le_right)))

end JSP000930.Positive
