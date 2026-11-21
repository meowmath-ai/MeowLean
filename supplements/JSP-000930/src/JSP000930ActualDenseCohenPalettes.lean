import JSP000930MixedRectangleDistance

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.Positive.Dyadic JSP000930.Positive.Cohen JSP000930.BooleanAnalysis
open JSP000930.Positive JSP000930.Negative

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem intervals_countable : Countable Interval := by
  apply Function.Injective.countable (f := fun s : Interval => (s.left,s.right))
  intro a b h
  cases a with
  | mk a₀ a₁ ha =>
    cases b with
    | mk b₀ b₁ hb =>
      have h₀ : a₀ = b₀ := congrArg Prod.fst h
      have h₁ : a₁ = b₁ := congrArg Prod.snd h
      subst b₀
      subst b₁
      rfl

noncomputable def rectangleSchedule (n : ℕ) : Interval × Interval := by
  letI := intervals_countable
  letI := Encodable.ofCountable (Interval × Interval)
  exact (Encodable.decode (α := Interval × Interval) n).getD (unitInterval,unitInterval)

theorem rectangleSchedule_surjective : Function.Surjective rectangleSchedule := by
  intro xy
  letI := intervals_countable
  letI := Encodable.ofCountable (Interval × Interval)
  refine ⟨Encodable.encode xy,?_⟩
  unfold rectangleSchedule
  rw [Encodable.encodek] <;> rfl

abbrev PaletteRow (I : Type) := I × ℕ × Bool

noncomputable def paletteBits (l : I) (n : ℕ) : ComplexBits (CohenBA B (PaletteRow I × ℕ)) :=
  ⟨intervalCutBits (B := B) (l,n,false) (rectangleSchedule n).1,
    intervalCutBits (B := B) (l,n,true) (rectangleSchedule n).2⟩

theorem paletteBits_cutOn (l : I) (n : ℕ) (p : CohenBA B (PaletteRow I × ℕ)) :
    (paletteBits (B := B) l n).CutOn p :=
  ⟨JSP000930.BooleanAnalysis.properCutOn_mono le_top (intervalCut_proper (l,n,false) (rectangleSchedule n).1),
    JSP000930.BooleanAnalysis.properCutOn_mono le_top (intervalCut_proper (l,n,true) (rectangleSchedule n).2)⟩

theorem dense_named_palette (l : I) (x : ComplexBits (CohenBA B (PaletteRow I × ℕ)))
    (m : CohenBA B (PaletteRow I × ℕ)) (hx : x.CutOn m) (ε : ℚ) (he : 0 < ε) :
    m ≤ ⨆ n : ℕ, distanceLe x (paletteBits (B := B) l n) ε := by
  by_contra h
  let s := m ⊓ (⨆ n : ℕ, distanceLe x (paletteBits (B := B) l n) ε)ᶜ
  have hs : s ≠ ⊥ := fun z =>
    h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr z.le))
  have hxS : x.CutOn s := ⟨JSP000930.BooleanAnalysis.properCutOn_mono inf_le_left hx.1,JSP000930.BooleanAnalysis.properCutOn_mono inf_le_left hx.2⟩
  obtain ⟨a,b,c,d,t,ht,hts,hab,hcd,hW₁,hW₂,heX,hiX⟩ :=
    exists_thin_complex_enclosure x s hs hxS (ε / 2) (div_pos he (by norm_num))
  let A : Interval := ⟨(2*a.value+b.value)/3,(a.value+2*b.value)/3,by linarith⟩
  let C : Interval := ⟨(2*c.value+d.value)/3,(c.value+2*d.value)/3,by linarith⟩
  obtain ⟨n,hn⟩ := rectangleSchedule_surjective (A,C)
  let y := paletteBits (B := B) l n
  have hY₁ : y.re = intervalCutBits (B := B) (l,n,false) A := by
    simp only [y,paletteBits,hn]
  have hY₂ : y.im = intervalCutBits (B := B) (l,n,true) C := by
    simp only [y,paletteBits,hn]
  have heY : RationalEncloses y.re a b t := by
    rw [hY₁]
    have hL : a.value < (A.follow []).left := by change a.value < (2*a.value+b.value)/3; linarith
    have hR : (A.follow []).right ≤ b.value := by change (a.value+2*b.value)/3 ≤ b.value; linarith
    refine ⟨?_,?_⟩
    · exact (show t ≤ wordValue B (l,n,false) [] by simpa only [wordValue_nil] using (le_top : t ≤ ⊤)).trans
        (intervalCut_below_left (l,n,false) A [] a hL)
    · exact (show t ≤ wordValue B (l,n,false) [] by simpa only [wordValue_nil] using (le_top : t ≤ ⊤)).trans
        (intervalCut_above_right (l,n,false) A [] b hR)
  have hiY : RationalEncloses y.im c d t := by
    rw [hY₂]
    have hL : c.value < (C.follow []).left := by change c.value < (2*c.value+d.value)/3; linarith
    have hR : (C.follow []).right ≤ d.value := by change (c.value+2*d.value)/3 ≤ d.value; linarith
    refine ⟨?_,?_⟩
    · exact (show t ≤ wordValue B (l,n,true) [] by simpa only [wordValue_nil] using (le_top : t ≤ ⊤)).trans
        (intervalCut_below_left (l,n,true) C [] c hL)
    · exact (show t ≤ wordValue B (l,n,true) [] by simpa only [wordValue_nil] using (le_top : t ≤ ⊤)).trans
        (intervalCut_above_right (l,n,true) C [] d hR)
  have hxT : x.CutOn t := ⟨JSP000930.BooleanAnalysis.properCutOn_mono hts hxS.1,JSP000930.BooleanAnalysis.properCutOn_mono hts hxS.2⟩
  have hDist : t ≤ distanceLe x y ε := distanceLe_of_common_box x y t hxT
    (paletteBits_cutOn l n t) a b c d heX hiX heY hiY ε (by linarith)
  have hD : t ≤ ⨆ n : ℕ, distanceLe x (paletteBits (B := B) l n) ε :=
    hDist.trans (le_iSup (fun k => distanceLe x (paletteBits (B := B) l k) ε) n)
  exact ht (disjoint_compl_right.out _ hD (hts.trans inf_le_right))

end JSP000930.Negative.Cohen
