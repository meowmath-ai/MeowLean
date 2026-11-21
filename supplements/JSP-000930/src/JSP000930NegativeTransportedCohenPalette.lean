import JSP000930ActualDenseCohenPalettes
import JSP000930AbsoluteCutArithmetic
import JSP000930NegativePinAvoidance

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.Positive.Dyadic JSP000930.Positive.Cohen JSP000930.BooleanAnalysis
open JSP000930.Positive JSP000930.Negative JSP000933.BooleanCompletion

variable {B I C : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

private theorem intervalEnclosesMap
    (F : CompleteValueMap (CohenBA B (PaletteRow I × ℕ)) C)
    (i : PaletteRow I) (A : Interval) (a b : RatPresentation) (t : C)
    (ha : a.value < A.left) (hb : A.right ≤ b.value) :
    RationalEncloses (mapCut F (intervalCutBits (B := B) i A)) a b t := by
  have h₁ : (⊤ : CohenBA B (PaletteRow I × ℕ)) ≤ intervalCutBits (B := B) i A a := by
    simpa only [wordValue_nil] using (intervalCut_below_left (B := B) i A [] a ha)
  have h₂ : (⊤ : CohenBA B (PaletteRow I × ℕ)) ≤ (intervalCutBits (B := B) i A b)ᶜ := by
    simpa only [wordValue_nil] using (intervalCut_above_right (B := B) i A [] b hb)
  exact ⟨le_top.trans (by simpa only [F.map_top,mapCut] using F.monotone h₁),
    le_top.trans (by simpa only [F.map_top,F.map_compl,mapCut] using F.monotone h₂)⟩

private theorem disjointRectanglePalette
    (l : I) (i j : ℕ) (A C D : Interval)
    (hi : rectangleSchedule i = (A,D)) (hj : rectangleSchedule j = (C,D))
    (h : A.right < C.left) :
    (⊤ : CohenBA B (PaletteRow I × ℕ)) ≤
      ((paletteBits (B := B) l i).name =ᴮ (paletteBits (B := B) l j).name)ᶜ := by
  obtain ⟨q,hq⟩ := ratPresentation_value_surjective ((A.right+C.left)/2)
  have hqA : A.right ≤ q.value := by rw [hq]; linarith
  have hqC : q.value < C.left := by rw [hq]; linarith
  let X := paletteBits (B := B) l i
  let Y := paletteBits (B := B) l j
  have hx : (⊤ : CohenBA B (PaletteRow I × ℕ)) ≤ (X.re q)ᶜ := by
    simpa only [X,paletteBits,hi,wordValue_nil] using
      (intervalCut_above_right (B := B) (l,i,false) A [] q hqA)
  have hy : (⊤ : CohenBA B (PaletteRow I × ℕ)) ≤ Y.re q := by
    simpa only [Y,paletteBits,hj,wordValue_nil] using
      (intervalCut_below_left (B := B) (l,j,false) C [] q hqC)
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff_inf_le]
  change ⊤ ⊓ (X.name =ᴮ Y.name) ≤ ⊥
  have hEq : (X.name =ᴮ Y.name) ≤ imp (Y.re q) (X.re q) := by
    rw [ComplexBits.name_eq,weightedRationalSet_eq]
    exact inf_le_left.trans (inf_le_right.trans (iInf_le _ q))
  have hx1 : ⊤ ⊓ (X.name =ᴮ Y.name) ≤ X.re q :=
    (le_inf (inf_le_right.trans hEq) (inf_le_left.trans hy)).trans Lattice.bv_imp_elim
  exact (le_inf hx1 (inf_le_left.trans hx)).trans_eq (inf_compl_self _)

theorem transported_cohen_palette_cutOn (F : CompleteValueMap (CohenBA B (PaletteRow I × ℕ)) C)
    (l : I) (n : ℕ) : ((paletteBits (B := B) l n).map F).CutOn (⊤ : C) := by
  simpa only [F.map_top] using ComplexBits.map_cutOn F (paletteBits_cutOn (B := B) l n ⊤)

theorem transported_cohen_avoiding_palette (F : CompleteValueMap (CohenBA B (PaletteRow I × ℕ)) C)
    (l : I) : AvoidingPalette (fun n => (paletteBits (B := B) l n).map F) := by
  intro x y m hx _ ε he
  by_contra h
  let A := fun n : ℕ => distanceLe x ((paletteBits (B := B) l n).map F) ε ⊓
    (((paletteBits (B := B) l n).map F).name =ᴮ y.name)ᶜ
  let s := m ⊓ (⨆ n, A n)ᶜ
  have hs : s ≠ ⊥ := fun z =>
    h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr z.le))
  obtain ⟨a,b,c,d,t,ht,hts,hab,hcd,hW₁,hW₂,heX,hiX⟩ :=
    exists_thin_complex_enclosure x s hs (cutOn_mono930 hx inf_le_left) (ε/2) (div_pos he (by norm_num))
  let R : Interval := ⟨(4*a.value+b.value)/5,(3*a.value+2*b.value)/5,by linarith⟩
  let S : Interval := ⟨(2*a.value+3*b.value)/5,(a.value+4*b.value)/5,by linarith⟩
  let T : Interval := ⟨(2*c.value+d.value)/3,(c.value+2*d.value)/3,by linarith⟩
  obtain ⟨i,hi⟩ := rectangleSchedule_surjective (R,T)
  obtain ⟨j,hj⟩ := rectangleSchedule_surjective (S,T)
  have hDist (n : ℕ) (U : Interval) (hn : rectangleSchedule n = (U,T))
      (ha : a.value < U.left) (hb : U.right ≤ b.value) :
      t ≤ distanceLe x ((paletteBits (B := B) l n).map F) ε := by
    have hT₀ : c.value < T.left := by dsimp [T]; linarith
    have hT₁ : T.right ≤ d.value := by dsimp [T]; linarith
    have hE := intervalEnclosesMap F (l,n,false) U a b t ha hb
    have hI := intervalEnclosesMap F (l,n,true) T c d t hT₀ hT₁
    refine distanceLe_of_common_box x ((paletteBits (B := B) l n).map F) t
      (cutOn_mono930 hx (hts.trans inf_le_left)) (cutOn_mono930 (transported_cohen_palette_cutOn F l n) le_top)
      a b c d heX hiX ?_ ?_ ε (by linarith)
    · simpa only [paletteBits,hn,ComplexBits.map] using hE
    · simpa only [paletteBits,hn,ComplexBits.map] using hI
  have hDi := hDist i R hi (by dsimp [R]; linarith) (by dsimp [R]; linarith)
  have hDj := hDist j S hj (by dsimp [S]; linarith) (by dsimp [S]; linarith)
  have hsep : R.right < S.left := by dsimp [R,S]; linarith
  let X := (paletteBits (B := B) l i).map F
  let Y := (paletteBits (B := B) l j).map F
  have hApart : (⊤ : C) ≤ (X.name =ᴮ Y.name)ᶜ := by
    simpa only [X,Y,F.map_top,F.map_compl,ComplexBits.map_nameEq] using
      F.monotone (disjointRectanglePalette (B := B) l i j R S T hi hj hsep)
  let u := t ⊓ ((X.name =ᴮ y.name)ᶜ)
  by_cases hu : u = ⊥
  · have hXy : t ≤ X.name =ᴮ y.name :=
      disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr hu.le)
    have hYy : t ≤ (Y.name =ᴮ y.name)ᶜ := by
      apply le_compl_iff_disjoint_right.mpr
      rw [disjoint_iff_inf_le]
      have hXY : t ⊓ (Y.name =ᴮ y.name) ≤ X.name =ᴮ Y.name :=
        bSet.bv_trans (inf_le_left.trans hXy) (inf_le_right.trans_eq bSet.bv_eq_symm)
      exact (le_inf hXY ((show t ⊓ (Y.name =ᴮ y.name) ≤ ⊤ from le_top).trans hApart)).trans_eq (inf_compl_self _)
    have hJ : t ≤ ⨆ n, A n := le_iSup_of_le j (le_inf hDj hYy)
    exact ht (disjoint_compl_right.out _ hJ (hts.trans inf_le_right))
  · have hI : u ≤ ⨆ n, A n := le_iSup_of_le i (le_inf (inf_le_left.trans hDi) inf_le_right)
    exact hu (disjoint_compl_right.out _ hI ((inf_le_left.trans hts).trans inf_le_right))

theorem avoidingPalette_dense {H : ℕ → ComplexBits C} (h : AvoidingPalette H) :
    DensePalette H := by
  intro x m hx e he
  exact (h x x m hx hx e he).trans (iSup_le fun n => inf_le_left.trans (le_iSup (fun j => distanceLe x (H j) e) n))

theorem transported_cohen_dense_palette (F : CompleteValueMap (CohenBA B (PaletteRow I × ℕ)) C)
    (l : I) : DensePalette (fun n => (paletteBits (B := B) l n).map F) :=
  avoidingPalette_dense (transported_cohen_avoiding_palette F l)

end JSP000930.Negative.Cohen
