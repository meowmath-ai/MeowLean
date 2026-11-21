import JSP000930AnalyticEvaluationMetric
import JSP000930AnalyticRadiusCoefficient
import JSP000930AnalyticComplexTermMask

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem complexCutOn_mono {s p : B} {z : ComplexBits B}
    (hsp : s ≤ p) (hz : z.CutOn p) : z.CutOn s :=
  ⟨properCutOn_mono hsp hz.1,properCutOn_mono hsp hz.2⟩

theorem bTruth_selectComplex_masked {n k : ℕ} (v : DVec (V B) n) (P : Fin k → STerm n)
    (R D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (z : ComplexBits B) (p : B) (hz : z.CutOn p)
    (hR : p ≤ bTruth (DVec.cons z.name v)
      (R (fun i => up (P i)) (bd_var ⟨0,Nat.succ_pos n⟩)))
    (hU : ∀ (s : B) (x : bSet B), s ≤ p →
      s ≤ bTruth (DVec.cons x v) (complex_f (bd_var ⟨0,Nat.succ_pos n⟩)) →
      s ≤ bTruth (DVec.cons x v) (R (fun i => up (P i)) (bd_var ⟨0,Nat.succ_pos n⟩)) →
      s ≤ x =ᴮ z.name) :
    p ⊓ bTruth v (selectComplex_f P R D) =
      p ⊓ bTruth (DVec.cons z.name v) (D (fun i => up (P i)) (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let U (x : bSet B) := DVec.cons x v
  let φ := R (fun i => up (P i)) T
  let ψ := D (fun i => up (P i)) T
  simp only [selectComplex_f,bTruth_sEx_r181,boolean_realize_bounded_formula_and]
  change (p ⊓ (⨆ x : bSet B,bTruth (U x) (complex_f T) ⊓
    (bTruth (U x) φ ⊓ bTruth (U x) ψ))) = p ⊓ bTruth (U z.name) ψ
  rw [inf_iSup_eq]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    let s := p ⊓ (bTruth (U x) (complex_f T) ⊓ (bTruth (U x) φ ⊓ bTruth (U x) ψ))
    have hs : s ≤ p := inf_le_left
    have he : s ≤ x =ᴮ z.name := hU s x hs (inf_le_right.trans inf_le_left)
      (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have hψ : s ≤ bTruth (U x) ψ := inf_le_right.trans (inf_le_right.trans inf_le_right)
    exact le_inf hs ((le_inf le_rfl hψ).trans
      ((bTruth_oneMask v x z.name ψ s he).le.trans inf_le_right))
  · apply le_iSup_of_le z.name
    exact le_inf inf_le_left (le_inf (inf_le_left.trans
      (forces_complexBits_name (U z.name) T z p (bTerm_current_r181 v z.name) hz))
      (le_inf (inf_le_left.trans hR) inf_le_right))

theorem bTruth_selectComplexNeg_weighted {n k : ℕ} (v : DVec (V B) n)
    (P : Fin k → STerm n) (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i : Fin k) (z : ComplexBits B) (p : B)
    (hZ : p ≤ bTerm v (P i) =ᴮ z.name) (hz : z.CutOn p) :
    p ⊓ bTruth v (selectComplex_f P (fun f r => complexNeg_f (f i) r) D) =
      p ⊓ bTruth (DVec.cons z.neg.name v) (D (fun j => up (P j)) (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  apply bTruth_selectComplex_masked v P (fun f r => complexNeg_f (f i) r) D
    z.neg p (ComplexBits.neg_cutOn hz)
  · apply forces_of_inf_eq_eqname
    exact bTruth_complexNeg_weightedMask (DVec.cons z.neg.name v) (up (P i)) T z z.neg p
      (hZ.trans_eq (congrArg (fun x => (x =ᴮ z.name))
        (bTerm_up_r181 v z.neg.name (P i))).symm)
      (le_top.trans bSet.bv_refl)
      hz (ComplexBits.neg_cutOn hz)
  · intro s x hs hX hR
    obtain ⟨a,ha,he⟩ := complexBits_of_forcedName (DVec.cons x v) T s hX
    have hxa : s ≤ x =ᴮ a.name := he
    let φ := complexNeg_f (up (P i)) T
    have hr : s ≤ bTruth (DVec.cons a.name v) φ :=
      (le_inf le_rfl hR).trans ((bTruth_oneMask v x a.name φ s hxa).le.trans inf_le_right)
    have hNeg := bTruth_complexNeg_weightedMask (DVec.cons a.name v) (up (P i)) T z a s
      ((hs.trans hZ).trans_eq (congrArg (fun x => (x =ᴮ z.name))
        (bTerm_up_r181 v a.name (P i))).symm)
      (le_top.trans bSet.bv_refl)
      (complexCutOn_mono hs hz) ha
    exact bSet.bv_trans hxa ((le_inf le_rfl hr).trans (hNeg.le.trans inf_le_right))

theorem bTruth_selectComplexAdd_weighted {n k : ℕ} (v : DVec (V B) n)
    (P : Fin k → STerm n) (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i j : Fin k) (u z : ComplexBits B) (p : B)
    (hU : bTerm v (P i) = u.name) (hZ : bTerm v (P j) = z.name)
    (hu : u.CutOn p) (hz : z.CutOn p) :
    p ⊓ bTruth v (selectComplex_f P (fun f r => complexAdd_f (f i) (f j) r) D) =
      p ⊓ bTruth (DVec.cons (u.add z).name v) (D (fun j => up (P j)) (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let w := u.add z
  apply bTruth_selectComplex_masked v P (fun f r => complexAdd_f (f i) (f j) r) D
    w p (ComplexBits.add_cutOn hu hz)
  · apply forces_of_inf_eq_eqname
    exact bTruth_complexAdd_weighted (DVec.cons w.name v) (up (P i)) (up (P j)) T u z w p
      ((bTerm_up_r181 v w.name (P i)).trans hU) ((bTerm_up_r181 v w.name (P j)).trans hZ)
      (bTerm_current_r181 v w.name) hu hz (ComplexBits.add_cutOn hu hz)
  · intro s x hs hX hR
    obtain ⟨a,ha,he⟩ := complexBits_of_forcedName (DVec.cons x v) T s hX
    have hxa : s ≤ x =ᴮ a.name := he
    let φ := complexAdd_f (up (P i)) (up (P j)) T
    have hr : s ≤ bTruth (DVec.cons a.name v) φ :=
      (le_inf le_rfl hR).trans ((bTruth_oneMask v x a.name φ s hxa).le.trans inf_le_right)
    have hAdd := bTruth_complexAdd_weighted (DVec.cons a.name v) (up (P i)) (up (P j)) T u z a s
      ((bTerm_up_r181 v a.name (P i)).trans hU) ((bTerm_up_r181 v a.name (P j)).trans hZ)
      (bTerm_current_r181 v a.name) (complexCutOn_mono hs hu) (complexCutOn_mono hs hz) ha
    exact bSet.bv_trans hxa ((le_inf le_rfl hr).trans (hAdd.le.trans inf_le_right))

theorem bTruth_selectTaylorPrefix_weighted {n k : ℕ} (v : DVec (V B) n)
    (P : Fin k → STerm n) (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → SForm d)
    (i j l : Fin k) (g : bSet B) (A : ℕ → ComplexBits B) (z : ComplexBits B) (m : ℕ) (p : B)
    (hA : bTerm v (P i) = g) (hZ : bTerm v (P j) = z.name) (hM : bTerm v (P l) = bSet.of_nat m)
    (hCut : ∀ s < m,(A s).CutOn p) (hz : z.CutOn p) (hF : p ≤ bSet.is_func g)
    (hVal : ∀ s < m,p ≤ bSet.pair (bSet.of_nat s) (A s).name ∈ᴮ g) :
    p ⊓ bTruth v (selectComplex_f P (fun f r => partialTaylorSum_f (f i) (f j) (f l) r) D) =
      p ⊓ bTruth (DVec.cons (taylorPrefixBits A z m).name v)
        (D (fun j => up (P j)) (bd_var ⟨0,Nat.succ_pos n⟩)) := by
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let w := taylorPrefixBits A z m
  apply bTruth_selectComplex_masked v P (fun f r => partialTaylorSum_f (f i) (f j) (f l) r) D
    w p (taylorPrefixBits_cutOn hz hCut m le_rfl)
  · let W := DVec.cons w.name v
    exact forces_partialTaylorSum_weighted W (up (P i)) (up (P j)) (up (P l)) T g A z m p
      ((bTerm_up_r181 v w.name (P i)).trans hA) ((bTerm_up_r181 v w.name (P j)).trans hZ)
      ((bTerm_up_r181 v w.name (P l)).trans hM) (bTerm_current_r181 v w.name) hCut hz hVal
  · intro s x hs _ h
    let W := DVec.cons x v
    have hg : bTerm W (up (P i)) = g := (bTerm_up_r181 v x (P i)).trans hA
    have eq := partialTaylorSum_unique W (up (P i)) (up (P j)) (up (P l)) T A z m s
      ((bTerm_up_r181 v x (P j)).trans hZ) ((bTerm_up_r181 v x (P l)).trans hM)
      (fun j hj => complexCutOn_mono hs (hCut j hj)) (complexCutOn_mono hs hz)
      (by rw [hg]; exact hs.trans hF) (fun j hj => by rw [hg]; exact hs.trans (hVal j hj)) h
    exact eq

end JSP000930.AnalyticSyntax
