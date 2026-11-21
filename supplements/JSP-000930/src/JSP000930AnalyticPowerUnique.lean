import JSP000930AnalyticRecursionUnique

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_unpackComplex_le_complex {n k : ℕ} (v : DVec (V B) n)
    (Z : STerm n) (P : Fin k → STerm n)
    (F : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → SForm d) :
    bTruth v (unpackComplex_f Z P F) ≤ bTruth v (complex_f Z) := by
  rw [bTruth_complex_expand]
  simp only [unpackComplex_f,bTruth_sEx_r181,bTruth_and_eq,bTruth_equal_r181]
  apply iSup_mono
  intro x
  apply iSup_mono
  intro y
  let W := complexCoordinates v x y
  have hpair : bTerm W (pair' realCoordinate_f imagCoordinate_f) = bSet.pair x y :=
    boolean_realize_bounded_term_pair' (v := W) _ _
  have hz : bTerm W (up2 Z) = bTerm v Z := bTerm_up2_r181 v x y Z
  have he : (bTerm W (up2 Z) =ᴮ bTerm W (pair' realCoordinate_f imagCoordinate_f)) =
      (bTerm v Z =ᴮ bSet.pair x y) := by rw [hz,hpair]
  exact le_inf (le_inf (inf_le_right.trans inf_le_left)
    (inf_le_right.trans (inf_le_right.trans inf_le_left))) (inf_le_left.trans_eq he)

theorem complexNat_current_unique {n : ℕ} (v : DVec (V B) n)
    (K : STerm n) (x : bSet B) (k : ℕ) (p : B) (hK : bTerm v K = bSet.of_nat k)
    (h : p ≤ bTruth (DVec.cons x v) (complexNat_f (up K) (bd_var ⟨0,Nat.succ_pos n⟩))) :
    p ≤ x =ᴮ (ComplexBits.ofNat k).name := by
  let Z : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let v1 : DVec (V B) (n+1) := DVec.cons x v
  change p ≤ bTruth v1 (complexNat_f (up K) Z) at h
  have hComplex : p ≤ bTruth v1 (complex_f Z) := h.trans (bTruth_unpackComplex_le_complex v1 Z _ _)
  obtain ⟨a,ha,he⟩ := complexBits_of_forcedName v1 Z p hComplex
  have hx : p ≤ x =ᴮ a.name := he
  let va : DVec (V B) (n+1) := DVec.cons a.name v
  have hv : p ≤ bTruth va (complexNat_f (up K) Z) :=
    (le_inf le_rfl h).trans ((bTruth_oneMask v x a.name (complexNat_f (up K) Z) p hx).le.trans inf_le_right)
  have hh := bTruth_complexNat_weighted va (up K) Z a k p
    ((bTerm_up_r181 v a.name K).trans hK) (bTerm_current_r181 v a.name) ha
  exact bSet.bv_trans hx ((le_inf le_rfl hv).trans (hh.le.trans inf_le_right))

theorem complexPow_unique {n : ℕ} (v : DVec (V B) n)
    (Z M W : STerm n) (z : ComplexBits B) (m : ℕ) (p : B)
    (hZ : bTerm v Z = z.name) (hM : bTerm v M = bSet.of_nat m) (hz : z.CutOn p)
    (h : p ≤ bTruth v (complexPow_f Z M W)) :
    p ≤ bTerm v W =ᴮ (z.power m).name := by
  let One : bSet B := bSet.of_nat 1
  let v1 : DVec (V B) (n+1) := DVec.cons One v
  let K : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let C : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let P : Fin 1 → STerm (n+2) := fun _ => up2 Z
  let S : ∀ {d : ℕ}, (Fin 1 → STerm d) → STerm d → STerm d → STerm d → SForm d :=
    fun prm _ cur next => complexMul_f cur (prm 0) next
  let R := complexRecursion_f (up2 M) C (up2 W) P S
  let D : SForm (n+2) := bd_and (complexNat_f (up K) C) R
  have hs (i : ℕ) : bTruth (DVec.cons (bSet.of_nat i) v)
      (successor_f zero K) = crispTruth B (i=1) :=
    bTruth_successor_twoChecked_r192 _ zero K 0 i (bTerm_zero_checked_r192 _)
      (bTerm_current_r181 v (bSet.of_nat i))
  unfold complexPow_f at h
  simp only [bTruth_exOmega_r192,bTruth_and_eq] at h
  change p ≤ ⨆ i : ℕ, bTruth (DVec.cons (bSet.of_nat i) v) (successor_f zero K) ⊓
    bTruth (DVec.cons (bSet.of_nat i) v) (sEx fun _ => D) at h
  simp only [hs,iSup_crispEquality_select_r193] at h
  change p ≤ bTruth v1 (sEx fun _ => D) at h
  rw [bTruth_sEx_r181] at h
  let F (x : bSet B) : B := bTruth (DVec.cons x v1) D
  obtain ⟨base,hbase⟩ := bSet.maximum_principle F (bTruth_body_ext_r191 v1 D)
  change p ≤ ⨆ x : bSet B,F x at h
  have hb : p ≤ bTruth (DVec.cons base v1) D := h.trans hbase.le
  simp only [D,bTruth_and_eq] at hb
  have he : p ≤ base =ᴮ (ComplexBits.ofNat 1).name :=
    complexNat_current_unique v1 K base 1 p (bTerm_current_r181 v One) (hb.trans inf_le_left)
  let b0 : bSet B := (ComplexBits.ofNat (B := B) 1).name
  let v2 : DVec (V B) (n+2) := DVec.cons b0 v1
  have hr : p ≤ bTruth v2 R :=
    (le_inf le_rfl (hb.trans inf_le_right)).trans ((bTruth_oneMask v1 base b0 R p he).le.trans inf_le_right)
  have hh : p ≤ bTerm v2 (up2 W) =ᴮ (z.power m).name := by
    apply complexRecursion_unique v2 (up2 M) C (up2 W) P S m z.power p
      (fun _ => z.name) ((bTerm_up2_r181 v One b0 M).trans hM)
      (bTerm_current_r181 v1 b0) (fun j => (bTerm_up2_r181 v One b0 Z).trans hZ) _ hr
    intro d w prm I Cur Next i a hi hparams hI hCur hNext ha hs'
    have heq := bTruth_complexMul_weighted w Cur (prm 0) Next (z.power i) z a p
      hCur (hparams 0) hNext (ComplexBits.power_cutOn hz i) hz ha
    exact (le_inf le_rfl hs').trans (heq.le.trans inf_le_right)
  rw [bTerm_up2_r181 v One b0 W] at hh
  exact hh

end JSP000930.AnalyticSyntax
