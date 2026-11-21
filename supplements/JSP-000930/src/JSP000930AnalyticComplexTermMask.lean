import JSP000930AnalyticComplexWitness

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_unpackComplex_weightedMask {n k : ℕ} (v : DVec (V B) n)
    (Z : STerm n) (P : Fin k → STerm n)
    (D : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → SForm d)
    (z : ComplexBits B) (p : B) (hZ : p ≤ bTerm v Z =ᴮ z.name) (hz : z.CutOn p) :
    p ⊓ bTruth v (unpackComplex_f Z P D) =
      p ⊓ bTruth (complexCoordinates v (weightedRationalSet z.re) (weightedRationalSet z.im))
        (D (fun i => up2 (P i)) realCoordinate_f imagCoordinate_f) := by
  let a := weightedRationalSet z.re
  let b := weightedRationalSet z.im
  let W (x y : bSet B) := complexCoordinates v x y
  let R : STerm (n+2) := realCoordinate_f
  let I : STerm (n+2) := imagCoordinate_f
  let M : SForm (n+2) := D (fun i => up2 (P i)) R I
  let φ : SForm (n+2) := bd_and (realCut_f R) (bd_and (realCut_f I) M)
  have hag (x y : bSet B) : bTruth (W x y) (bd_equal (up2 Z) (pair' R I)) =
      (bTerm v Z =ᴮ bSet.pair x y) := by
    have hpair : bTerm (W x y) (pair' R I) = bSet.pair x y :=
      boolean_realize_bounded_term_pair' (v := W x y) R I
    rw [bTruth_equal_r181,bTerm_up2_r181 v x y Z,hpair]
  simp only [unpackComplex_f,bTruth_sEx_r181]
  change (p ⊓ (⨆ x : bSet B,⨆ y : bSet B,bTruth (W x y)
    (bd_and (bd_equal (up2 Z) (pair' R I)) φ))) = p ⊓ bTruth (W a b) M
  simp only [bTruth_and_eq,hag]
  rw [inf_iSup_eq]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun y => ?_
    let e := p ⊓ ((bTerm v Z =ᴮ bSet.pair x y) ⊓ bTruth (W x y) φ)
    change e ≤ _
    have ep : e ≤ p := inf_le_left
    have hPairX : e ≤ bTerm v Z =ᴮ bSet.pair x y := inf_le_right.trans inf_le_left
    have hPairA : e ≤ bTerm v Z =ᴮ bSet.pair a b := ep.trans hZ
    have hPair : e ≤ bSet.pair x y =ᴮ bSet.pair a b :=
      bSet.bv_trans (hPairX.trans_eq bSet.bv_eq_symm) hPairA
    have hx := hPair.trans bSet.eq_of_eq_pair_left
    have hy := hPair.trans bSet.eq_of_eq_pair_right
    have hφ : e ≤ bTruth (W a b) φ := (le_inf le_rfl (inf_le_right.trans inf_le_right)).trans
      ((bTruth_twoMask v x y a b φ e hx hy).le.trans inf_le_right)
    have hM : e ≤ bTruth (W a b) M := by
      simp only [φ,bTruth_and_eq] at hφ
      exact hφ.trans (inf_le_right.trans inf_le_right)
    exact le_inf ep hM
  · refine le_iSup_of_le a ?_
    rw [inf_iSup_eq]
    refine le_iSup_of_le b ?_
    obtain ⟨hr,hi⟩ := forces_weightedComplex_coordinates v z.re z.im
    have hR := (forces_realCut_weighted_iff (W a b) R z.re hr p).2 hz.1
    have hI := (forces_realCut_weighted_iff (W a b) I z.im hi p).2 hz.2
    simp only [φ,bTruth_and_eq]
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hZ) (le_inf
      (inf_le_left.trans hR) (le_inf (inf_le_left.trans hI) inf_le_right)))

theorem bTruth_complexNeg_weightedMask {n : ℕ} (v : DVec (V B) n)
    (A Z : STerm n) (a z : ComplexBits B) (p : B)
    (hA : p ≤ bTerm v A =ᴮ a.name) (hZ : p ≤ bTerm v Z =ᴮ z.name)
    (ha : a.CutOn p) (hz : z.CutOn p) :
    p ⊓ bTruth v (complexNeg_f A Z) = p ⊓ (z.name =ᴮ a.neg.name) := by
  let W := complexCoordinates v (weightedRationalSet a.re) (weightedRationalSet a.im)
  let V := complexCoordinates W (weightedRationalSet z.re) (weightedRationalSet z.im)
  let ax : STerm (n+2) := realCoordinate_f
  let ay : STerm (n+2) := imagCoordinate_f
  let zx : STerm (n+4) := realCoordinate_f
  let zy : STerm (n+4) := imagCoordinate_f
  obtain ⟨hax,hay⟩ := forces_weightedComplex_coordinates v a.re a.im
  obtain ⟨hzx,hzy⟩ := forces_weightedComplex_coordinates W z.re z.im
  have hi : p ≤ bTerm W (up2 Z) =ᴮ z.name := by
    rw [bTerm_up2_r181 v (weightedRationalSet a.re) (weightedRationalSet a.im) Z]
    exact hZ
  have hx : bTerm V (up2 ax) = weightedRationalSet a.re := by
    exact (bTerm_up2_r181 W _ _ ax).trans hax
  have hy : bTerm V (up2 ay) = weightedRationalSet a.im := by
    exact (bTerm_up2_r181 W _ _ ay).trans hay
  unfold complexNeg_f
  rw [bTruth_unpackComplex_weightedMask v A (fun _ : Fin 1 => Z) _ a p hA ha]
  change p ⊓ bTruth W (unpackComplex_f (up2 Z) (fun i => ![ax,ay] i)
    (fun t r s => bd_and (realNeg_f (t 0) r) (realNeg_f (t 1) s))) = _
  rw [bTruth_unpackComplex_weightedMask W (up2 Z) (fun i => ![ax,ay] i) _ z p hi hz]
  change p ⊓ bTruth V (bd_and (realNeg_f (up2 ax) zx) (realNeg_f (up2 ay) zy)) = _
  rw [bTruth_and_eq,
    bTruth_realNeg_weighted V (up2 ax) zx a.re z.re hx hzx,
    bTruth_realNeg_weighted V (up2 ay) zy a.im z.im hy hzy,ComplexBits.name_eq] <;> rfl

end JSP000930.AnalyticSyntax
