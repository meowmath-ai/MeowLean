import JSP000930AnalyticComplexMul

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_complexNat_weighted {n : ℕ} (v : DVec (V B) n)
    (K Z : STerm n) (z : ComplexBits B) (k : ℕ) (p : B)
    (hK : bTerm v K = bSet.of_nat k) (hZ : bTerm v Z = z.name) (hz : z.CutOn p) :
    p ⊓ bTruth v (complexNat_f K Z) =
      p ⊓ (z.name =ᴮ (ComplexBits.ofNat k).name) := by
  unfold complexNat_f
  rw [bTruth_unpackComplex_weighted v Z (fun _ : Fin 1 => K) _ z p hZ hz]
  let W := complexCoordinates v (weightedRationalSet z.re) (weightedRationalSet z.im)
  let x : STerm (n+2) := realCoordinate_f
  let y : STerm (n+2) := imagCoordinate_f
  obtain ⟨hx,hy⟩ := forces_weightedComplex_coordinates v z.re z.im
  have hK' : bTerm W (up2 K) = bSet.of_nat k := (bTerm_up2_r181 v _ _ K).trans hK
  change p ⊓ bTruth W (bd_and (realNat_f (up2 K) x) (realNat_f zero y)) = _
  have hAnd : bTruth W (bd_and (realNat_f (up2 K) x) (realNat_f zero y)) =
      bTruth W (realNat_f (up2 K) x) ⊓ bTruth W (realNat_f zero y) :=
    boolean_realize_bounded_formula_and
  rw [hAnd,bTruth_realNat_weighted W (up2 K) x k z.re hK' hx,
    bTruth_realNat_weighted W zero y 0 z.im (bTerm_zero_checked_r192 W) hy,
    ComplexBits.name_eq] <;> rfl

theorem bTruth_complexNeg_weighted {n : ℕ} (v : DVec (V B) n)
    (A Z : STerm n) (a z : ComplexBits B) (p : B)
    (hA : bTerm v A = a.name) (hZ : bTerm v Z = z.name)
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
  have hi : bTerm W (up2 Z) = z.name := by
    exact (bTerm_up2_r181 v _ _ Z).trans hZ
  have hx : bTerm V (up2 ax) = weightedRationalSet a.re := by
    exact (bTerm_up2_r181 W _ _ ax).trans hax
  have hy : bTerm V (up2 ay) = weightedRationalSet a.im := by
    exact (bTerm_up2_r181 W _ _ ay).trans hay
  unfold complexNeg_f
  rw [bTruth_unpackComplex_weighted v A (fun _ : Fin 1 => Z) _ a p hA ha]
  change p ⊓ bTruth W (unpackComplex_f (up2 Z) (fun i => ![ax,ay] i)
    (fun t r s => bd_and (realNeg_f (t 0) r) (realNeg_f (t 1) s))) = _
  rw [bTruth_unpackComplex_weighted W (up2 Z) (fun i => ![ax,ay] i) _ z p hi hz]
  change p ⊓ bTruth V (bd_and (realNeg_f (up2 ax) zx) (realNeg_f (up2 ay) zy)) = _
  have hAnd : bTruth V (bd_and (realNeg_f (up2 ax) zx) (realNeg_f (up2 ay) zy)) =
      bTruth V (realNeg_f (up2 ax) zx) ⊓ bTruth V (realNeg_f (up2 ay) zy) :=
    boolean_realize_bounded_formula_and
  rw [hAnd,bTruth_realNeg_weighted V (up2 ax) zx a.re z.re hx hzx,
    bTruth_realNeg_weighted V (up2 ay) zy a.im z.im hy hzy,ComplexBits.name_eq] <;> rfl

theorem bTruth_complexNormSq_weighted {n : ℕ} (v : DVec (V B) n)
    (Z R : STerm n) (z : ComplexBits B) (r : RatPresentation → B) (p : B)
    (hZ : bTerm v Z = z.name) (hR : bTerm v R = weightedRationalSet r)
    (hz : z.CutOn p) :
    p ⊓ bTruth v (complexNormSq_f Z R) =
      p ⊓ (weightedRationalSet r =ᴮ weightedRationalSet z.normSq) := by
  let W := complexCoordinates v (weightedRationalSet z.re) (weightedRationalSet z.im)
  let x : STerm (n+2) := realCoordinate_f
  let y : STerm (n+2) := imagCoordinate_f
  let P : Fin 3 → STerm (n+2) := ![x,y,up2 R]
  let xx := mulCutName z.re z.re
  let yy := mulCutName z.im z.im
  let W1 : DVec (V B) (n+3) := DVec.cons xx W
  let W2 : DVec (V B) (n+4) := DVec.cons yy W1
  let tx : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let ty : STerm (n+4) := bd_var ⟨0,Nat.succ_pos (n+3)⟩
  let P1 : Fin 3 → STerm (n+3) := ![up y,up (up2 R),tx]
  obtain ⟨hx,hy⟩ := forces_weightedComplex_coordinates v z.re z.im
  have hr : bTerm W (up2 R) = weightedRationalSet r := by
    exact (bTerm_up2_r181 v _ _ R).trans hR
  have hy1 : bTerm W1 (P1 0) = weightedRationalSet z.im :=
    (bTerm_up_r181 W xx y).trans hy
  unfold complexNormSq_f
  rw [bTruth_unpackComplex_weighted v Z (fun _ : Fin 1 => R) _ z p hZ hz]
  rw [bTruth_selectMul_weighted W P _ 0 0 z.re z.re p hx hx hz.1 hz.1]
  change p ⊓ bTruth W1 (selectReal_f P1 (fun w y => realMul_f (w 0) (w 0) y)
    (fun w y => realAdd_f (w 2) y (w 1))) = _
  rw [bTruth_selectMul_weighted W1 P1 _ 0 0 z.im z.im p hy1 hy1 hz.2 hz.2]
  change p ⊓ bTruth W2 (realAdd_f (up tx) ty (up (up (up2 R)))) = _
  have hxx : bTerm W2 (up tx) = xx := by
    exact (bTerm_up_r181 W1 yy tx).trans (bTerm_current_r181 W xx)
  have hyy : bTerm W2 ty = yy := bTerm_current_r181 W1 yy
  have hr' : bTerm W2 (up (up (up2 R))) = weightedRationalSet r := by
    exact (bTerm_up_r181 W1 yy (up (up2 R))).trans ((bTerm_up_r181 W xx (up2 R)).trans hr)
  rw [bTruth_realAdd_weighted W2 (up tx) ty (up (up (up2 R)))
    (mulCutBits z.re z.re) (mulCutBits z.im z.im) r hxx hyy hr'] <;> rfl

end JSP000930.AnalyticSyntax
