import JSP000930AnalyticComplexBits

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_unpackComplex_weighted {n k : ℕ} (v : DVec (V B) n)
    (Z : STerm n) (ps : Fin k → STerm n)
    (body : ∀ {d : ℕ}, (Fin k → STerm d) → STerm d → STerm d → SForm d)
    (z : ComplexBits B) (p : B) (hZ : bTerm v Z = z.name) (hz : z.CutOn p) :
    p ⊓ bTruth v (unpackComplex_f Z ps body) =
      p ⊓ bTruth (complexCoordinates v (weightedRationalSet z.re) (weightedRationalSet z.im))
        (body (fun i => up2 (ps i)) realCoordinate_f imagCoordinate_f) := by
  rw [bTruth_unpackComplex_pair v Z ps body (weightedRationalSet z.re)
    (weightedRationalSet z.im) hZ]
  simp only [boolean_realize_bounded_formula_and]
  let W := complexCoordinates v (weightedRationalSet z.re) (weightedRationalSet z.im)
  obtain ⟨hr,hi⟩ := forces_weightedComplex_coordinates v z.re z.im
  have hR := (forces_realCut_weighted_iff W realCoordinate_f z.re hr p).2 hz.1
  have hI := (forces_realCut_weighted_iff W imagCoordinate_f z.im hi p).2 hz.2
  apply le_antisymm
  · exact le_inf inf_le_left (inf_le_right.trans (inf_le_right.trans inf_le_right))
  · exact le_inf inf_le_left (le_inf (inf_le_left.trans hR)
      (le_inf (inf_le_left.trans hI) inf_le_right))

def complexTripleMatrix {n : ℕ} : Fin 6 → STerm (n+6) :=
  ![up2 (up2 (realCoordinate_f (n := n))),up2 (up2 (imagCoordinate_f (n := n))),
    up2 (realCoordinate_f (n := n+2)),up2 (imagCoordinate_f (n := n+2)),
    realCoordinate_f (n := n+4),imagCoordinate_f (n := n+4)]

abbrev complexTripleEnv {n : ℕ} (v : DVec (V B) n) (a b c : ComplexBits B) :
    DVec (V B) (n+6) :=
  complexCoordinates (complexCoordinates
      (complexCoordinates v (weightedRationalSet a.re) (weightedRationalSet a.im))
      (weightedRationalSet b.re) (weightedRationalSet b.im))
    (weightedRationalSet c.re) (weightedRationalSet c.im)

def cutTripleMatrix (a b c : ComplexBits B) : Fin 6 → RatPresentation → B :=
  ![a.re,a.im,b.re,b.im,c.re,c.im]

theorem bTerm_complexTripleMatrix {n : ℕ} (v : DVec (V B) n)
    (a b c : ComplexBits B) (i : Fin 6) :
    bTerm (complexTripleEnv v a b c) (complexTripleMatrix i) =
      weightedRationalSet (cutTripleMatrix a b c i) := by
  fin_cases i <;> rfl

theorem bTruth_complexTriple_weighted {n : ℕ} (v : DVec (V B) n)
    (A C D : STerm n) (body : ∀ {d : ℕ}, (Fin 6 → STerm d) → SForm d)
    (a c d : ComplexBits B) (p : B)
    (hA : bTerm v A = a.name) (hC : bTerm v C = c.name) (hD : bTerm v D = d.name)
    (ha : a.CutOn p) (hc : c.CutOn p) (hd : d.CutOn p) :
    p ⊓ bTruth v (complexTriple_f A C D body) =
      p ⊓ bTruth (complexTripleEnv v a c d) (body complexTripleMatrix) := by
  let va := complexCoordinates v (weightedRationalSet a.re) (weightedRationalSet a.im)
  let vc := complexCoordinates va (weightedRationalSet c.re) (weightedRationalSet c.im)
  let ax : STerm (n+2) := realCoordinate_f
  let ay : STerm (n+2) := imagCoordinate_f
  let cx : STerm (n+4) := realCoordinate_f
  let cy : STerm (n+4) := imagCoordinate_f
  have hC' : bTerm va (up2 C) = c.name := by
    exact (bTerm_up2_r181 v _ _ C).trans hC
  have hD' : bTerm vc (up2 (up2 D)) = d.name := by
    exact (bTerm_up2_r181 va _ _ (up2 D)).trans ((bTerm_up2_r181 v _ _ D).trans hD)
  unfold complexTriple_f
  rw [bTruth_unpackComplex_weighted v A (fun i => ![C,D] i) _ a p hA ha]
  change p ⊓ bTruth va (unpackComplex_f (up2 C) (fun i => ![ax,ay,up2 D] i)
    (fun r bx by0 => unpackComplex_f (r 2) (fun i => ![r 0,r 1,bx,by0] i)
      (fun s dx dy => body (fun i => ![s 0,s 1,s 2,s 3,dx,dy] i)))) = _
  rw [bTruth_unpackComplex_weighted va (up2 C) (fun i => ![ax,ay,up2 D] i) _ c p hC' hc]
  change p ⊓ bTruth vc (unpackComplex_f (up2 (up2 D))
    (fun i => ![up2 ax,up2 ay,cx,cy] i)
    (fun s dx dy => body (fun i => ![s 0,s 1,s 2,s 3,dx,dy] i))) = _
  rw [bTruth_unpackComplex_weighted vc (up2 (up2 D)) (fun i => ![up2 ax,up2 ay,cx,cy] i)
    _ d p hD' hd] <;> rfl

theorem bTruth_complexAdd_weighted {n : ℕ} (v : DVec (V B) n)
    (A C D : STerm n) (a c d : ComplexBits B) (p : B)
    (hA : bTerm v A = a.name) (hC : bTerm v C = c.name) (hD : bTerm v D = d.name)
    (ha : a.CutOn p) (hc : c.CutOn p) (hd : d.CutOn p) :
    p ⊓ bTruth v (complexAdd_f A C D) = p ⊓ (d.name =ᴮ (a.add c).name) := by
  unfold complexAdd_f
  rw [bTruth_complexTriple_weighted v A C D _ a c d p hA hC hD ha hc hd]
  let w := complexTripleEnv v a c d
  let t : Fin 6 → STerm (n+6) := complexTripleMatrix
  change p ⊓ bTruth w (bd_and (realAdd_f (t 0) (t 2) (t 4))
    (realAdd_f (t 1) (t 3) (t 5))) = _
  have hM (i : Fin 6) : bTerm w (t i) = weightedRationalSet (cutTripleMatrix a c d i) :=
    bTerm_complexTripleMatrix v a c d i
  have hAnd : bTruth w (bd_and (realAdd_f (t 0) (t 2) (t 4))
      (realAdd_f (t 1) (t 3) (t 5))) =
      bTruth w (realAdd_f (t 0) (t 2) (t 4)) ⊓ bTruth w (realAdd_f (t 1) (t 3) (t 5)) :=
    boolean_realize_bounded_formula_and
  rw [hAnd,bTruth_realAdd_weighted w (t 0) (t 2) (t 4) a.re c.re d.re (hM 0) (hM 2) (hM 4),
    bTruth_realAdd_weighted w (t 1) (t 3) (t 5) a.im c.im d.im (hM 1) (hM 3) (hM 5),
    ComplexBits.name_eq] <;> rfl

end JSP000930.AnalyticSyntax
