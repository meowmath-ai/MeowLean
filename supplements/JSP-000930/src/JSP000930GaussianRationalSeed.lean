import JSP000930SymbolicPinLogSelection
import Mathlib.Data.List.Forall2
import JSP000930MixedRectangleDistance

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000933.BooleanNames

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def gaussianRat (s : ℚ × ℚ) : ℂ := ⟨(s.1 : ℝ),(s.2 : ℝ)⟩

theorem exists_gaussianRat_approx (w : ComplexBits B) (m : B) (hm : m ≠ ⊥)
    (hw : w.CutOn m) (e : ℚ) (he : 0 < e) :
    ∃ (s : B) (r : ℚ × ℚ), s ≠ ⊥ ∧ s ≤ m ∧
      s ≤ distanceLe w (ComplexBits.checked (gaussianRat r)) e := by
  obtain ⟨a,b,c,d,s,hs,hsM,hab,hcd,h₁,h₂,hRe,hIm⟩ :=
    exists_thin_complex_enclosure w m hm hw (e/2) (half_pos he)
  let r : ℚ × ℚ := ((a.value + b.value)/2,(c.value + d.value)/2)
  let z := ComplexBits.checked (B := B) (gaussianRat r)
  have hAL : (a.value : ℝ) < (r.1 : ℝ) := by
    exact_mod_cast (show a.value < r.1 by dsimp [r]; linarith)
  have hBR : (r.1 : ℝ) ≤ (b.value : ℝ) := by
    exact_mod_cast (show r.1 ≤ b.value by dsimp [r]; linarith)
  have hCL : (c.value : ℝ) < (r.2 : ℝ) := by
    exact_mod_cast (show c.value < r.2 by dsimp [r]; linarith)
  have hDR : (r.2 : ℝ) ≤ (d.value : ℝ) := by
    exact_mod_cast (show r.2 ≤ d.value by dsimp [r]; linarith)
  have hrRe : RationalEncloses z.re a b s := by
    constructor
    · simpa only [z,gaussianRat,ComplexBits.checked,checkedRealBits,JSP000933.PositiveForcing.crispTruth,ite_eq_left hAL] using
        (le_top : s ≤ ⊤)
    · simpa only [z,gaussianRat,ComplexBits.checked,checkedRealBits,JSP000933.PositiveForcing.crispTruth,
        ite_eq_right (not_lt_of_ge hBR),compl_bot] using (le_top : s ≤ ⊤)
  have hrIm : RationalEncloses z.im c d s := by
    constructor
    · simpa only [z,gaussianRat,ComplexBits.checked,checkedRealBits,JSP000933.PositiveForcing.crispTruth,ite_eq_left hCL] using
        (le_top : s ≤ ⊤)
    · simpa only [z,gaussianRat,ComplexBits.checked,checkedRealBits,JSP000933.PositiveForcing.crispTruth,
        ite_eq_right (not_lt_of_ge hDR),compl_bot] using (le_top : s ≤ ⊤)
  exact ⟨s,r,hs,hsM,distanceLe_of_common_box w z s (cutOn_mono930 hw hsM)
    (ComplexBits.checked_cutOn _ _) a b c d hRe hIm hrRe hrIm e (by linarith)⟩

def SeedClose (m : B) (a : List (ComplexBits B)) (seed : List (ℚ × ℚ)) (e : ℚ) : Prop :=
  List.Forall₂ (fun w r => m ≤ distanceLe w (ComplexBits.checked (gaussianRat r)) e) a seed

theorem SeedClose.mono {m s : B} {a : List (ComplexBits B)} {r : List (ℚ × ℚ)} {e : ℚ}
    (h : SeedClose m a r e) (hs : s ≤ m) : SeedClose s a r e := by
  unfold SeedClose at h ⊢
  induction h with
  | nil => exact .nil
  | cons h hRest ih => exact .cons (hs.trans h) ih

theorem exists_gaussian_seed (a : List (ComplexBits B)) (m : B) (hm : m ≠ ⊥)
    (ha : ∀ w ∈ a,w.CutOn m) (e : ℚ) (he : 0 < e) :
    ∃ (s : B) (seed : List (ℚ × ℚ)), s ≠ ⊥ ∧ s ≤ m ∧ SeedClose s a seed e := by
  induction a generalizing m with
  | nil => exact ⟨m,[],hm,le_rfl,List.Forall₂.nil⟩
  | cons w a ih =>
    obtain ⟨s,r,hs,hsM,hr⟩ := exists_gaussianRat_approx w m hm
      (ha w List.mem_cons_self) e he
    have haS : ∀ v ∈ a, v.CutOn s := fun v hv =>
      cutOn_mono930 (ha v (List.mem_cons_of_mem _ hv)) hsM
    obtain ⟨t,seed,ht,htS,hRest⟩ := ih s hs haS
    exact ⟨t,r::seed,ht,htS.trans hsM,List.Forall₂.cons (htS.trans hr) hRest⟩

end JSP000930.Negative
