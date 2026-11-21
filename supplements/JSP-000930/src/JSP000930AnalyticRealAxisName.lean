import JSP000930AnalyticComplexPair
import JSP000930AnalyticCutCauchyMetric

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.BooleanNames JSP000933.PositiveForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def ProperCutOn (p : B) (β : RatPresentation → B) : Prop :=
  (p ≤ ⨆ q : RatPresentation, β q) ∧
  (p ≤ ⨆ q : RatPresentation, (β q)ᶜ) ∧
  (∀ q r : RatPresentation, q.value ≤ r.value → p ⊓ β r ≤ β q) ∧
  (∀ q : RatPresentation, p ⊓ β q ≤ ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), β r)

theorem checkedRealBits_properCut (x : ℝ) : ProperCutOn (⊤ : B) (checkedRealBits x) := by
  constructor
  · obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn (show x-1 < x by linarith)
    obtain ⟨r,hr⟩ := ratPresentation_value_surjective q
    have h : (r.value : ℝ) < x := by simpa only [hr] using hq₂
    have he : checkedRealBits (B := B) x r = ⊤ := by simp [checkedRealBits,crispTruth,h]
    exact (le_of_eq he.symm).trans (le_iSup (checkedRealBits (B := B) x) r)
  · constructor
    · obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn (show x < x+1 by linarith)
      obtain ⟨r,hr⟩ := ratPresentation_value_surjective q
      have h : ¬ (r.value : ℝ) < x := by rw [hr]; exact not_lt_of_gt hq₁
      have he : (checkedRealBits (B := B) x r)ᶜ = ⊤ := by simp [checkedRealBits,crispTruth,h]
      exact (le_of_eq he.symm).trans (le_iSup (fun s : RatPresentation => (checkedRealBits (B := B) x s)ᶜ) r)
    · constructor
      · intro q r hqr
        by_cases hr : (r.value : ℝ) < x
        · have hs : (q.value : ℝ) ≤ (r.value : ℝ) := by exact_mod_cast hqr
          simp [checkedRealBits,crispTruth,hr,hs.trans_lt hr]
        · simp [checkedRealBits,crispTruth,hr]
      · intro q
        by_cases hq : (q.value : ℝ) < x
        · obtain ⟨r,hr₁,hr₂⟩ := exists_rat_btwn hq
          obtain ⟨s,hs⟩ := ratPresentation_value_surjective r
          have hs₁ : q.value < s.value := by
            exact_mod_cast (show (q.value : ℝ) < (s.value : ℝ) by rwa [hs])
          have hs₂ : (s.value : ℝ) < x := by rwa [hs]
          have htop : checkedRealBits (B := B) x s = ⊤ := by simp [checkedRealBits,crispTruth,hs₂]
          exact inf_le_left.trans ((le_of_eq htop.symm).trans (le_iSup_of_le s (le_iSup (fun _ : q.value < s.value => checkedRealBits (B := B) x s) hs₁)))
        · simp [checkedRealBits,crispTruth,hq]

end JSP000930.BooleanAnalysis

namespace JSP000930.AnalyticSyntax

open JSP000930.BooleanAnalysis JSP000933.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem forces_complex_pair_of_cutData {n : ℕ} (v : DVec (V B) n) (Z : STerm n)
    (re im : RatPresentation → B) (p : B)
    (hZ : p ≤ bTerm v Z =ᴮ bSet.pair (weightedRationalSet re) (weightedRationalSet im))
    (hre : ProperCutOn p re) (him : ProperCutOn p im) :
    p ≤ bTruth v (complex_f Z) := by
  let w := complexCoordinates v (weightedRationalSet re) (weightedRationalSet im)
  obtain ⟨hx,hy⟩ := forces_weightedComplex_coordinates v re im
  exact forces_complex_pair_of_weightedCuts v Z re im p hZ
    ((forces_realCut_weighted_iff w realCoordinate_f re hx p).2 hre)
    ((forces_realCut_weighted_iff w imagCoordinate_f im hy p).2 him)

theorem forces_complex_realAxis {n : ℕ} (v : DVec (V B) n) (Z : STerm n)
    (re : RatPresentation → B) (h : ProperCutOn ⊤ re)
    (hZ : bTerm v Z = bSet.pair (weightedRationalSet re)
      (weightedRationalSet (checkedRealBits (B := B) 0))) :
    (⊤ : B) ≤ bTruth v (complex_f Z) := by
  refine forces_complex_pair_of_cutData v Z re (checkedRealBits 0) ⊤ ?_ h
    (checkedRealBits_properCut 0)
  rw [hZ]
  exact bSet.bv_refl

end JSP000930.AnalyticSyntax
