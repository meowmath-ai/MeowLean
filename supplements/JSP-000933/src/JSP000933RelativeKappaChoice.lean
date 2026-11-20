import JSP000933PreparedKappaBounds

namespace JSP000933
namespace RelativeOCA

open PreparedModel

variable {B N : Type} [CompleteBooleanAlgebra B]

abbrev KappaOccurrence (N : Type) := GroundContinuumSuccIndex×N

open scoped Classical in
noncomputable def kappaRowBefore (x y : KappaOccurrence N) : B :=
  if x.1<y.1 then ⊤ else ⊥

open scoped Classical in
noncomputable def kappaRowBelowCut (x : KappaOccurrence N) (b : GroundContinuumSuccIndex) : B :=
  if x.1≤b then ⊤ else ⊥

theorem kappaRowBelowCut_mono_r474 (x : KappaOccurrence N) :
    Monotone (kappaRowBelowCut (B := B) x) := by
  classical
  intro a b hab
  by_cases h : x.1≤a
  · simp only [kappaRowBelowCut,ite_eq_left h,ite_eq_left (h.trans hab),le_rfl]
  · simp only [kappaRowBelowCut,ite_eq_right h,bot_le]

theorem kappaRowBelowCut_before_r474 (x y : KappaOccurrence N) (b : GroundContinuumSuccIndex)
    (h : b<y.1) : (kappaRowBelowCut x b : B)≤kappaRowBefore x y := by
  classical
  by_cases hx : x.1≤b
  · simp only [kappaRowBelowCut,kappaRowBefore,ite_eq_left hx,ite_eq_left (hx.trans_lt h),le_rfl]
  · simp only [kappaRowBelowCut,ite_eq_right hx,bot_le]

theorem exists_nextKappaOccurrence_r474 {I : Type} (hB : BoundsSmallKappaNames B)
    (hI : Cardinal.mk I<GroundContinuumSucc)
    (W : GroundContinuumSuccIndex→N→B) (m : B)
    (hM : m≤unboundedKappaValue (fun i => ⨆ n,W i n))
    (old : I→DiscreteChoiceOn (KappaOccurrence N) m) :
    ∃ C : DiscreteChoiceOn (KappaOccurrence N) m,
      (∀ y,C.value y≤W y.1 y.2) ∧
      ∀ i y,C.value y≤guardByChoice (old i) (fun x => kappaRowBefore x y) := by
  let T (i : I) (b : GroundContinuumSuccIndex) :=
    guardByChoice (old i) (fun x => kappaRowBelowCut x b)
  have hT (i : I) : m≤⨆ b,T i b := by
    rw [← (old i).covers]
    apply iSup_le
    intro x
    apply le_iSup_of_le x.1
    apply (le_inf le_rfl (show (old i).value x≤kappaRowBelowCut x x.1 by
      simp only [kappaRowBelowCut,ite_eq_left le_rfl,le_top])).trans
    exact guardByChoice_onCell_r445 (old i) (fun x' => kappaRowBelowCut x' x.1) x
  let All (b : GroundContinuumSuccIndex) := ⨅ i,T i b
  have hAll : m≤⨆ b,All b := uniform_smallKappa_cutoffs_r473 hB hI m T
    (fun i _ _ hab => guardByChoice_mono_r445 (old i) (fun x => kappaRowBelowCut_mono_r474 x hab))
    hT
  let U (y : KappaOccurrence N) := W y.1 y.2⊓
    ⨅ i,guardByChoice (old i) (fun x => kappaRowBefore x y)
  have hU : m≤⨆ y,U y := by
    apply (le_inf le_rfl hAll).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro b
    have hTail : m⊓All b≤aboveKappaValue (fun i => ⨆ n,W i n) b :=
      inf_le_left.trans (hM.trans (iInf_le _ b))
    apply (le_inf le_rfl hTail).trans
    rw [aboveKappaValue,inf_iSup_eq]
    apply iSup_le
    intro y
    rw [inf_iSup_eq]
    apply iSup_le
    intro n
    apply le_iSup_of_le (y.val,n)
    apply le_inf inf_le_right
    apply le_iInf
    intro i
    have hA : (m⊓All b)⊓W y.val n≤T i b :=
      inf_le_left.trans (inf_le_right.trans (iInf_le _ i))
    exact hA.trans (guardByChoice_mono_r445 (old i)
      (fun x => kappaRowBelowCut_before_r474 x (y.val,n) b y.property))
  obtain ⟨C,hC⟩ := exists_discreteChoiceOn_r445 m U hU
  exact ⟨C,fun y => (hC y).trans inf_le_left,
    fun i y => (hC y).trans (inf_le_right.trans (iInf_le _ i))⟩

end RelativeOCA
end JSP000933
