import JSP000933GroundParityCuts

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def actualBand (j m : ℕ) : ℕ :=
  hybridBand (actualSampleCut j) (actualSampleCut_strict_r267 j) m

theorem actualBand_at_r268 (j k m : ℕ)
    (hm : actualSampleCut j k≤ m) (hn : m<actualSampleCut j (k+1)) : actualBand j m=k :=
  (hybridBand_eq_iff (actualSampleCut j) (actualSampleCut_strict_r267 j)
    (actualSampleCut_zero_r267 j) m k).mpr ⟨hm,hn⟩

noncomputable def actualParityCap (c : ℕ → B) (j : ℕ) (b : Bool) (m : ℕ) : B :=
  if actualBand j m%2=colorParity b then c m else ⊥

theorem actualParityCap_le_r268 (c : ℕ → B) (j : ℕ) (b : Bool) (m : ℕ) :
    actualParityCap c j b m≤c m := by
  unfold actualParityCap
  split <;> simp

theorem actualParityCap_join_r268 (c : ℕ → B) (j m : ℕ) :
    actualParityCap c j false m⊔actualParityCap c j true m=c m := by
  have h := Nat.mod_lt (actualBand j m) (show 0<2 by decide)
  by_cases h0 : actualBand j m%2=0
  · have h1 : actualBand j m%2≠1 := by omega
    simp [actualParityCap,colorParity,h0,h1]
  · have h1 : actualBand j m%2=1 := by omega
    simp [actualParityCap,colorParity,h0,h1]

theorem actualParityCap_unbounded_r268 (x : ℕ → B) (j : ℕ) (b : Bool) :
    (⊤ : B)≤actualUnboundedCap (actualParityCap (actualBranchBits x) j b) := by
  unfold actualUnboundedCap
  apply le_iInf
  intro N
  let k := 2*N+colorParity b
  have hN : N≤actualSampleCut j k :=
    (show N≤k by cases b <;> simp [k,colorParity] <;> omega).trans (self_le_actualSampleCut_r267 j k)
  have hPar : k%2=colorParity b := by cases b <;> simp [k,colorParity] <;> omega
  apply (actualSampleCut_band_nonempty_r267 x j k).trans
  apply iSup_le
  intro m
  apply le_iSup_of_le ⟨m.val,hN.trans m.property.1⟩
  have hBand := actualBand_at_r268 j k m.val m.property.1 m.property.2
  simp only [actualParityCap,hBand,ite_eq_left hPar,le_rfl]

noncomputable def afterCutDisjointValue (a b : ℕ → B) (r : ℕ) : B :=
  ⨅ m : {m : ℕ // r≤ m}, (a m.val⊓b m.val)ᶜ

theorem afterCutDisjointValue_intro_r268 {p : B} {a b : ℕ → B} {r : ℕ}
    (h : ∀ m, r≤ m → p⊓(a m⊓b m)≤⊥) : p≤afterCutDisjointValue a b r := by
  unfold afterCutDisjointValue
  exact le_iInf (fun m => le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr (h m.val m.property)))

theorem afterCutDisjointValue_apply_r268 {p : B} {a b : ℕ → B} {r : ℕ}
    (h : p≤afterCutDisjointValue a b r) (m : ℕ) (hm : r≤ m) : p⊓(a m⊓b m)≤⊥ := by
  unfold afterCutDisjointValue at h
  exact disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp
    (h.trans (iInf_le (fun j : {j : ℕ // r ≤ j} => (a j.val ⊓ b j.val)ᶜ) ⟨m,hm⟩)))

theorem ActualBranchCrossingData.paritySample_beforePrefix_r268
    {G : bSet B} {kf : ℕ → ℕ} {p q : B} (T : ActualBranchCrossingData G kf p)
    (j l k : ℕ) (b : Bool) (u : Word) (x : ℕ → B)
    (hl : l≤k) (hPar : k%2≠colorParity b) (hu : u.length=4*actualSampleCut j k)
    (hp : q≤p) (hX : q≤namedBranchCrossDomain G x)
    (hC : q≤ClosedMember (T.cover j) l x) (hU : q≤cylinderValue x u) :
    q≤afterCutDisjointValue (crossCap ((T.samples j).nameFor l u))
      (actualParityCap T.freshCap j b) (actualSampleCut j k) := by
  refine afterCutDisjointValue_intro_r268 (fun m hm => ?_)
  by_cases h : m<actualSampleCut j (k+1)
  · have hBand := actualBand_at_r268 j k m hm h
    simp only [actualParityCap,hBand,ite_eq_right hPar,inf_bot_eq,le_rfl]
  · have hCut := (actualSampleCut_lookahead_r267 j k l u hl hu).trans (Nat.le_of_not_gt h)
    exact (le_inf inf_le_left (le_inf (inf_le_right.trans inf_le_left)
      ((inf_le_right.trans inf_le_right).trans (actualParityCap_le_r268 T.freshCap j b m)))).trans
        (T.avoidance_r266 j l u x hp hX hC hU m hCut)

end SetLanguage
end JSP000933
