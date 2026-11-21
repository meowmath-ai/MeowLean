import JSP000930AnalyticPowerUnique

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_chooseThree {n : ℕ} (v : DVec (V B) n) (F : SForm (n+3)) (p : B)
    (h : p ≤ bTruth v (sEx fun _ => sEx fun _ => sEx fun _ => F)) :
    ∃ a b c : bSet B, p ≤ bTruth (DVec.cons c (DVec.cons b (DVec.cons a v))) F := by
  rw [bTruth_sEx_r181] at h
  obtain ⟨a,ha⟩ := bSet.maximum_principle
    (fun a : bSet B => bTruth (DVec.cons a v) (sEx fun _ => sEx fun _ => F))
    (bTruth_body_ext_r191 v _)
  have h1 := h.trans ha.le
  rw [bTruth_sEx_r181] at h1
  obtain ⟨b,hb⟩ := bSet.maximum_principle
    (fun b : bSet B => bTruth (DVec.cons b (DVec.cons a v)) (sEx fun _ => F))
    (bTruth_body_ext_r191 (DVec.cons a v) _)
  have h2 := h1.trans hb.le
  rw [bTruth_sEx_r181] at h2
  obtain ⟨c,hc⟩ := bSet.maximum_principle
    (fun c : bSet B => bTruth (DVec.cons c (DVec.cons b (DVec.cons a v))) F)
    (bTruth_body_ext_r191 (DVec.cons b (DVec.cons a v)) _)
  exact ⟨a,b,c,h2.trans hc.le⟩

theorem bTruth_threeMask {n : ℕ} (v : DVec (V B) n)
    (a b c a' b' c' : bSet B) (F : SForm (n+3)) (p : B)
    (ha : p ≤ a =ᴮ a') (hb : p ≤ b =ᴮ b') (hc : p ≤ c =ᴮ c') :
    p ⊓ bTruth (DVec.cons c (DVec.cons b (DVec.cons a v))) F =
      p ⊓ bTruth (DVec.cons c' (DVec.cons b' (DVec.cons a' v))) F := by
  apply bTruth_vecMask_r191
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hc
  · refine Fin.cases ?_ (fun t => ?_) j
    · exact hb
    · refine Fin.cases ?_ (fun _ => ?_) t
      · exact ha
      · exact bSet.bv_refl

private theorem force_threeMask {n : ℕ} (v : DVec (V B) n)
    (a b c x y z : bSet B) (φ : SForm (n+3)) (p : B)
    (ha : p ≤ a =ᴮ x) (hb : p ≤ b =ᴮ y) (hc : p ≤ c =ᴮ z)
    (h : p ≤ bTruth (DVec.cons c (DVec.cons b (DVec.cons a v))) φ) :
    p ≤ bTruth (DVec.cons z (DVec.cons y (DVec.cons x v))) φ :=
  (le_inf le_rfl h).trans ((bTruth_threeMask v a b c x y z φ p ha hb hc).le.trans inf_le_right)

private theorem force_stepClauses {d : ℕ} (v : DVec (V B) d) (p : B)
    (F G H I J : SForm d)
    (h : p ≤ bTruth v (bd_and F (bd_and G (bd_and H (bd_and I J))))) :
    p ≤ bTruth v F ∧ p ≤ bTruth v G ∧ p ≤ bTruth v H ∧
      p ≤ bTruth v I ∧ p ≤ bTruth v J := by
  simpa only [bTruth_and_eq,le_inf_iff] using h

private theorem chooseStepClauses {n : ℕ} (v : DVec (V B) n) (p : B)
    (F G H I J : SForm (n+3))
    (h : p ≤ bTruth v (sEx fun _ => sEx fun _ => sEx fun _ =>
      bd_and F (bd_and G (bd_and H (bd_and I J))))) :
    ∃ x y t : bSet B,
      let W : DVec (V B) (n+3) := DVec.cons t (DVec.cons y (DVec.cons x v))
      p ≤ bTruth W F ∧ p ≤ bTruth W G ∧ p ≤ bTruth W H ∧
        p ≤ bTruth W I ∧ p ≤ bTruth W J := by
  obtain ⟨x,y,t,ht⟩ := bTruth_chooseThree v (bd_and F (bd_and G (bd_and H (bd_and I J)))) p h
  exact ⟨x,y,t,force_stepClauses (DVec.cons t (DVec.cons y (DVec.cons x v))) p F G H I J ht⟩

private theorem partialTaylorStep_shape {n : ℕ}
    (P : Fin 2 → STerm n) (I C N : STerm n) :
    let A : STerm (n+3) := up2 (bd_var ⟨0,Nat.succ_pos n⟩)
    let Q : STerm (n+3) := up (bd_var ⟨0,Nat.succ_pos (n+1)⟩)
    let T : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
    partialTaylorStep_f P I C N = (sEx fun _ => sEx fun _ => sEx fun _ =>
      bd_and (value_f (up3 (P 0)) (up3 I) A)
        (bd_and (complexPow_f (up3 (P 1)) (up3 I) Q)
          (bd_and (complex_f T) (bd_and (complexMul_f A Q T)
            (complexAdd_f (up3 C) T (up3 N)))))) := by
  simp only [partialTaylorStep_f,sEx]

private theorem partialTaylorStep_components {n : ℕ} (v : DVec (V B) n)
    (P : Fin 2 → STerm n) (I C N : STerm n) (p : B)
    (h : p ≤ bTruth v (partialTaylorStep_f P I C N)) :
    let A : STerm (n+3) := up2 (bd_var ⟨0,Nat.succ_pos n⟩)
    let Q : STerm (n+3) := up (bd_var ⟨0,Nat.succ_pos (n+1)⟩)
    let T : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
    ∃ x y t : bSet B,
      let W : DVec (V B) (n+3) := DVec.cons t (DVec.cons y (DVec.cons x v))
      p ≤ bTruth W (value_f (up3 (P 0)) (up3 I) A) ∧
      p ≤ bTruth W (complexPow_f (up3 (P 1)) (up3 I) Q) ∧
      p ≤ bTruth W (complex_f T) ∧
      p ≤ bTruth W (complexMul_f A Q T) ∧
      p ≤ bTruth W (complexAdd_f (up3 C) T (up3 N)) := by
  let A : STerm (n+3) := up2 (bd_var ⟨0,Nat.succ_pos n⟩)
  let Q : STerm (n+3) := up (bd_var ⟨0,Nat.succ_pos (n+1)⟩)
  let T0 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  exact chooseStepClauses v p
    (value_f (up3 (P 0)) (up3 I) A) (complexPow_f (up3 (P 1)) (up3 I) Q)
    (complex_f T0) (complexMul_f A Q T0) (complexAdd_f (up3 C) T0 (up3 N))
    (Eq.mp (congrArg (fun f : SForm n => p ≤ bTruth v f) (partialTaylorStep_shape P I C N)) h)

set_option maxHeartbeats 600000 in
theorem partialTaylorStep_unique {n : ℕ} (v : DVec (V B) n)
    (P : Fin 2 → STerm n) (I C N : STerm n) (i : ℕ) (G : bSet B)
    (a z c d : ComplexBits B) (p : B)
    (hA : bTerm v (P 0) = G) (hZ : bTerm v (P 1) = z.name)
    (hI : bTerm v I = bSet.of_nat i) (hC : bTerm v C = c.name) (hN : bTerm v N = d.name)
    (ha : a.CutOn p) (hz : z.CutOn p) (hc : c.CutOn p) (hd : d.CutOn p)
    (hFunc : p ≤ bSet.is_func G) (hVal : p ≤ bSet.pair (bSet.of_nat i) a.name ∈ᴮ G)
    (h : p ≤ bTruth v (partialTaylorStep_f P I C N)) :
    p ≤ d.name =ᴮ (c.add (a.mul (z.power i))).name := by
  let A0 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let Q0 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let T0 : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  let A := up2 A0
  let Q := up Q0
  obtain ⟨x,y,t,hValue,hPow,hComplex,hMul₀,hAdd₀⟩ := partialTaylorStep_components v P I C N p h
  let W : DVec (V B) (n+3) := DVec.cons t (DVec.cons y (DVec.cons x v))
  have hmem : p ≤ bSet.pair (bSet.of_nat i) x ∈ᴮ G := by
    have hVal := hValue
    rw [bTruth_value,(bTerm_up3_r181 v x y t (P 0)).trans hA,
      (bTerm_up3_r181 v x y t I).trans hI,
      (bTerm_up2_r181 (DVec.cons x v) y t A0).trans (bTerm_current_r181 v x)] at hVal
    exact hVal
  have hx : p ≤ x =ᴮ a.name :=
    bSet.eq_of_is_func_of_eq hFunc (le_top.trans bSet.bv_refl) hmem hVal
  have hy : p ≤ y =ᴮ (z.power i).name := by
    have he := complexPow_unique W (up3 (P 1)) (up3 I) Q z i p
      ((bTerm_up3_r181 v x y t _).trans hZ) ((bTerm_up3_r181 v x y t I).trans hI) hz hPow
    rw [(bTerm_up_r181 (DVec.cons y (DVec.cons x v)) t Q0).trans
      (bTerm_current_r181 (DVec.cons x v) y)] at he
    exact he
  obtain ⟨u,hu,hTu⟩ := complexBits_of_forcedName W T0 p hComplex
  have hTu' : p ≤ t =ᴮ u.name := hTu
  let q := z.power i
  let W0 : DVec (V B) (n+2) := DVec.cons q.name (DVec.cons a.name v)
  let W1 : DVec (V B) (n+3) := DVec.cons u.name W0
  have hMul : p ≤ bTruth W1 (complexMul_f A Q T0) :=
    force_threeMask v x y t a.name q.name u.name (complexMul_f A Q T0) p hx hy hTu' hMul₀
  have hp : q.CutOn p := ComplexBits.power_cutOn hz i
  have hMulEq := bTruth_complexMul_weighted W1 A Q T0 a q u p
    ((bTerm_up2_r181 (DVec.cons a.name v) q.name u.name A0).trans (bTerm_current_r181 v a.name))
    ((bTerm_up_r181 W0 u.name Q0).trans (bTerm_current_r181 (DVec.cons a.name v) q.name))
    (bTerm_current_r181 W0 u.name) ha hp hu
  let prod := a.mul q
  have huEq : p ≤ u.name =ᴮ prod.name :=
    (le_inf le_rfl hMul).trans (hMulEq.le.trans inf_le_right)
  let W2 : DVec (V B) (n+3) := DVec.cons prod.name W0
  have hAdd : p ≤ bTruth W2 (complexAdd_f (up3 C) T0 (up3 N)) :=
    force_threeMask v x y t a.name q.name prod.name (complexAdd_f (up3 C) T0 (up3 N)) p
      hx hy (bSet.bv_trans hTu' huEq) hAdd₀
  have hAddEq := bTruth_complexAdd_weighted W2 (up3 C) T0 (up3 N) c prod d p
    ((bTerm_up3_r181 v a.name q.name prod.name C).trans hC)
    (bTerm_current_r181 W0 prod.name) ((bTerm_up3_r181 v a.name q.name prod.name N).trans hN)
    hc (ComplexBits.mul_cutOn ha hp) hd
  exact (le_inf le_rfl hAdd).trans (hAddEq.le.trans inf_le_right)

theorem partialTaylorSum_unique {n : ℕ} (v : DVec (V B) n) (A Z M W : STerm n)
    (a : ℕ → ComplexBits B) (z : ComplexBits B) (m : ℕ) (p : B)
    (hZ : bTerm v Z = z.name) (hM : bTerm v M = bSet.of_nat m)
    (ha : ∀ i < m,(a i).CutOn p) (hz : z.CutOn p)
    (hF : p ≤ bSet.is_func (bTerm v A))
    (hVal : ∀ i < m,p ≤ bSet.pair (bSet.of_nat i) (a i).name ∈ᴮ bTerm v A)
    (h : p ≤ bTruth v (partialTaylorSum_f A Z M W)) :
    p ≤ bTerm v W =ᴮ (taylorPrefixBits a z m).name := by
  let f := taylorPrefixBits a z
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let P : Fin 2 → STerm (n+1) := fun j => if j = 0 then up A else up Z
  let pv : Fin 2 → bSet B := fun j => if j = 0 then bTerm v A else z.name
  let R := complexRecursion_f (up M) T (up W) P (fun ps i c d => partialTaylorStep_f ps i c d)
  let Core : SForm (n+1) := bd_and (complexNat_f zero T) R
  change p ≤ bTruth v (sEx fun _ => Core) at h
  rw [bTruth_sEx_r181] at h
  let F (x : bSet B) := bTruth (DVec.cons x v) Core
  obtain ⟨x,hx⟩ := bSet.maximum_principle F (bTruth_body_ext_r191 v Core)
  change p ≤ ⨆ x : bSet B,F x at h
  have hX : p ≤ bTruth (DVec.cons x v) Core := h.trans hx.le
  simp only [Core,bTruth_and_eq] at hX
  have hzero : p ≤ bTruth (DVec.cons x v) (complexNat_f (up zero) T) := by
    change p ≤ bTruth (DVec.cons x v) (complexNat_f zero T)
    exact hX.trans inf_le_left
  have he : p ≤ x =ᴮ (f 0).name :=
    complexNat_current_unique v zero x 0 p (bTerm_zero_checked_r192 v) hzero
  let v0 : DVec (V B) (n+1) := DVec.cons (f 0).name v
  have hr : p ≤ bTruth v0 R :=
    (le_inf le_rfl (hX.trans inf_le_right)).trans
      ((bTruth_oneMask v x (f 0).name R p he).le.trans inf_le_right)
  have hP : ∀ j,bTerm v0 (P j) = pv j := by
    intro j
    by_cases hj : j = 0
    · simp only [P,pv,ite_eq_left hj]
      exact bTerm_up_r181 v (f 0).name A
    · simp only [P,pv,ite_eq_right hj]
      exact (bTerm_up_r181 v (f 0).name Z).trans hZ
  have hOut : p ≤ bTerm v0 (up W) =ᴮ (f m).name := by
    apply complexRecursion_unique v0 (up M) T (up W) P
      (fun ps i c d => partialTaylorStep_f ps i c d) m f p pv
      ((bTerm_up_r181 v (f 0).name M).trans hM) (bTerm_current_r181 v (f 0).name) hP _ hr
    intro d env ps i cur next j a0 hj hps hi hCur hNext ha0 hs
    exact partialTaylorStep_unique env ps i cur next j (bTerm v A) (a j) z (f j) a0 p
      (by simpa [pv] using hps 0) (by simpa [pv] using hps 1)
      hi hCur hNext (ha j hj) hz (taylorPrefixBits_cutOn hz ha j hj.le) ha0 hF (hVal j hj) hs
  rw [bTerm_up_r181 v (f 0).name W] at hOut
  exact hOut

end JSP000930.AnalyticSyntax
