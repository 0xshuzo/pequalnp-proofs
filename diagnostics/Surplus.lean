import PEqualNP.Outside.L_meta_9752

namespace PEqualNP.Outside.L_meta_9745.Surplus
open PEqualNP.Outside.L_meta_9752.Engine

noncomputable def retained {R} (keep : Bool) (a : Wire R) : Nat :=
  if keep then cost a else 0

noncomputable def born {R} (z a b : Wire R) : Nat := by
  classical exact if Constant z ∧ ¬(Constant a ∧ Constant b) then 1 else 0

inductive Trace {R : Type} (u : Bool) (target : Wire R) :
    Nat → List (Wire R) → Nat → Prop
  | stop : Trace u target 0 [target] 0
  | perm {s ws zs e} : ws.Perm zs → Trace u target s ws e → Trace u target s zs e
  | two {s a b tail e} (d : Nat) (valid : allowed u d) (ka kb : Bool) :
      Trace u target s (comb d a b :: kept ka a (kept kb b tail)) e →
      Trace u target (s+1) (a::b::tail)
        (e+retained ka a+retained kb b+born (comb d a b) a b)

theorem measure {R u} {target : Wire R} {s ws} (h : Run u target s ws) :
    ∃ e, Trace u target s ws e := by
  induction h using Run.ind with
  | stop => exact ⟨0,Trace.stop⟩
  | perm eq _ ih =>
    obtain ⟨e,t⟩ := ih
    exact ⟨e,Trace.perm eq t⟩
  | two d hd ka kb _ ih =>
    obtain ⟨e,t⟩ := ih
    exact ⟨_,Trace.two d hd ka kb t⟩

theorem extend {R u} (roots : List (Wire R)) {p bank a b} (d) (ok : allowed u d)
    (hp : Reach u roots p bank) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
      (∀ w, Available u bank w → Available u next w) ∧
      q+cost a+cost b+born (comb d a b) a b ≤ p+1+cost (comb d a b) := by
  classical
  by_cases charged : Constant (comb d a b) ∧ ¬(Constant a ∧ Constant b)
  · refine ⟨p,bank,hp,Or.inr (Or.inl charged.1),fun _ h => h,?_⟩
    have h0 := charged.1
    by_cases da : Constant a <;> by_cases db : Constant b
    · exact (charged.2 ⟨da,db⟩).elim
    all_goals simp [born,charged,cost,da,db,h0] <;> omega
  · obtain ⟨q,bs,hq,av,inc,le⟩ := extend_comb roots d ok hp ha hb
    exact ⟨q,bs,hq,av,inc,by simpa [born,charged] using le⟩

theorem keptMass {R} (a : Wire R) (xs) (save : Bool) :
    mass (kept save a xs) = retained save a + mass xs := by
  cases save <;> simp [kept,retained,mass_cons]

theorem compress {R u} {target : Wire R} (nonconstant : ¬ Constant target) {s ws e}
    (t : Trace u target s ws e) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next target ∧ q+mass ws+e ≤ p+s := by
  classical
  induction t generalizing p bank with
  | stop => exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nonconstant]⟩
  | perm eq _ ih =>
    have sub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hq,hv,hl⟩ := ih hp sub
    exact ⟨q,W,hq,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b tail e d valid ka kb _ ih =>
    obtain ⟨r,B,hr,hz,inc,hc⟩ := extend roots d valid hp (hs a (by simp)) (hs b (by simp))
    have sub : supply u B (comb d a b :: kept ka a (kept kb b tail)) := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl|hh
      · exact hz
      · apply inc w
        apply hs
        rcases mem_kept hh with rfl|hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hq,hv,hl⟩ := ih hr sub
    rw [mass_cons,keptMass,keptMass] at hl
    refine ⟨q,W,hq,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

theorem singleSurplus {R} {target : Wire R} {roots ws s e}
    (h : Trace true target s ws e) (nc : ¬ Constant target)
    (avail : supply true roots ws) (massOne : mass ws=1) (small : s≤23)
    (price : ∀ q bs, Reach true roots q bs → Available true bs target → 21≤q) : e≤1 := by
  obtain ⟨q,B,hq,goal,pay⟩ := compress nc h roots Reach.start avail
  have high := price q B hq goal
  omega

end PEqualNP.Outside.L_meta_9745.Surplus
