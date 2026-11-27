import PEqualNP.Defs
namespace O18597
open PEqualNP.AndCount
open PEqualNP.AndCount.AndCountCircuit

abbrev V := Fin 42
abbrev Flag := V × V
def oriented (u v : V) : Prop := u.val < 21 ∧ 21 ≤ v.val ∧
  (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)
instance (u v : V) : Decidable (oriented u v) := by unfold oriented; infer_instance

def graph := SimpleGraph.fromRel oriented
def flags : Finset Flag := Finset.univ.filter (fun e : Flag => oriented e.1 e.2)

def direct (C : AndCountCircuit 42) (g : Fin C.size) (e : Flag) : Prop :=
  (e.1 ∈ C.leftVars g ∧ e.2 ∈ C.rightVars g) ∨
  (e.2 ∈ C.leftVars g ∧ e.1 ∈ C.rightVars g)

instance (C : AndCountCircuit 42) (g : Fin C.size) (e : Flag) : Decidable (direct C g e) := by
  unfold direct
  infer_instance

theorem direct_true (C : AndCountCircuit 42) (i : Fin C.size) (a b : V)
    (ha : a ∈ C.leftVars i) (hb : b ∈ C.rightVars i) : C.gateVal {a,b} i = true := by
  have fuel : ∀ d, C.gateValFuel {a,b} (d+1) i = true := by
    intro d
    simp only [gateValFuel,Bool.and_eq_true,sideTrue,decide_eq_true_eq]
    exact ⟨Or.inl ⟨a,ha,by simp⟩,Or.inl ⟨b,hb,by simp⟩⟩
  have lt := i.isLt
  have eq : C.size = C.size-1+1 := by omega
  exact (congrArg (fun d => C.gateValFuel {a,b} d i) eq).trans (fuel _)

theorem output_clean (C : AndCountCircuit 42) (computes : C.Computes graph) (i : Fin C.size)
    (hi : i ∈ C.outGates) : ∀ a ∈ C.leftVars i, ∀ b ∈ C.rightVars i, graph.Adj a b := by
  intro a ha b hb
  have on : C.eval {a,b} = true := by
    simp only [eval,decide_eq_true_eq]
    exact Or.inr ⟨i,hi,direct_true C i a b ha hb⟩
  obtain ⟨x,hx,y,hy,adj⟩ := (computes _).mp on
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact False.elim (graph.loopless.irrefl _ adj)
  · exact adj
  · exact adj.symm
  · exact False.elim (graph.loopless.irrefl _ adj)

theorem emptyNorm :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.AndCount.AndCountCircuit n),
      C.Computes G →
        C.outVars = ∅ ∧ ∀ j ∈ C.outGates, ∀ v : Fin n, C.gateVal {v} j = false := by
  classical
  intro n G C hC
  constructor
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have hEv : C.eval {v} = true := by
      simp [PEqualNP.AndCount.AndCountCircuit.eval, hv]
    rcases (hC {v}).mp hEv with ⟨a, ha, c, hc, hac⟩
    simp only [Finset.mem_singleton] at ha hc
    subst ha
    subst hc
    exact G.irrefl hac
  · intro j hj v
    have hNot : C.gateVal {v} j ≠ true := by
      intro hTrue
      have hEv : C.eval {v} = true := by
        rw [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq]
        exact Or.inr ⟨j, hj, hTrue⟩
      rcases (hC {v}).mp hEv with ⟨a, ha, c, hc, hac⟩
      simp only [Finset.mem_singleton] at ha hc
      subst ha
      subst hc
      exact G.irrefl hac
    cases h : C.gateVal {v} j with
    | false => rfl
    | true => exact (hNot h).elim
theorem fuel_witness {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true →
      ∃ k : Fin C.size, (∃ v ∈ C.leftVars k, v ∈ U) ∧ (∃ v ∈ C.rightVars k, v ∈ U) := by
  intro d
  induction d with
  | zero =>
    intro i h
    simp [AndCountCircuit.gateValFuel] at h
  | succ d ih =>
    intro i h
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true,
      AndCountCircuit.sideTrue, decide_eq_true_eq] at h
    obtain ⟨hl, hr⟩ := h
    rcases hl with hl | ⟨j, _, _, hj⟩
    · rcases hr with hr | ⟨j, _, _, hj⟩
      · exact ⟨i, hl, hr⟩
      · exact ih j hj
    · exact ih j hj


abbrev J := Fin 21
def shifts : Finset J := {0,5,7,17,20}
def P (p:J) : V := Fin.castAdd 21 p
def L (d p:J) : V := Fin.natAdd 21 (p+d)
def dyad (d p:J) : Finset V := {P p,L d p}
def cross (C:AndCountCircuit 42) (g:Fin C.size) (d p:J) := 
  (∃v∈C.leftVars g,v∈dyad d p) ∧ ∃v∈C.rightVars g,v∈dyad d p
def first (C:AndCountCircuit 42) (g:Fin C.size) (d p:J) := 
  cross C g d p ∧ ∀ j<g, ¬cross C j d p
def repeated (C:AndCountCircuit 42) (g:Fin C.size) (d:J) := 
  ∃p q:J,p≠q ∧ first C g d p ∧ first C g d q
noncomputable def colliders (C:AndCountCircuit 42) : Finset (Fin C.size) :=
  open Classical in Finset.univ.filter fun g => ∃d∈shifts, repeated C g d
instance : DecidableRel graph.Adj := by unfold graph; infer_instance
set_option maxRecDepth 10000 in
lemma flags_ok : ∀ d∈shifts,∀p:J, graph.Adj (P p) (L d p) := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma switch_bad : ∀ d∈shifts,∀p q:J,p≠q →
  (¬graph.Adj (P p) (L d q) ∨ ¬graph.Adj (P q) (L d p)) ∧ ¬graph.Adj (P p) (P q) := by
  decide +kernel
theorem raw_orient (C:AndCountCircuit 42) (dis:∀g,Disjoint (C.leftVars g) (C.rightVars g))
    (g:Fin C.size) (d p:J) (h:cross C g d p) : direct C g (P p,L d p) := by
  obtain ⟨⟨a,al,af⟩,⟨b,br,bf⟩⟩ := h
  have ab : a ≠ b := fun h => Finset.disjoint_left.mp (dis g) al (h ▸ br)
  simp only [dyad,Finset.mem_insert,Finset.mem_singleton] at af bf
  rcases af with rfl|rfl <;> rcases bf with rfl|rfl
  · exact False.elim (ab rfl)
  · exact Or.inl ⟨al,br⟩
  · exact Or.inr ⟨al,br⟩
  · exact False.elim (ab rfl)
theorem collision_hidden (C:AndCountCircuit 42) (correct:C.Computes graph)
    (dis:∀g,Disjoint (C.leftVars g) (C.rightVars g)) {g:Fin C.size}
    (hg:g∈colliders C) : g∉C.outGates := by
  rintro ho
  obtain ⟨d,hd,p,q,ne,hp,hq⟩ := (Finset.mem_filter.mp hg).2
  have ⟨crossed,across⟩ := switch_bad d hd p q ne
  have clean := output_clean C correct g ho
  rcases raw_orient C dis g d p hp.1 with ⟨ap,bp⟩|⟨bp,ap⟩ <;>
    rcases raw_orient C dis g d q hq.1 with ⟨aq,bq⟩|⟨bq,aq⟩
  · exact crossed.elim (fun h => h (clean _ ap _ bq)) (fun h => h (clean _ aq _ bp))
  · exact across (clean _ ap _ aq)
  · exact across (clean _ aq _ ap).symm
  · exact crossed.elim (fun h => h (clean _ bq _ ap).symm) (fun h => h (clean _ bp _ aq).symm)
theorem nonoutputs (C:AndCountCircuit 42) (correct:C.Computes graph)
    (dis:∀g,Disjoint (C.leftVars g) (C.rightVars g)) :
    (colliders C).card+C.outGates.card≤ C.size := by
  have hd : Disjoint (colliders C) C.outGates := Finset.disjoint_left.mpr fun i hi ho =>
    collision_hidden C correct dis hi ho
  have cap := Finset.card_le_univ (colliders C ∪ C.outGates)
  simpa only [Finset.card_union_of_disjoint hd,Fintype.card_fin] using cap

theorem existsFirst (C:AndCountCircuit 42) (correct:C.Computes graph)
    (d:J) (hd:d∈shifts) (p:J) : ∃ g, first C g d p := by
  classical
  have on := (correct (dyad d p)).mpr ⟨P p,by simp [dyad],L d p,by simp [dyad],flags_ok d hd p⟩
  simp only [eval,decide_eq_true_eq,(emptyNorm _ _ _ correct).1,Finset.notMem_empty,
    false_and,exists_false,false_or] at on
  obtain ⟨k,ok,hk⟩ := on
  obtain ⟨j,hj⟩ := fuel_witness C (dyad d p) C.size k hk
  let T := Finset.univ.filter (fun g => cross C g d p)
  have nn : T.Nonempty := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  refine ⟨T.min' nn,(Finset.mem_filter.mp (T.min'_mem nn)).2,?_⟩
  intro t lt ht
  exact (not_le_of_gt lt) (T.min'_le t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩))
theorem all_directions (C:AndCountCircuit 42) (correct:C.Computes graph)
    (small:C.size≤20) (d:J) (hd:d∈shifts) : ∃g, repeated C g d := by
  choose g h using existsFirst C correct d hd
  have lt : Fintype.card (Fin C.size)<Fintype.card J := by simp;omega
  obtain ⟨p,q,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt g lt
  exact ⟨g p,p,q,ne,h p,eq.symm ▸ h q⟩
end O18597
