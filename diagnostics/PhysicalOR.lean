import PEqualNP.Defs

namespace Plane17872Trace

abbrev V := Fin 24
abbrev G := Fin 26
abbrev Wires := ℕ → Finset V
abbrev Homes := G → Finset V
abbrev Dem := Finset (G × ℕ)
abbrev Obligations := Finset (G × V)

def Covers (W : Wires) (D : Dem) (Z : Obligations) :=
  ∀ z ∈ Z, ∃ d ∈ D, d.1 = z.1 ∧ z.2 ∈ W d.2

def Fits (W : Wires) (H : Homes) (D : Dem) (bound : ℕ) :=
  ∀ d ∈ D, d.2 < bound ∧ W d.2 ⊆ H d.1

def Linear (H : Homes) := ∀ (g h : G), g ≠ h →
  ∀ u ∈ H g, u ∈ H h → ∀ v ∈ H g, v ∈ H h → u=v

def Legal (W : Wires) (s : ℕ) := ∀ j<s,
  W (24+j)=∅ ∨ (∃ v, W (24+j)={v}) ∨
  ∃ a<24+j, ∃ b<24+j, W (24+j) = W a ∪ W b

end Plane17872Trace

namespace Plane17872Trace

def graph (a b : Fin 12) : Prop :=
  (9 : Fin 13).succAbove a + (0 : Fin 13).succAbove b ∈ ({0,1,3,9} : Finset (Fin 13))
instance (a b : Fin 12) : Decidable (graph a b) := by unfold graph; infer_instance

abbrev F := {e : Fin 12 × Fin 12 // graph e.1 e.2}
abbrev pt (i : Fin 12) := i.castAdd 12
abbrev ln (i : Fin 12) := i.natAdd 12
def name (i : V) : G := ⟨i.val,by omega⟩
def table : List (Finset V) := [
  {12,14,20},
  {13,19,23},
  {12,18,22,23},
  {17,21,22},
  {16,20,21,23},
  {15,19,20,22},
  {14,18,19,21},
  {13,17,18,20},
  {12,16,17,19},
  {14,15,17,23},
  {13,14,16,22},
  {12,13,15,21},
  {0,2,8,11},
  {1,7,10,11},
  {0,6,9,10},
  {5,9,11},
  {4,8,10},
  {3,7,8,9},
  {2,6,7},
  {1,5,6,8},
  {0,4,5,7},
  {3,4,6,11},
  {2,3,5,10},
  {1,2,4,9},
  {0,1,3},
  {15,16,18}]

def home (g : G) : Finset V := table.getD g.val ∅
def star (i : V) : Finset V := home (name i)

def extra (i : Fin 6) : G × V :=
  ((if i.val<3 then 24 else 25), ([0,1,3,15,16,18] : List V).getD i.val 0)

def flag (b : Bool) (e : F) : G × V :=
  if b then (name (pt e.val.1),ln e.val.2) else (name (ln e.val.2),pt e.val.1)

set_option maxHeartbeats 10000000 in
theorem finite_geometry :
    Fintype.card F=45 ∧
    (∀ (a b : Bool) (e f : F), flag a e=flag b f → e=f) ∧
    (∀ (a : Bool) (e : F) (i : Fin 6), flag a e ≠ extra i) ∧
    (∀ i j : Fin 6, extra i=extra j → i=j) ∧
    (∀ i : Fin 6, (extra i).2 ∈ home (extra i).1) := by decide +kernel

def color (v : V) : Fin 12 := ⟨([0,1,2,3,4,5,6,7,8,9,10,11,8,7,6,5,4,3,2,1,0,11,10,9] : List Nat).getD v.val 0 % 12, Nat.mod_lt _ (by decide)⟩
def diagonal (i : Fin 12) : Fin 12 := ⟨([8,7,6,5,4,3,2,1,0,11,10,9] : List Nat).getD i.val 0 % 12,Nat.mod_lt _ (by decide)⟩

theorem match_geom : ∀ i : Fin 12, graph i (diagonal i) ∧ color (pt i)=i ∧ color (ln (diagonal i))=i := by decide +kernel

def Oriented (W : Wires) {t : Nat} (cen : Fin t → V) (arm : Fin t → Nat) :=
  ∀ e : F, ∃ i : Fin t, ∃ b : Bool, (flag b e).1=name (cen i) ∧ (flag b e).2∈W (arm i)

end Plane17872Trace

namespace Plane17872Trace
open PEqualNP.CircuitLowerBounds

def probe (a b : V) : V → Bool := fun i => decide (i=a ∨ i=b)
def fires (x : V → Bool) := ∃ a b : Fin 12, graph a b ∧ x (pt a)=true ∧ x (ln b)=true
instance (x : V→Bool) : Decidable (fires x) := by unfold fires; infer_instance
def upperP (x : V → Bool) := x 0 || x 1 || x 3
def upperL (x : V → Bool) := x 15 || x 16 || x 18
abbrev read (C : Circuit) (x : V→Bool) (i : Nat) := PEqualNP.BlindGate.wireValue C 24 x i
def Spec (C : Circuit) (q : List (Nat×Nat)) (ma mb : Nat) :=
  ∀ x : V→Bool, ((q.any fun p => read C x p.1 && read C x p.2)=true ↔ fires x) ∧
    (¬fires x → read C x ma = upperP x ∧ read C x mb=upperL x)

def Agrees (C : Circuit) (W : Wires) := ∀ k<24+C.size, ∀ u v : V,
  read C (probe u v) k=true ↔ u∈W k ∨ v∈W k

end Plane17872Trace

namespace Plane17872Trace
open PEqualNP.CircuitLowerBounds

def xraw : List (Finset V) := (List.finRange 24).map fun i=>{i}
def unite (xs : List (Finset V)) := xs.foldr (·∪·) ∅
def press (w : List (Finset V)) (g : Gate) :=
  w ++ [unite (g.inputs.map fun i=>w.getD i ∅)]
def steps (gs : List Gate) := gs.foldl press xraw
def words (gs : List Gate) (i : Nat) := (steps gs).getD i ∅

theorem slen (gs : List Gate) (w : List (Finset V)) :
    (gs.foldl press w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,press]; omega

theorem glen (gs : List Gate) : (steps gs).length=24+gs.length := by simp [steps,slen,xraw]

theorem wkeep (gs : List Gate) (g : Gate) (i : Nat) (h : i<24+gs.length) :
    words (gs++[g]) i=words gs i := by
  simp only [words,steps,List.foldl_append,List.foldl_cons,List.foldl_nil,press]
  apply List.getD_append
  simpa only [←glen] using h

theorem wlast (gs : List Gate) (g : Gate) :
   words (gs++[g]) (24+gs.length) = unite (g.inputs.map fun i=>words gs i) := by
  rw [←glen]
  change ((steps gs)++[_]).getD (steps gs).length ∅ = _
  simp

theorem wout (gs : List Gate) (i : Nat) (hi : 24+gs.length≤i) : words gs i=∅ := by
  apply List.getD_eq_default
  simpa [glen] using hi

theorem raw_words (gs : List Gate) : ∀ i : V, words gs i.val={i} := by
  induction gs using List.reverseRecOn with
  | nil => intro i; simp [words,steps,xraw,List.getD_eq_getElem?_getD,List.finRange,i.isLt]
  | append_singleton gs g ih => intro i; rw [wkeep gs g i.val (by omega),ih]

theorem easyLegal (gs : List Gate) (hf : ∀ g∈gs,g.inputs.length≤2) : Legal (words gs) gs.length := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    have prev := ih (fun t h => hf t (List.mem_append_left _ h))
    let k := 24+gs.length
    let U := words gs
    let W := words (gs++[g])
    have keep (i : Nat) (h : i<k) : W i=U i := wkeep gs g i h
    intro j hj
    have hj' : j<gs.length+1 := by simpa using hj
    by_cases e : j=gs.length
    · subst j
      have sz := hf g (by simp)
      let a := g.inputs.getD 0 k
      let b := g.inputs.getD 1 k
      have eq : W k = U a ∪ U b := by
        rw [show W k=unite (g.inputs.map U) from wlast gs g]
        have emp : U k=∅ := wout _ _ (by rfl)
        dsimp only [a,b]
        cases iz : g.inputs with
        | nil => simp [unite,emp]
        | cons v l =>
          cases l with
          | nil => simp [unite,emp]
          | cons u l =>
            cases l with
            | nil => simp [unite]
            | cons v' l => simp [iz] at sz
      change W k=∅ ∨ _ ∨ ∃ a<k,∃ b<k,W k=W a∪W b
      by_cases aa : a<k
      · by_cases bb : b<k
        · exact Or.inr (Or.inr ⟨a,aa,b,bb,by simpa [keep a aa,keep b bb] using eq⟩)
        · have ze : U b=∅ := wout _ _ (by dsimp [k] at bb; omega)
          exact Or.inr (Or.inr ⟨a,aa,a,aa,by simpa [keep a aa,ze] using eq⟩)
      · have ze : U a=∅ := wout _ _ (by dsimp [k] at aa; omega)
        by_cases bb : b<k
        · exact Or.inr (Or.inr ⟨b,bb,b,bb,by simpa [keep b bb,ze] using eq⟩)
        · have ze' : U b=∅ := wout _ _ (by dsimp [k] at bb; omega)
          exact Or.inl (by simpa [ze,ze'] using eq)
    · have h : j<gs.length := by omega
      have old : W (24+j)=U (24+j) := keep _ (by dsimp [k]; omega)
      rcases prev j h with he|⟨v,hv⟩|⟨a,ha,b,hb,hq⟩
      · exact Or.inl (old.trans he)
      · exact Or.inr (Or.inl ⟨v,old.trans hv⟩)
      · exact Or.inr (Or.inr ⟨a,ha,b,hb,by rw [show words (gs++[g]) (24+j)=U (24+j) from old,
          show words (gs++[g]) a=U a from keep a (by dsimp [k];omega),
          show words (gs++[g]) b=U b from keep b (by dsimp [k];omega)];exact hq⟩)

def hit (u v : V) (S : Finset V) := decide (u∈S ∨ v∈S)
def vals (u v : V) (w : List (Finset V)) := w.map (hit u v)

theorem hitunion (u v : V) (l : List (Finset V)) :
    hit u v (unite l) = (l.map (hit u v)).any id := by
  induction l with
  | nil => simp [hit,unite]
  | cons h t ih =>
    change hit u v (h ∪ unite t) = (hit u v h || _)
    rw [←ih]
    simp [hit,or_assoc,or_left_comm,or_comm]

theorem readvals (u v : V) (w : List (Finset V)) (k : Nat) :
    (vals u v w).getD k false=hit u v (w.getD k ∅) := by
  simp only [vals,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[k]? <;> simp [hit]

theorem fullvals (gs : List Gate) (w : List (Finset V)) (u v : V) (hs : ∀ g∈gs,g.op=.or) :
  gs.foldl (fun (z:List Bool) g=>z++[g.op.eval (g.inputs.map fun i=>z.getD i false)]) (vals u v w)
    = vals u v (gs.foldl press w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [← ih _ (fun g hg=>hs g (by simp [hg]))]
    congr 1
    have hop := hs h (by simp)
    simp [press,vals,List.map_append,hop,GateOp.eval,hitunion,List.map_map,Function.comp,←readvals]

theorem agrees_or (C : Circuit) (h : ∀ g∈C.gates,g.op=.or) : Agrees C (words C.gates) := by
  intro k _ u v
  have iv : vals u v xraw = List.ofFn (probe u v) := by
    simp [vals,xraw,List.finRange,hit,probe,List.map_ofFn,eq_comm]
  unfold read PEqualNP.BlindGate.wireValue Circuit.wires
  rw [←iv,fullvals _ _ _ _ h,readvals]
  simp [hit,words,steps]

theorem OR_only_price (sparse_price : ∀ (C : Circuit) (q : List (Nat×Nat)) (ma mb : Nat) (W : Wires),
    (∀ i : V,W i.val={i}) → Legal W C.size → Agrees C W →
    Spec C q ma mb → ma<24+C.size → mb<24+C.size →
    (∀ z∈q,z.1 < 24+C.size ∧ z.2 < 24+C.size) → 61≤C.size+2*q.length) (C : Circuit) (q : List (Nat×Nat)) (ma mb : Nat)
    (pure : ∀ g∈C.gates,g.op=.or) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (sp : Spec C q ma mb) (ha : ma<24+C.size) (hb : mb<24+C.size)
    (bounds : ∀ z∈q,z.1 < 24+C.size ∧ z.2 < 24+C.size) : 61≤C.size+2*q.length :=
  sparse_price C q ma mb (words C.gates) (raw_words _) (easyLegal _ (fun g hg=>(hm g hg).2))
    (agrees_or C pure) sp ha hb bounds

end Plane17872Trace
