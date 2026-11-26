import PEqualNP.Outside.L_meta_670

namespace PetersenBatchAudit
open PEqualNP.Outside.L_meta_670

def auditBatchMove (u : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => checkAt c i j op ka kb) mask xs

theorem auditBatchMove_at {u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u)
    (pass : auditBatchMove u (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · exact marked_ok _ _ _ q hq (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def auditBatchPair (u : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := auditBatchMove u b xs i j op
  f false false && f true false && f false true && f true true
def auditBatchRow (u : Bool) (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (auditBatchPair u b xs i j))
def auditBatchRows (u : Bool) (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => auditBatchRow u b xs i js && auditBatchRows u b xs js

theorem auditBatchRows_at {u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : auditBatchRows u (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [auditBatchRows,Bool.and_eq_true,auditBatchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @auditBatchMove_at u k n xs i j op
    simp only [auditBatchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode pass.1.1.1,check hi hj' hq budget arity mode pass.1.1.2⟩,
      check hi hj' hq budget arity mode pass.1.2⟩,check hi hj' hq budget arity mode pass.2⟩

def auditRunBatch (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    auditBatchRows u (makeBatch k n xs) xs (List.range n)
theorem auditRunBatch_at {u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u)
    (hn : xs[q].2.2.1.length=n)
    (pass : auditRunBatch u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := auditBatchRows_at k n xs hq hb ha hm (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

theorem packedBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : auditRunBatch g.mode k ar (contexts g k start n)=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ auditRunBatch_at hq hb ha hm hn h

def checkedBand (g : Forest) (k i n : Nat) :=
  let ar := (contextOf g k i).2.1
  if header g k i n ar then auditRunBatch g.mode k ar (contexts g k i n) else block g k i n
theorem checkedBand_ok {g k i n} (h : checkedBand g k i n = true) : block g k i n = true := by
  unfold checkedBand at h
  split at h
  next hd => exact packedBlock hd h
  next => exact h
def scanBands (g : Forest) (k : Nat) : Nat → Nat → Nat → Bool
  | 0,i,n => checkedBand g k i n
  | d+1,i,n => checkedBand g k i 32 && scanBands g k d (i+32) (n-32)
theorem scanBands_ok {g k d i n} (bound : 32*d ≤ n) (h : scanBands g k d i n=true) : block g k i n=true := by
  induction d generalizing i n with
  | zero => exact checkedBand_ok h
  | succ d ih =>
    simp only [scanBands,Bool.and_eq_true] at h
    obtain ⟨a,b⟩ := h
    have hit := @block_merge g k i 32 (n-32) (checkedBand_ok a) (ih (by omega) b)
    rwa [show 32+(n-32)=n by omega] at hit


end PetersenBatchAudit
