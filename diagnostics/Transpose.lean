import PEqualNP.Defs

namespace Linear9798
set_option maxHeartbeats 0
inductive Port
  | bit
  | pair (a b : Port)
def Port.Val : Port → Type
  | .bit => Bool
  | .pair a b => a.Val × b.Val
def Port.dim : Port → Nat
  | .bit => 1
  | .pair a b => a.dim+b.dim
def Port.dot : (a : Port) → a.Val → a.Val → Bool
  | .bit,u,v => u && v
  | .pair a b,u,v => a.dot u.1 v.1 || b.dot u.2 v.2
inductive Net (X : Type) : Port → Port → Type
  | identity (a) : Net X a a
  | copy : Net X .bit (.pair .bit .bit)
  | add : Net X (.pair .bit .bit) .bit
  | scale (c : X → Bool) : Net X .bit .bit
  | swap (a b) : Net X (.pair a b) (.pair b a)
  | assoc (a b c) : Net X (.pair (.pair a b) c) (.pair a (.pair b c))
  | unassoc (a b c) : Net X (.pair a (.pair b c)) (.pair (.pair a b) c)
  | parallel {a b c d} (l : Net X a b) (r : Net X c d) : Net X (.pair a c) (.pair b d)
  | seq {a b c} (l : Net X a b) (r : Net X b c) : Net X a c

namespace Net
variable {X : Type}
def run {a b} (c : Net X a b) (x : X) : a.Val → b.Val := match c with
  | .identity _ => id
  | .copy => fun v => (v,v)
  | .add => fun v => v.1 || v.2
  | .scale t => fun v => t x && v
  | .swap _ _ => fun v => (v.2,v.1)
  | .assoc _ _ _ => fun v => (v.1.1,(v.1.2,v.2))
  | .unassoc _ _ _ => fun v => ((v.1,v.2.1),v.2.2)
  | .parallel l r => fun v => (l.run x v.1,r.run x v.2)
  | .seq l r => fun v => r.run x (l.run x v)
def rev {a b} (c : Net X a b) : Net X b a := match c with
  | .identity a => .identity a
  | .copy => .add
  | .add => .copy
  | .scale t => .scale t
  | .swap a b => .swap b a
  | .assoc a b c => .unassoc a b c
  | .unassoc a b c => .assoc a b c
  | .parallel l r => .parallel l.rev r.rev
  | .seq l r => .seq r.rev l.rev
def adds {a b} (c : Net X a b) : Nat := match c with
  | .add => 1
  | .parallel l r => l.adds+r.adds
  | .seq l r => l.adds+r.adds
  | _ => 0

theorem adjoint {a b} (c : Net X a b) (x : X) (u : a.Val) (v : b.Val) :
    b.dot (c.run x u) v = a.dot u (c.rev.run x v) := by
  induction c with
  | identity => rfl
  | copy => cases u <;> simp [run,rev,Port.dot]
  | add => rcases u with ⟨i,j⟩; cases v <;> simp [run,rev,Port.dot]
  | scale t => simp [run,rev,Port.dot,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
  | swap => simp [run,rev,Port.dot,Bool.or_comm]
  | assoc => simp [run,rev,Port.dot,Bool.or_assoc]
  | unassoc => simp [run,rev,Port.dot,Bool.or_assoc]
  | parallel l r li ri =>
    simp only [run,rev,Port.dot]
    rw [li,ri]
  | seq l r li ri =>
    simp only [run,rev]
    rw [ri,li]

theorem balance {a b} (c : Net X a b) :
    c.rev.adds+a.dim=c.adds+b.dim := by
  induction c with
  | identity => rfl
  | copy => decide
  | add => decide
  | scale => rfl
  | swap => simp [rev,adds,Port.dim,Nat.add_comm]
  | assoc => simp [rev,adds,Port.dim,Nat.add_assoc]
  | unassoc => simp [rev,adds,Port.dim,Nat.add_assoc]
  | parallel l r li ri =>
    simp only [rev,adds,Port.dim]
    omega
  | seq l r li ri =>
    simp only [rev,adds]
    omega

end Net
end Linear9798
