import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_Marked
abbrev V := Fin 20
structure Port where
  kind : Nat
  cut : V
  pos : Nat
  neg : Nat
  serial : Nat
  deriving DecidableEq, Repr

def fixedOff (m x : V) : Prop := m≠x ∧ (m.val/4=x.val/4 ∨ m.val%4=x.val%4)
instance (m x : V) : Decidable (fixedOff m x) := by unfold fixedOff; infer_instance

structure Site where
  kind : Nat
  pos : V → Prop
  neg : V → Prop
  clean : ∀x, pos x → ¬neg x

structure Serves (s : Site) (d : Port) : Prop where
  typed : s.kind=d.kind
  positive : ∀x : V, d.pos.testBit x.val=true → s.pos x
  negative : ∀x : V, d.neg.testBit x.val=true → s.neg x
  trueFixed : ¬s.pos d.cut
  falseFixed : ∀x, fixedOff d.cut x → ¬s.neg x

def blocks (d e : Port) : Prop :=
  d.pos.testBit e.cut.val=true ∨
  ∃x : V, (d.neg.testBit x.val=true ∧ fixedOff e.cut x) ∨
      (d.pos.testBit x.val=true ∧ e.neg.testBit x.val=true)
instance (d e : Port) : Decidable (blocks d e) := by unfold blocks; infer_instance

theorem rejects {s : Site} {d e : Port} (h : blocks d e) (x : Serves s d) (y : Serves s e) : False := by
  rcases h with t|⟨q,hq⟩
  · exact y.trueFixed (x.positive _ t)
  · rcases hq with ⟨n,k⟩|⟨p,n⟩
    · exact y.falseFixed q k (x.negative q n)
    · exact s.clean q (x.positive _ p) (y.negative _ n)

def clash (d e : Port) : Prop :=
  d.kind≠e.kind ∨ (d.cut=e.cut ∧ d.serial≠e.serial) ∨ blocks d e ∨ blocks e d
instance (d e : Port) : Decidable (clash d e) := by unfold clash; infer_instance

def data : Array Port := #[⟨16,9,0,1,0⟩,
⟨17,8,0,2,0⟩,
⟨18,8,262144,4,0⟩,
⟨19,8,32768,8,0⟩,
⟨32,5,0,1,0⟩,
⟨33,4,0,2,0⟩,
⟨34,4,262144,4,0⟩,
⟨35,4,32768,8,0⟩,
⟨36,13,526336,16,0⟩,
⟨36,13,263168,16,1⟩,
⟨36,18,8704,16,1⟩,
⟨37,12,526336,32,0⟩,
⟨37,12,263168,32,1⟩,
⟨37,18,4352,32,1⟩,
⟨38,12,788480,64,0⟩,
⟨38,12,131584,64,1⟩,
⟨38,17,4352,64,1⟩,
⟨39,12,263168,128,0⟩,
⟨39,12,655872,128,1⟩,
⟨39,17,37120,128,1⟩,
⟨48,5,256,1,0⟩,
⟨49,4,512,2,0⟩,
⟨50,4,263168,4,0⟩,
⟨51,4,0,8,0⟩,
⟨52,9,557056,16,0⟩,
⟨52,9,278528,16,1⟩,
⟨52,18,8960,16,1⟩,
⟨53,8,557056,32,0⟩,
⟨53,8,278528,32,1⟩,
⟨53,18,4864,32,1⟩,
⟨54,8,819200,64,0⟩,
⟨54,8,139264,64,1⟩,
⟨54,17,5376,64,1⟩,
⟨55,8,278528,128,0⟩,
⟨55,8,663552,128,1⟩,
⟨55,17,4352,128,1⟩,
⟨56,1,557056,256,0⟩,
⟨56,1,278528,256,1⟩,
⟨57,0,557056,512,0⟩,
⟨57,0,278528,512,1⟩,
⟨58,0,819200,1024,0⟩,
⟨58,0,139264,1024,1⟩,
⟨59,0,278528,2048,0⟩,
⟨59,0,663552,2048,1⟩,
⟨64,5,4352,1,0⟩,
⟨65,4,8704,2,0⟩,
⟨66,4,0,4,0⟩,
⟨67,4,34816,8,0⟩,
⟨68,9,561152,16,0⟩,
⟨68,9,282624,16,1⟩,
⟨68,14,131840,16,1⟩,
⟨69,8,565248,32,0⟩,
⟨69,8,286720,32,1⟩,
⟨69,14,66304,32,1⟩,
⟨70,8,557056,64,0⟩,
⟨70,8,155648,64,1⟩,
⟨70,13,66816,64,1⟩,
⟨71,8,311296,128,0⟩,
⟨71,8,139264,128,1⟩,
⟨71,13,65792,128,1⟩,
⟨72,1,561152,256,0⟩,
⟨72,1,282624,256,1⟩,
⟨73,0,565248,512,0⟩,
⟨73,0,286720,512,1⟩,
⟨74,0,557056,1024,0⟩,
⟨74,0,155648,1024,1⟩,
⟨75,0,311296,2048,0⟩,
⟨75,0,139264,2048,1⟩,
⟨76,1,786432,4096,0⟩,
⟨77,0,786432,8192,0⟩,
⟨78,0,655360,16384,0⟩,
⟨79,0,393216,32768,0⟩,
⟨80,5,8,0,0⟩,
⟨81,4,8,0,0⟩,
⟨82,4,10,0,0⟩,
⟨83,4,0,0,0⟩,
⟨84,9,557184,0,0⟩,
⟨84,9,278720,0,1⟩,
⟨84,14,131744,0,1⟩,
⟨85,8,557184,0,0⟩,
⟨85,8,278720,0,1⟩,
⟨85,14,65936,0,1⟩,
⟨86,8,557216,0,0⟩,
⟨86,8,139424,0,1⟩,
⟨86,13,65936,0,1⟩,
⟨87,8,278592,0,0⟩,
⟨87,8,139296,0,1⟩,
⟨87,13,65808,0,1⟩,
⟨88,1,559104,0,0⟩,
⟨88,1,281600,0,1⟩,
⟨89,0,559104,0,0⟩,
⟨89,0,281600,0,1⟩,
⟨90,0,559616,0,0⟩,
⟨90,0,141824,0,1⟩,
⟨91,0,279552,0,0⟩,
⟨91,0,139776,0,1⟩,
⟨92,1,835584,0,0⟩,
⟨93,0,835584,0,0⟩,
⟨94,0,696320,0,0⟩,
⟨95,0,417792,0,0⟩]

def port (i : Fin 100) : Port := data[i.val]?.getD ⟨0,0,0,0,0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem table : ∀i j : Fin 100, i≠j → clash (port i) (port j) := by decide +kernel

theorem hundred {n : Nat} (sites : Fin n → Site) (put : Fin 100 → Fin n)
    (h : ∀i, Serves (sites (put i)) (port i))
    (localOrder : ∀i j, (port i).cut=(port j).cut → put i=put j →
      (port i).serial=(port j).serial) : 100≤n := by
  have inj : Function.Injective put := by
    intro i j eq
    by_contra ne
    have a:=h i
    have b:=h j
    rw [eq] at a
    rcases table i j ne with ht|⟨hc,hs⟩|h1|h2
    · exact ht (a.typed.symm.trans b.typed)
    · exact hs (localOrder i j hc eq)
    · exact rejects h1 a b
    · exact rejects h2 b a
  simpa using Fintype.card_le_of_injective put inj

end PEqualNP.Outside.L_pcx_166_Marked
