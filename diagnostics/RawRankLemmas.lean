import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8399
def p8399Word (xs : List Nat) : Nat := xs.foldl (fun a n => (a <<< 64) + n) 0
def wd0 : Nat := p8399Word [0x1ff, 0xfeffff7befbfffee, 0xffff7fffbfffddff, 0xfef7fffbdefb7fff, 0xbdfffef7bedef6fb, 0xeeeef7ff555b55b7, 0xffdad5adfff55ab6, 0xd7ffdb6db6db5adb, 0x5ad6b57ffdb6adab, 0x6b5fff6dfff6afff, 0xb57ffdfff7ffdfff, 0x0000000000000000]
def wd1 : Nat := p8399Word [0xaaa4aa48, 0x00252a52000aa549, 0x280024924924a524, 0xa5294a8002495254, 0x94a0009200095000, 0x4a80020008002000, 0x0000000000000000]
def wd2 : Nat := p8399Word [0x200, 0x0100008410400011, 0x0000800040002200, 0x0108000421048000, 0x4200010841210904, 0x1111080000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000]
def wd3 : Nat := p8399Word [0x4002, 0x0010008004002001]
def wd4 : Nat := p8399Word [0x100, 0x1001001001001001]
def wd5 : Nat := p8399Word [0xffff8000, 0x000000ffff000000, 0x00000003e0000000, 0x000000f800000000, 0x03c000100000c440, 0x0000311000004044, 0x4004800805080001, 0x0044480200020085, 0x1200012000090400, 0x4821200482120bf9, 0xcfce33ffe61fe004, 0x36021b0820ab6360, 0x011b008da3c6c002, 0x361008d842f8004d, 0x84013610be021208, 0x2222f01b04000030, 0x0000000c000002b0, 0x1000036006034200, 0x02c0b10001802188, 0x634000000000afff, 0x857ffc0007ffdfff, 0xfe73f38cfff987f8]
def wd6 : Nat := p8399Word [0x3, 0xfffc003e00000000, 0x000000000007fff8, 0x1fffe07800000000, 0x0000000003c00f80, 0x3800000061060830, 0x0800820c04220308, 0x3021004020016108, 0x4210860400100400, 0x218832180890c044, 0x86021888602191cf, 0xd752dfff3ad2b408, 0x8aae45004f8028a0, 0x024501228051451e, 0x8a047a281e0800a2, 0x88028a210244f013, 0xe04e104500184180, 0x0002002000011880, 0xc0001860301802d8, 0x4210840001808c23, 0x085fff0c00062000, 0x310001fff0001fff, 0x73f5d4b7ffceb4ad]
def wd7 : Nat := p8399Word [0x7fff8, 0x00000f8000000000, 0x0000000000000000, 0x0000000001fffe07, 0xfff81e007803e003, 0x8000000100101006, 0x6046040310481810, 0x0c48020100200020, 0x080100e0c280a028, 0x4061840612203091, 0x018407101c4062cf, 0xeba56fff3d2d595d, 0x0c048603e10050c0, 0x0486024300a18805, 0x0c201430841127c3, 0x009f0c07841e20f8, 0x40e4208600400400, 0x0018118000041a06, 0x00001b0180c05800, 0x5816057ffc30a028, 0x0b00006000068000, 0x340001fff7ffc000, 0xb3fae95bffcf4b56]
def wd8 : Nat := p8399Word [0x1fffe0000000000, 0x1fffef0000000007, 0xfffbc0000003efb8, 0x0000004001400092, 0x0050002500000900, 0x9600100368002400, 0x5a8012404800ad00, 0x04a0904a800250d4, 0x12c04a012804a37f, 0xbf39b0343e7f9c12, 0x5009281082018502, 0x18284f94050a0028, 0x5044f943c0200914, 0x10b750f0080844fb, 0xee00412810005000, 0x0000140000054006, 0xd7ffc00c00db001b, 0x0016b0000036002b, 0x6000006dfff00000, 0x357ffc0000000000, 0xdfefce6c0d0f9fe7]
def wd9 : Nat := p8399Word [0x7fffb, 0xfffde000000003ff, 0xfc0000000007fffb, 0xc000000001fffef0, 0x000000007bd80000, 0x000001016c001924, 0x6b00064a156a8019, 0x280026d00000496a, 0x0001a48092b40000, 0x694126951ab4a801, 0xa506941a506940fe, 0x3c3fb338e7e1815c, 0x60ae307800020600, 0x8f300418020c011e, 0x60f02181004025d8, 0x3c046040101ef620, 0x84008030405b0000, 0x001ac00000055ab0, 0x0000000db600001b, 0x5ac000000036ad80, 0x0000006dfff6afff, 0x8000000000000000, 0x3f8f0fecce39f860]
def wd10 : Nat := p8399Word [0x3ff, 0xfdfffeffff700000, 0x0000000001fffef7, 0xfffbdefb00000000, 0x00000154000001c6, 0x2152107380000001, 0xcc00369b4d6a0000, 0x000038c0daa6a9ad, 0x0e7000e600073000, 0x3980e603980e609a, 0xb1ded5514faabc60, 0x80304021040c0804, 0xaf4057a02bd01c50, 0x80014200080035e0, 0x3cd780f7bec08001, 0x0008024055000000, 0x001ad5adfff00000, 0x0000000db6db5ac0, 0x000000000036adab, 0x6b5fff0000000000, 0x0000000000000000, 0x26ac77b55453eaaf]
def wd11 : Nat := p8399Word [0x3ff, 0xfdfffeffff77fffb, 0xdfffef7bec000000, 0x0000000000000000, 0x00000154254241f8, 0x0000007c00000001, 0xf00034da6d4b6d4b, 0x52d43f0600000000, 0x0f8000f80007c000, 0x3e00f803e00f80ad, 0x32ef6aa197d55d81, 0x00c0804208301008, 0xcf8067c033e01d9f, 0x00f67c03defb4600, 0x0118000200100040, 0x00800480555b55b7, 0xffc0000000000000, 0x0000000db6db5adb, 0x5ad6b57ffd800000, 0x0000000000000000, 0x0000000000000000, 0x2b4cbbdaa865f557]
def wd12 : Nat := p8399Word [0x7fffb, 0xfffdefbeffffb800, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000148149e00, 0x4a04a780156ad25e, 0x006d800000000000, 0x0001c00000000000, 0x7000070000380001, 0xc007001c007003f6, 0x3ff03cf2d9f86dfe, 0x00ff007befbfe00e, 0xf00078003c0011e0, 0x0087800210827800, 0x21e0008420800082, 0x08000700555b55b7, 0xffdad5adfff55ab6, 0xd7ffdb6000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xfd8ffc0f3cb67e1b]
def wd13 : Nat := p8399Word [0x1ff, 0xfeffff7befbfffee, 0xffff7fffbfffddff, 0xfef7fffbdefb7fff, 0xbdfffef7bedef6fb, 0xeeeef7ff555b55b7, 0xffdad5adfff55ab6, 0xd7ffdb6db6db5adb, 0x5ad6b57ffdb6adab, 0x6b5fff6dfff6afff, 0xb57ffdfff7ffdfff, 0xffffffffffffffff]
def wd14 : Nat := p8399Word [0x202010000802020, 0x0001000080404002, 0x0200080802080000, 0x8000020002001000, 0x2002100100000000, 0x0000000000000080, 0x0000006000000200, 0x0200800001800000, 0x0040000000002000, 0x0100000000001fff, 0x7271d084ffc884a8]
def wd15 : Nat := p8399Word [0x4, 0x0400020020004040, 0x0002000100808000, 0x0400001000100041, 0x0001040084020008, 0x0020200200000000, 0x0000000000000200, 0x0000030000004000, 0x0000010000002008, 0x0300000000008000, 0x0400000007ffc000, 0xb272e108ffc90350]
def wd16 : Nat := p8399Word [0x1000080000010100, 0x0008008401020000, 0x1000084040200004, 0x0001101008000008, 0x2200400800000000, 0x0000000000000000, 0x1000000000030000, 0x0000b00000000008, 0x6000000000000000, 0x057ffc0000000000, 0xde63c20c0d0987e0]
def wd17 : Nat := p8399Word [0x4, 0x2002100800020200, 0x0110000802040002, 0x2010008000400048, 0x0400200010021200, 0x0000801000000000, 0x00000000000002b0, 0x0000000006000000, 0x02c0000000002180, 0x000000000000afff, 0x8000000000000000, 0x3e03038cce398060]
def wd18 : Nat := p8399Word [0x80000, 0x010000803fffc000, 0x0000000000000040, 0x04010010be000000, 0x0000000004000000, 0x1000000c04000000, 0x0010000006034200, 0x0000000200002188, 0x6340800008000040, 0x0002000800200080, 0x26207384545182a8]
def wd19 : Nat := p8399Word [0x200000, 0x010000803fffc002, 0x0010080042f80000, 0x0000000000000000, 0x0000000004000030, 0x1000000004000000, 0x0010000006034200, 0x02c0b10201800000, 0x0000800008000040, 0x0002000800200080, 0x2a40b388a8618550]
def wd20 : Nat := p8399Word [0x4, 0x0002000820bfffe0, 0x0000000020000000, 0x0000000000800000, 0x0000000020000000, 0x0000000004000031, 0x0000000c400002b0, 0x1100036000000000, 0x0000001000000000, 0x0004000040000200, 0x0010004001000400, 0xfc03f00c3cb00618]
def wd21 : Nat := p8399Word [0x8, 0x0804040041000080, 0x0004000200010004, 0x0800102004000082, 0x0002080100042010, 0x4044000400000000, 0x0000000000001800, 0x0000180000000000, 0x4010040000008020, 0x0800000000060000, 0x300001fff0000000, 0x33f0c013ffce0004]
def wd22 : Nat := p8399Word [0x8000002000000, 0x0000010000000008, 0x0007fff800000000, 0x0002002000004013, 0xe000000000004000, 0x0400000001010000, 0xc004000000180018, 0x0010800080000023, 0x0000200c02000010, 0x3100800200080020, 0x53e5c4240d0e94a5]
def wd23 : Nat := p8399Word [0x8, 0x00ffff0000000000, 0x02000000000001ff, 0xfe00200000000080, 0x080000000004f000, 0x8000000000180002, 0x0802000082011880, 0x0208000030000018, 0x4200002100008c00, 0x0008400c84062420, 0x0021008402100840, 0x338504a4ce08b020]
def wd24 : Nat := p8399Word [0x8020400004000800, 0x0240012000500410, 0x80004200080000a0, 0x0802802102408001, 0x0008004000000000, 0x0002002000000000, 0x00000000301802c0, 0x0000000000008c23, 0x085fff0000000000, 0x0000000000000000, 0x22a454b55442a0ad]
def wd25 : Nat := p8399Word [0x80000008000000, 0x02000100004005ff, 0xfe07fff81e080000, 0x0000000000000000, 0x0000000000184180, 0x0c00000003000000, 0x000c0000301802d8, 0x4210840181800000, 0x0000600006000030, 0x0001800600180060, 0x23449092a844b405]
def wd26 : Nat := p8399Word [0x8, 0x00ffff004f802000, 0x0000000000000100, 0x0004000010000000, 0x0000000000000002, 0x0000000000184182, 0x0002002080011880, 0xc200186000000000, 0x0000002000000000, 0x0008000080000400, 0x0020008002000800, 0x7185d4073c863409]
def wd27 : Nat := p8399Word [0x10, 0x0000000080000000, 0x0000020000000000, 0x0000100080000100, 0x01fffe00000800f8, 0x4000000000000000, 0x0080100000440006, 0x0001000000c00000, 0x0016000010300028, 0x0000086000800004, 0x3400200080020008, 0x93eac8480d0f0b46]
def wd28 : Nat := p8399Word [0x1ff, 0xfe04000000000000, 0x0400000000000004, 0x0020000000007fff, 0x80040000001e2020, 0x0000000000400004, 0x0118000100841a00, 0x0402000180000000, 0x580000402030a000, 0x0010106101068808, 0x0040410104041010, 0x338a0948ce094840]
def wd29 : Nat := p8399Word [0x40, 0x0000000100000000, 0x0400020000800800, 0x0000000000007fff, 0x81fffe0784000000, 0x0000000000000000, 0x0198118000c00000, 0x0003000180c05800, 0x000000003030a028, 0x0b0018000180000c, 0x0000600180060018, 0x22a8611154434a06]
def wd30 : Nat := p8399Word [0x101, 0x0000800200001000, 0x0480024000a00805, 0x0020140084110600, 0x0018000200100040, 0x0080008000400400, 0x0000000000000000, 0x0000000180c05800, 0x5816057ffc000000, 0x0000000000000000, 0x0000000000000000, 0x2348a95aa8454156]
def wd31 : Nat := p8399Word [0x1ff, 0xfe040003e1004000, 0x0000000000000000, 0x0000000000002000, 0x0080000400000080, 0x0000000000400404, 0x0018118100041a06, 0x04001b0000000000, 0x0000004000000000, 0x0010000100000800, 0x0040010004001000, 0xb18ae80b3c864a12]
def wd32 : Nat := p8399Word [0x10, 0x4008201000000400, 0x0820041000080008, 0x4040210100000110, 0x1004404000084420, 0x8400002000000000, 0x0000000000054000, 0x0000000c0000001b, 0x0000000000360000, 0x0000006dfff00000, 0x0000000000000000, 0x1f8f0e6c0c099860]
def wd33 : Nat := p8399Word [0x8007fff81000000, 0x0000400000000100, 0x11fffef008000001, 0x0000000010000000, 0x2080140008400000, 0x0021000c00db0000, 0x000000041036002b, 0x6001080010800084, 0x0004201080420108, 0x06ac462404038aa7]
def wd34 : Nat := p8399Word [0x8007fff81000008, 0x0047fffbc0200000, 0x0010000000000040, 0x0000000010005000, 0x2400000009000000, 0x0024000c00db001b, 0x0016b00480000000, 0x0001200012000090, 0x0004801200480120, 0x0b4c8a4808059547]
def wd35 : Nat := p8399Word [0x12, 0x0009001082018002, 0x1000480004000020, 0x0004800200000800, 0x00a0008000000082, 0x0800010010005000, 0x0000140000054006, 0xd7ffc00000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xdd8fcc0c0c061e03]
def wd36 : Nat := p8399Word [0x40, 0x0020002000000000, 0xffff040002000010, 0x0000000000007fff, 0xbc04004010008000, 0x0000000040000000, 0x411ac00010800000, 0x0042000db6000000, 0x000000082036ad80, 0x0002100021000108, 0x0008402100840210, 0x268c07a44411e820]
def wd37 : Nat := p8399Word [0x100, 0x0080004000000000, 0xffff0400020001ff, 0xfef0200100400400, 0x0000000000100000, 0x00000000405b0000, 0x4800000012000000, 0x0048000db600001b, 0x5ac0000900000000, 0x0002400024000120, 0x0009002400900240, 0x2b0c0bc88821f040]
def wd38 : Nat := p8399Word [0x1ff, 0xfeffff7800020000, 0x8000000000000100, 0x0080000000002000, 0x2000000000000000, 0x00000000405b0006, 0x001ac00180055ab0, 0x0600000000000000, 0x0000006000000000, 0x0018000180000c00, 0x0060018006001800, 0x3d8f0c0c0c307800]
def wd39 : Nat := p8399Word [0xffff7fffbfffdc10, 0x0000400008000400, 0x0010000200000000, 0x0000000055000000, 0x700000001c000000, 0x0070000db6db5ac0, 0x0000000e00000000, 0x00038000380001c0, 0x000e003800e00380, 0x220c33900041e007]
def wd40 : Nat := p8399Word [0x60, 0x00300021040c0004, 0xa000500028001040, 0x0001000000003000, 0x20c0008420800000, 0x0000020055000000, 0x001ad5adfff00000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x248c740514126a0b]
def wd41 : Nat := p8399Word [0x180, 0x00c0004208300008, 0xc000600030001180, 0x0086000210824000, 0x0100000000000000, 0x00000400555b55b7, 0xffc0000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x290cb80a28247413]
def wd42 : Nat := p8399Word [0x2, 0x8800400000004000, 0x200010820101, 0x80240188014208, 0xa000400402000800]
def wd43 : Nat := p8399Word [0x2, 0x8800400000004000, 0x208010860101, 0x80240188014208, 0xa000400402000800]
def wd44 : Nat := p8399Word [0x32201300448, 0x1302800820004404, 0x4080001043200400, 0x86201002028241a]
def wd45 : Nat := p8399Word [0x8, 0x640000040101c004, 0xc0a0260410058, 0x880044000214800]
def wd46 : Nat := p8399Word [0x10100008, 0x88082460200200, 0x800001200010a, 0x100004000004862, 0x2800200209056000, 0x900000094040840]
def wd47 : Nat := p8399Word [0x2000004000884, 0x2001008001010000, 0x9014003041000020, 0x2400000040000010, 0x8004401020000, 0x2080000602008448]
def wd48 : Nat := p8399Word [0x608080, 0x1280000520001420, 0x8124408408600080, 0x1002000010040000, 0x80a1400000000800]
def wd49 : Nat := p8399Word [0x60c080, 0x12800005a0001420, 0x8124408c08602080, 0x1202000010040010, 0x80a1400000000800]
def wd50 : Nat := p8399Word [0x20108108, 0xa07112d02201e608, 0x287b015f10800162]
def wd51 : Nat := p8399Word [0x3000, 0x2000042000898004, 0x2000484000901040, 0x400041018444000, 0x9000040900000000]
def wd52 : Nat := p8399Word [0x20c121, 0xa9000406a007820e, 0x280003cd0c0608c9]
def wd53 : Nat := p8399Word [0x2204880402, 0x14006248d0000880, 0x98019200a200a400, 0x440e000410081012]
def wd54 : Nat := p8399Word [0x2c862000000, 0x92431a0850842a29, 0x6400044a10008800, 0x280112010404008]
def wd55 : Nat := p8399Word [0x20840300048, 0x4104360080c40008, 0xa0aa8040b49b0660]
def wd56 : Nat := p8399Word [0xb6271108, 0x82281880000091a0, 0xa44820006012053, 0x802003108010004]
def wd57 : Nat := p8399Word [0x2b0281041201, 0x901226210a0000e8, 0x5800440400280220, 0xa2a000890818d020]
def wd58 : Nat := p8399Word [0x60c080, 0x1280000520001420, 0x8124408c08602080, 0x1202000010040000, 0x80a1400000000800]
def wd59 : Nat := p8399Word [0xa101904, 0x1000050098040000, 0x34a0000058010000, 0x10010012004000, 0x9604300000082400, 0x20000008011220]
-- Computational declarations are placed first using the organization of public L_meta_8401.
section hz1
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
def Z0 : ℕ → ℕ := fun _ => 0
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
end hz1
section hz2
variable {R : ℕ → ℕ}
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
end hz2
section hz3
variable {R : ℕ → ℕ}
open Finset in
def Acc (n T k b : ℕ) (D : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ U ⊆ S, ∀ q, q + b < k + ∑ w ∈ S \ U, D w → ¬ Sol Z0 n (T &&& n) q (C n (Im n U))
inductive Kd
  | N | K0 | KA | KC
def Kd.ok (n : ℕ) (d : Bool) (a c : ℕ) : Kd → Prop
  | .N => True
  | .K0 => Cst n (op d a c)
  | .KA => op d a c &&& n = a &&& n
  | .KC => op d a c &&& n = c &&& n
def Kd.del (la lc : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => 1 + la + lc
  | .KA => 1 + lc
  | .KC => 1 + la
def Kd.out (la lc : ℕ) : Kd → ℕ
  | .N => 1 + la + lc
  | .K0 => 0
  | .KA => la
  | .KC => lc
def Kd.kpa (x : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => x
  | .KA => 0
  | .KC => x
def Kd.kpc (x : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => x
  | .KA => x
  | .KC => 0
structure DStep (κ : Kd) (D D' : ℕ → ℕ) (g a c : ℕ) (S' : Finset ℕ) : Prop where
  hg : D' g ≤ κ.out (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c)
  ha : a ∈ S' → D' a ≤ κ.kpa (D a)
  hc : c ∈ S' → D' c ≤ κ.kpc (D c)
  ho : ∀ w ∈ S', w ≠ g → w ≠ a → w ≠ c → D' w ≤ D w
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
  d : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 714
def AA : Nat := wd0
def HX : Nat := wd1
def HY : Nat := wd2
end hz3
noncomputable section hz4
variable {R : ℕ → ℕ}
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def masksOf (e : Nat) : Nat × Nat := (Nat.land e HX,Nat.land e HY)
def maskedHit (f : Nat) (e : Nat × Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Nat.land f e.2) 0)) false (Nat.beq (Nat.land f e.1) 0)
def maskedHits (f : Nat) (es : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => Bool.rec (motive := fun _ => Bool) ih true (maskedHit f e)) es
def maskedRect (d : Bool) (l o : Nat) (v : List W) : List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool) (fun _ => false)
    (fun w _ ih m => (fun f => Bool.rec (motive := fun _ => Bool) (ih (masksOf f :: m)) true (maskedHits f m)) (flag d l o w)) v
lemma maskedHit_eq (f e : Nat) : maskedHit f (masksOf e) = hit f e := by
  simp only [maskedHit,masksOf,hit,show ∀ x y : Nat, Nat.land x y = x &&& y from fun _ _ => rfl,Nat.and_assoc]
lemma maskedHits_eq (f : Nat) (m : List Nat) : maskedHits f (m.map masksOf) = hits f m := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change Bool.rec (motive := fun _ => Bool) (maskedHits f (m.map masksOf)) true (maskedHit f (masksOf e)) = _
    rw [maskedHit_eq,ih]
    rfl
lemma maskedRect_eq (d : Bool) (l o : Nat) (v : List W) (m : List Nat) :
    maskedRect d l o v (m.map masksOf) = rect d l o v m := by
  induction v generalizing m with
  | nil => rfl
  | cons w v ih =>
    let f := flag d l o w
    change Bool.rec (motive := fun _ => Bool) (maskedRect d l o v ((f::m).map masksOf)) true (maskedHits f (m.map masksOf)) =
      Bool.rec (motive := fun _ => Bool) (rect d l o v (f::m)) true (hits f m)
    rw [maskedHits_eq,ih]
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (kb : Bool) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) (st z (fun z => mk (f z))) false kb) (Nat.beq (Nat.land z g) g)
def laneL (w : Nat) (L : List Nat) : Nat := List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih w) d) L
def WL (N : Nat) : Nat := Nat.succ (Nat.mul 2 N)
def FM2 (N : Nat) : Nat := Nat.sub (Nat.pow 2 (Nat.mul 2 N)) 1
def R16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 1)
def MM16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 (FM2 N))
def GG16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 (Nat.pow 2 (Nat.mul 2 N)))
def MD16 (N : Nat) : Nat := Nat.sub (Nat.pow 2 (WL N)) 32
def U16 : Nat := laneL 5 (List.replicate 16 1)
def zflG (N np q nc : Nat) : Nat := Nat.land (Nat.sub U16 (Nat.mod (Nat.shiftRight (Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N)) (Nat.mul 2 N)) (MD16 N))) nc
def zfl (np q nc : Nat) : Nat := zflG NN np q nc
def MU (f : Nat) : Nat := Nat.mul 31 f
def rmk (sa : Nat) (ka : Bool) (da : Nat) (sc : Nat) (kc : Bool) (dc : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (ih h) (st dc fun d => W.rec (motive := fun _ => Bool) (fun s a b c r0 _ => ih (fun r => h (⟨s, a, b, c, r0, d⟩ :: r))) w) kc) (Nat.beq w.s sc))
    (Bool.rec (motive := fun _ => Bool) (ih h) (st da fun d => W.rec (motive := fun _ => Bool) (fun s a b c r0 _ => ih (fun r => h (⟨s, a, b, c, r0, d⟩ :: r))) w) ka) (Nat.beq w.s sa)) v
def rmkB (sa da sc dc d0 : Nat) (v : List W) (h : List W → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (rmk sa true da sc true dc v h) (h v) (Nat.beq d0 0)
def put (m s x y : Nat) (v : List W) (d : Nat) (h : List W → Bool) : Bool :=
  st s fun s => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (st x fun x1 => st y fun y1 => st (Nat.lor x y) fun w => st d fun d => ins ⟨s, x1, y1, w, 0, d⟩ v h) false (Nat.beq s m)) false (Nat.beq s 0)
def kids (c : Bool → ((List W → Bool) → Bool) → Nat → Bool) (e n z u w fA fC : Nat) (a c' : W) (oa oc ka kc kb : Bool) (mk : Nat → (List W → Bool) → Bool) : Bool :=
  (fun fN sA sC =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
        (c kb (fun h => mk fN (fun r => rmkB a.s (Nat.land sC a.d) c'.s (Nat.land sA c'.d) (Nat.add a.d c'.d) r h)) (Nat.sub (Nat.sub z a.c) c'.c))
        (Nat.ble (Nat.succ (Nat.succ n)) e)) true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (c kc (fun h => mk (Nat.add fN (Nat.land (MU (Nat.add fN fA)) a.d)) (fun r => rmk a.s false 0 c'.s true (Nat.land sA c'.d) r h)) (Nat.sub (Nat.sub z (Nat.land sC a.d)) c'.c)) oa) true
        (Bool.rec (motive := fun _ => Bool) false
          (c ka (fun h => mk (Nat.add fN (Nat.land (MU (Nat.add fN fC)) c'.d)) (fun r => rmk a.s true (Nat.land sC a.d) c'.s false 0 r h)) (Nat.sub (Nat.sub z a.c) (Nat.land sA c'.d))) oc)) (Nat.ble (Nat.succ n) e))) true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (c false (fun h => mk (Nat.add (Nat.add fN (Nat.land (MU (Nat.add fN fA)) a.d)) (Nat.land (MU (Nat.add fN fC)) c'.d)) (fun r => rmk a.s false 0 c'.s false 0 r h)) (Nat.sub (Nat.sub z (Nat.land sC a.d)) (Nat.land sA c'.d))) oc) oa))
  (Nat.sub (Nat.sub (Nat.sub u w) fA) fC) (MU (Nat.add w fA)) (MU (Nat.add w fC))
def mid (f : Nat → List W → Bool) (m g np e n z : Nat) (v : List W) (a c : W) (oa oc ka kc kb : Bool) (s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    ((fun u w => (fun nc => st (zfl np (Nat.xor a.s s) nc) fun eA => st (zfl np (Nat.xor c.s s) (Nat.sub nc eA)) fun eC =>
      Bool.rec (motive := fun _ => Bool) false
        (st (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) fun z =>
          kids (child f g) e n z u w (Nat.add eA (Nat.sub c.c (Nat.land c.c w))) (Nat.add eC (Nat.sub a.c (Nat.land a.c w))) a c oa oc ka kc kb (put m s x y v))
        (Nat.beq (Nat.land (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) g) g))
      (Nat.sub u (Nat.lor (Nat.lor a.c c.c) w))) (Nat.shiftRight g 4) (Nat.lor x y))
    (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (Bool.rec (motive := fun _ => Bool)
    (st (Nat.xor a.s m) fun s => st (Nat.sub z a.c) fun z => (fun u =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (st u fun d1 => ins ⟨s, a.b, a.a, a.c, 0, d1⟩ v (fun v => child (f s) g false (rmk a.s true 0 a.s true 0 v) (Nat.sub z a.c))) (Nat.ble (Nat.succ n) e)) true
        (Bool.rec (motive := fun _ => Bool) false (st (Nat.add u a.d) fun d1 => ins ⟨s, a.b, a.a, a.c, 0, d1⟩ v (fun v => child (f s) g false (rmk a.s false 0 a.s false 0 v) z)) (Nat.ble n e)))
      (Nat.sub (Nat.shiftRight g 4) a.c)) false (Nat.beq (Nat.succ a.s) q))) r
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def overlapping (d : Bool) (l : Nat) (v : List W) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ tail seen => (fun mask => Nat.lor (Nat.land mask seen) (tail (Nat.lor seen mask))) (sp d l w.s)) v
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (overlapping d l v 0)
lemma overlapping_eq (d : Bool) (l : Nat) (v : List W) (seen : Nat) :
    overlapping d l v seen = (seen &&& cov d l v) ||| twice d l v := by
  induction v generalizing seen with
  | nil => simp [overlapping,cov,twice]
  | cons w v ih =>
    change (sp d l w.s &&& seen) ||| overlapping d l v (seen ||| sp d l w.s) =
      (seen &&& (sp d l w.s ||| cov d l v)) ||| ((sp d l w.s &&& cov d l v) ||| twice d l v)
    rw [ih]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.testBit_or]
    cases (sp d l w.s).testBit i <;> cases seen.testBit i <;> cases (cov d l v).testBit i <;>
      cases (twice d l v).testBit i <;> rfl
lemma wst_eq_twice (d : Bool) (l : Nat) (v : List W) : wst d l v = l ^^^ twice d l v := by
  simp [wst,overlapping_eq]

def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
end hz4
section hz5
variable {R : ℕ → ℕ}
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
def segsX : List (ℕ × ℕ) := [(63, 77), (77, 91), (91, 105), (105, 119), (119, 121), (121, 123), (123, 126), (126, 140), (140, 142), (142, 144), (144, 147), (147, 161), (161, 164), (164, 167), (167, 181), (181, 183), (183, 186), (186, 188), (188, 191), (191, 194), (194, 196), (196, 198), (198, 201), (201, 204), (204, 206), (206, 208), (208, 211), (211, 214), (214, 217), (217, 231), (231, 233), (233, 235), (235, 238), (238, 240), (240, 243), (243, 245), (245, 248), (248, 250), (250, 253), (253, 255), (255, 258), (258, 261), (261, 264), (264, 266), (266, 269), (269, 271), (271, 274), (274, 277), (277, 280), (280, 283), (283, 286), (286, 289), (289, 292), (292, 295), (295, 298), (298, 301), (301, 315), (315, 317), (317, 320), (320, 323), (323, 326), (326, 328), (328, 330), (330, 333), (333, 335), (335, 337), (337, 339), (339, 353), (353, 356), (356, 358), (358, 361), (361, 363), (363, 365), (365, 368), (368, 370), (370, 373), (373, 387), (387, 390), (390, 393), (393, 395), (395, 397), (397, 399), (399, 402), (402, 405), (405, 407), (407, 409), (409, 411), (411, 413), (413, 415)]
def segsY : List (ℕ × ℕ) := [(415, 427), (427, 432), (432, 436), (436, 440), (440, 444), (444, 450), (450, 456), (456, 459), (459, 464), (464, 469), (469, 472), (472, 478), (478, 483), (483, 488), (488, 505), (505, 510), (510, 527), (527, 530), (530, 536), (536, 541), (541, 546), (546, 563), (563, 568), (568, 585), (585, 589), (589, 606), (606, 623), (623, 640), (640, 644), (644, 662), (662, 668), (668, 674), (674, 679), (679, 696), (696, 713)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
def lane (w n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (w * j)
def fb (x j : ℕ) : ℕ := (x.testBit (5 * j)).toNat
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ (b : ℕ → ℕ) (D : ℕ → ℕ → ℕ), (∀ j < P.length, b j ≤ 15) ∧ (∀ j < P.length, Acc (P.getD j 0) T k (b j) (D j) S) ∧
    (∀ w ∈ v, w.d = pk P.length (fun j => D j w.s)) ∧ (∀ j < P.length, k + ∑ s ∈ S, D j s ≤ 15) ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g np T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
  hnp : ∃ f : ℕ → ℕ, (∀ j < 16, f j < 2 ^ (2 * NN)) ∧ np = lane (WL NN) 16 f ∧ ∀ j < P.length, j < 16 → P.getD j 0 &&& f j = P.getD j 0
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0, 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0, 0⟩
def wd (w : W) (d : ℕ) : W := ⟨w.s, w.a, w.b, w.c, w.r, d⟩
def upd (sa da sc dc : ℕ) (w : W) : W := bif Nat.beq w.s sa then wd w da else bif Nat.beq w.s sc then wd w dc else w
def kp (sa : ℕ) (ka : Bool) (sc : ℕ) (kc : Bool) (w : W) : Bool := bif Nat.beq w.s sa then ka else bif Nat.beq w.s sc then kc else true
def kdOf (fo FA FC : ℕ) : Kd := if fo = 1 then .K0 else if FA = 1 then .KA else if FC = 1 then .KC else .N
def fAo (e o c : ℕ) : ℕ := Nat.add e (Nat.sub c (Nat.land c o))
def fNo (u w fA fC : ℕ) : ℕ := Nat.sub (Nat.sub (Nat.sub u w) fA) fC
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0, 0⟩
end hz5
noncomputable section hz6
variable {R : ℕ → ℕ}
def len (v : List W) : Nat := List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) v
def geo (w n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.add (Nat.shiftLeft ih w) 1) n
def LNN : Nat := Nat.mul 12 NN
def LN2 : Nat := Nat.mul 24 NN
def LN4 : Nat := Nat.mul 48 NN
def LM1 : Nat := Nat.mul 13 NN
def LM2 : Nat := Nat.mul 26 NN
def LM4 : Nat := Nat.mul 52 NN
def RL : Nat := geo NN 12
def PLN : Nat := Nat.pow 2 LNN
def AAR : Nat := Nat.mul AA RL
def HXR : Nat := Nat.mul HX (geo NN 84)
def HYR : Nat := Nat.mul HY (geo NN 84)
def MRR : Nat := Nat.mul (Nat.sub (Nat.pow 2 NN) (Nat.pow 2 64)) (geo NN 84)
def TOPR : Nat := Nat.shiftLeft (geo NN 72) LM1
def GMD : Nat := Nat.sub (Nat.pow 2 (Nat.sub NN 1)) 1
def pkd (d : Bool) (l : Nat) (v : List W) : Nat := List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.shiftLeft (sp d l w.s) (Nat.mul NN (len t))) ih) v
def dbl (m x : Nat) : Nat := Nat.lor x (Nat.shiftLeft x m)
def eg2 (G : Nat) : Nat := Nat.shiftRight (Nat.mod (Nat.land (Nat.land (Nat.add (Nat.land G HXR) MRR) (Nat.add (Nat.land G HYR) MRR)) TOPR) GMD) 1
def eg1 (F : Nat) : Nat := eg2 (Nat.land (dbl LN4 (dbl LN2 (dbl LNN F))) (dbl LM4 (dbl LM2 (dbl LM1 F))))
def edg (d : Bool) (l o : Nat) (v : List W) : Nat := eg1 (Nat.mod (Nat.add (Nat.land (pkd d l v) (Nat.mul o RL)) AAR) PLN)
def f12c (b : Nat) : Nat := Nat.land (Nat.lor b (Nat.shiftRight b 12)) 4095
def f12b (a : Nat) : Nat := f12c (Nat.lor a (Nat.shiftRight a 24))
def f12 (w : Nat) : Nat := f12b (Nat.lor w (Nat.shiftRight w 48))
def f13c (b : Nat) : Nat := Nat.land (Nat.lor b (Nat.shiftRight b 13)) 4095
def f13b (a : Nat) : Nat := f13c (Nat.lor a (Nat.shiftRight a 26))
def f13 (w : Nat) : Nat := f13b (Nat.lor w (Nat.shiftRight w 52))
def nbr (e S : Nat) : Nat := Nat.lor (f12 (Nat.land e (Nat.mul S wd3))) (f13 (Nat.land e (Nat.mul S wd4)))
def bfs (e : Nat) (fuel : Nat) : Nat → Nat → (Nat → Bool) → Bool := Nat.rec (motive := fun _ => Nat → Nat → (Nat → Bool) → Bool) (fun _ _ _ => false)
  (fun _ ih A B k => st (Nat.lor A (nbr e B)) (fun a => st (Nat.lor B (nbr e a)) (fun b => Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) (ih a b k) (k (Nat.lor a b)) (Nat.beq (Nat.lor A B) (Nat.lor a b))) (Nat.beq (Nat.land a b) 0)))) fuel
def nonb (e : Nat) (fuel : Nat) : Nat → Bool := Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
  (fun _ ih r => Bool.rec (motive := fun _ => Bool) (bfs e 12 (Nat.gcd r 2048) 0 (fun c => ih (Nat.sub r (Nat.land r c)))) false (Nat.beq r 0)) fuel
def nonbip (e : Nat) : Bool := nonb e 12 (Nat.lor (f12 e) (f13 e))
def tch (i : Nat) : Nat := Nat.lor (Nat.mul i wd3) (Nat.mul i wd4)
def del (e i : Nat) : Nat := Nat.xor (Nat.lor e (tch i)) (tch i)
def ne0 (e : Nat) : Bool := Bool.rec (motive := fun _ => Bool) true false (Nat.beq e 0)
def kF (_ : Nat) : Bool := false
def kF2 (_ _ : Nat) : Bool := false
def kT2 (_ _ : Nat) : Bool := true
def tst1 (h : Nat) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (F (fun i => ne0 (del h i)) kT2) false (nonbip h)
def tri5 (a L r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (Nat.lor a (Nat.gcd L 4096)) r (Nat.beq L 0)
def tri4 (h i N k r : Nat) : Nat := tri5 (Nat.lor i k) (Nat.land (nbr h k) N) r
def tri3 (h i N M r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (tri4 h i N (Nat.gcd M 4096) r) r (Nat.beq M 0)
def tri2 (h i N r : Nat) : Nat := tri3 h i N (Nat.land (nbr h N) N) r
def tri1 (h i r : Nat) : Nat := tri2 h i (nbr h i) r
def tri (h : Nat) (fuel : Nat) : Nat → Nat := Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
  (fun _ ih r => Bool.rec (motive := fun _ => Nat) (tri1 h (Nat.gcd r 2048) (ih (Nat.sub r (Nat.gcd r 2048)))) 0 (Nat.beq r 0)) fuel
def k1 (h i : Nat) : Bool := nonbip (del h i)
def k2 (h i j : Nat) : Bool := ne0 (del (del h i) j)
def k3 (h T i : Nat) : Bool := Bool.rec (motive := fun _ => Bool) (nonbip (del h i)) true (Nat.beq (Nat.land i T) 0)
def k4 (h T i j : Nat) : Bool := Bool.rec (motive := fun _ => Bool) true (ne0 (del (del h i) j)) (Nat.beq (Nat.land (Nat.lor i j) T) (Nat.lor i j))
def tst2 (h : Nat) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool := st (tri h 12 (f12 h)) (fun T => Bool.rec (motive := fun _ => Bool) (F (k3 h T) (k4 h T)) (F (k1 h) (k2 h)) (Nat.beq T 0))
def rawFirst (v : List W) : List W :=
  v.filter (fun w => !(w.r == 0)) ++ v.filter (fun w => w.r == 0)
def tsn (d : Bool) (l e : Nat) (v : List W) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool :=
  (fun n => (fun o => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F kF kF2) (st (edg false l o v) (fun h => tst2 h F)) (Nat.beq (Nat.succ (Nat.succ n)) e))
      (st (edg false l o v) (fun h => tst1 h F)) (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) false (F kF kF2) (!(maskedRect d l o (rawFirst v) []))) (Nat.beq n e)) (wst d l v)) (len v)
end hz6
lemma hit_swap (f e : Nat) : hit f e = hit e f := by
  unfold hit
  rw [show Nat.land f e = Nat.land e f from Nat.and_comm f e]
lemma hits_cons_eq (f e : Nat) (m : List Nat) :
    hits f (e :: m) = (hit f e || hits f m) := by
  change Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) = _
  cases hit f e <;> rfl
lemma rect_cons_eq (d : Bool) (l o : Nat) (w : W) (v : List W) (m : List Nat) :
    rect d l o (w :: v) m = (hits (flag d l o w) m || rect d l o v (flag d l o w :: m)) := by
  change Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) = _
  cases hits (flag d l o w) m <;> rfl
lemma hits_perm {m n : List Nat} (f : Nat) (h : m.Perm n) : hits f m = hits f n := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [hits_cons_eq,ih]
  | swap x y s => simp only [hits_cons_eq,Bool.or_left_comm]
  | trans a b ha hb => exact ha.trans hb
lemma rect_acc_perm (d : Bool) (l o : Nat) (v : List W) {m n : List Nat} (h : m.Perm n) :
    rect d l o v m = rect d l o v n := by
  induction v generalizing m n with
  | nil => rfl
  | cons x v ih => rw [rect_cons_eq,rect_cons_eq,hits_perm (flag d l o x) h,ih (h.cons (flag d l o x))]
lemma rect_perm (d : Bool) (l o : Nat) {v u : List W} (h : v.Perm u) (m : List Nat) :
    rect d l o v m = rect d l o u m := by
  induction h generalizing m with
  | nil => rfl
  | cons x h ih => simp only [rect_cons_eq,ih]
  | swap x y v =>
    have swapAcc := rect_acc_perm d l o v (List.Perm.swap (flag d l o x) (flag d l o y) m)
    simp only [rect_cons_eq,hits_cons_eq]
    rw [swapAcc,hit_swap (flag d l o x) (flag d l o y)]
    simp only [Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
  | trans a b ha hb => exact (ha m).trans (hb m)
lemma moveHead {α : Type} (x : α) (a b : List α) : (a ++ x :: b).Perm (x :: (a ++ b)) := by
  induction a with
  | nil => exact List.Perm.refl _
  | cons w v ih => exact (ih.cons w).trans (List.Perm.swap _ _ _)
lemma rawFirst_perm (v : List W) : (rawFirst v).Perm v := by
  induction v with
  | nil => exact List.Perm.nil
  | cons w v ih =>
    cases hw : w.r == 0 with
    | false => simpa [rawFirst,List.filter_cons,hw] using ih.cons w
    | true => simpa [rawFirst,List.filter_cons,hw] using
        (moveHead w (v.filter (fun w => !(w.r == 0))) (v.filter (fun w => w.r == 0))).trans (ih.cons w)

end PEqualNP.Outside.L_meta_8399
