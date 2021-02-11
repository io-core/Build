(* begin-module-use-description  vim:fdm=marker fmr=(*%,%*) fdl=0 fen 
Module OXG generates the processor-specific instructions for executing an Oberon program.

end-module-use-description *)
(* begin-module-develop-description
Module OXG implements the processor-specific backends used by ORG

(C.Perkins 2020)

**OXG** is called from ORP and generates machine code various Oberon language constructs for the Oberon RISC5 architeture.

end-module-develop-description *)
MODULE OXG; (* C.Perkis 2020*)
  IMPORT SYSTEM, Files, ORS, ORB;

  
  CONST     (*% *)
    WordSize* = 4;
    RStkOrg0 = -64;
    IStkOrg0 = -64;
    AStkOrg0 = -64;
    aStkOrg0 = -64;
    VStkOrg0 = -64;
    vStkOrg0 = -64;
    MT = 12; SP = 14; LNK = 15;   (*dedicated registers*)
    maxCode = 8000; maxStrx = 6400; maxTD = 160; C24 = 1000000H;
    Reg = 10; RegI = 11; Cond = 12;  (*internal item modes*)

    (*frequently used opcodes*)  U = 2000H; V = 1000H;
    Mov = 0; Lsl = 1; Asr = 2; Ror= 3; And = 4; Ann = 5; Ior = 6; Xor = 7;
    Add = 8; Sub = 9; Cmp = 9; Mul = 10; Div = 11;
    Fad = 12; Fsb = 13; Fml = 14; Fdv = 15; MovU = 16;
    Ldr = 8; Ldb = 9; Str = 10; Stb = 11;
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;
    BMI =  0; BEQ =  1; BCS =  2; BVS =  3; 
    BLS =  4; BLT =  5; BLE =  6; B   =  7;
    BPL =  8; BNE =  9; BVC = 10; BCC = 11;
    BHI = 12; BGE = 13; BGT = 14; BNO = 15;
    (* %*)



  TYPE      (*% *)
    (* %*)

  VAR       (*% *)
    code*: ARRAY maxCode OF LONGINT;
    data*: ARRAY maxTD OF LONGINT;  (*type descriptors*)
    str*: ARRAY maxStrx OF CHAR;
    fixorgP*, fixorgD*, fixorgT*: LONGINT;   (*origins of lists of locations to be fixed up by loader*)
    err: ARRAY 32 OF CHAR;
    regmap: ARRAY 16 OF INTEGER; (*shuffle of registers for allocation/use*)
    it0: ARRAY 16 OF INTEGER;
    it1: ARRAY 16 OF INTEGER;
    it2: ARRAY 4 OF INTEGER;
    it3: ARRAY 16 OF INTEGER;
    (* %*)

  (*%S ## --------- Fixup Chains Updating *)

  PROCEDURE setFixOrgP*(v: LONGINT);  (*%P *)
  (* begin-procedure-description
---
**setFixOrgP**
  end-procedure-description *)
  BEGIN 
    fixorgP := v
  END setFixOrgP;                     (* P%*)

  PROCEDURE setFixOrgD*(v: LONGINT);  (*%P *)
  (* begin-procedure-description
---
**setFixOrgD**
  end-procedure-description *)
  BEGIN 
    fixorgD := v
  END setFixOrgD;                     (* P%*)

  PROCEDURE setFixOrgT*(v: LONGINT);  (*%P *)
  (* begin-procedure-description
---
**setFixOrgT**
  end-procedure-description *)
  BEGIN 
    fixorgT := v
  END setFixOrgT;                     (* P%*)

  (* S%*)

  (* begin-section-description
## ---------- Utility Operations
  end-section-description *)

  (* begin-procedure-description
---
**Put1Byte** places a byte in in the instruction stream which is expected to have 8 zero bits at that location.
  end-procedure-description *)
  PROCEDURE Put1Byte(a: INTEGER; VAR pc, pcb: INTEGER);
    VAR b: ARRAY 4 OF INTEGER;
  BEGIN
    b[0]:=code[pc] MOD 100H; b[1]:= code[pc] DIV 100H MOD 100H; b[2]:= code[pc] DIV 10000H MOD 100H; b[3]:= code[pc] DIV 1000000H MOD 100H;
    b[pcb]:=ORD(a); code[pc]:=b[0]+b[1]*100H+b[2]*10000H+b[3]*1000000H;
    INC(pcb); IF pcb > 3 THEN pcb :=0; INC(pc) END
  END Put1Byte;

  (* begin-procedure-description
---
**Put2Bytes** places two bytes in in the instruction stream.
  end-procedure-description *)
  PROCEDURE Put2Bytes(a, b: INTEGER; VAR pc, pcb: INTEGER);
  BEGIN
    Put1Byte(a,pc,pcb);
    Put1Byte(b,pc,pcb);
  END Put2Bytes;

  (* begin-procedure-description
---
**Put3Bytes** places three bytes in in the instruction stream.
  end-procedure-description *)
  PROCEDURE Put3Bytes(a, b, c: INTEGER; VAR pc, pcb: INTEGER);
  BEGIN
    Put1Byte(a,pc,pcb);
    Put1Byte(b,pc,pcb);
    Put1Byte(c,pc,pcb);
  END Put3Bytes;

  (* begin-procedure-description
---
**Put4Bytes** places four bytes in in the instruction stream.
  end-procedure-description *)
  PROCEDURE Put4Bytes(a, b, c, d: INTEGER; VAR pc, pcb: INTEGER);
  BEGIN
    Put1Byte(a,pc,pcb);
    Put1Byte(b,pc,pcb);
    Put1Byte(c,pc,pcb);
    Put1Byte(d,pc,pcb);
  END Put4Bytes;

  (* begin-procedure-description
---
**Put4Integer** places an integer as 4 bytes in in the instruction stream.
  end-procedure-description *)
  PROCEDURE Put4Integer(i: INTEGER; VAR pc, pcb: INTEGER);
  BEGIN
    Put1Byte(i MOD 100H,pc,pcb);
    Put1Byte(i DIV 100H MOD 100H,pc,pcb);
    Put1Byte(i DIV 10000H MOD 100H,pc,pcb);
    Put1Byte(i DIV 1000000H MOD 100H,pc,pcb);
  END Put4Integer;




  (* begin-section-description
## ---------- RISC5 instruction generation
  end-section-description *)

(* begin-procedure-description
---
**RPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE RPut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
      code[pc] := ((a*10H + b) * 10H + op) * 10000H + c;
    INC(pc);
  END RPut0;

  (* begin-procedure-description
---
**RPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE RPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*emit format-1 instruction,  -10000H <= im < 10000H*)
    IF op = MovU THEN   (*  U = 2000H; V = 1000H; *)
      IF im < 0 THEN
        code[pc] := (((a+70H) * 10H + b) * 10H ) * 10000H + (im MOD 10000H)
      ELSE
        code[pc] := (((a+60H) * 10H + b) * 10H ) * 10000H + (im MOD 10000H)
      END;
    ELSE
      IF im < 0 THEN INC(op, V) END ;
      code[pc] := (((a+40H) * 10H + b) * 10H + op) * 10000H + (im MOD 10000H);
    END;   
    INC(pc);
 
  END RPut1;

  (* begin-procedure-description
---
**RPut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE RPut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as RPut1, but with range test  -10000H <= im < 10000H*)
    IF (im >= -10000H) & (im <= 0FFFFH) THEN RPut1(o, pc, pcb, op, a, b, im);
    ELSE RPut1(o, pc, pcb, Mov+U, RH, 0, im DIV 10000H);
      IF im MOD 10000H # 0 THEN RPut1(o, pc, pcb, Ior, RH, RH, im MOD 10000H) END ;
      RPut0(pc, pcb, op, a, b, RH);
    END

  END RPut1a;

  (* begin-procedure-description
---
**RPut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE RPut2*(VAR pc, pcb: LONGINT; op, a, b, off: LONGINT);
  BEGIN (*emit load/store instruction*)
    code[pc] := ((op * 10H + a) * 10H + b) * 100000H + (off MOD 100000H); INC(pc);
  END RPut2;


  (* begin-procedure-description
---
**RPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE RPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
  BEGIN (*emit branch instruction*)
    code[pc] := ((op+12) * 10H + cond) * 1000000H + (off MOD 1000000H); INC(pc);
  END RPut3;


  (* begin-procedure-description
---
**RHeader** prepares the code introductory sequence for a compiled module
  end-procedure-description *)
  PROCEDURE RHeader*(VAR pc, pcb, RH, entry, version: LONGINT);
  BEGIN entry := pc*4;
    IF version = 0 THEN code[0] := 0E7000000H-1 + pc;  RPut1a(120, pc, pcb, RH, Mov, SP, 0, RStkOrg0)  (*BAREMETAL*)
    ELSE RPut1(121, pc, pcb, Sub, SP, SP, 4); RPut2(pc, pcb, Str, LNK, SP, 0)
    END
  END RHeader;

  (* begin-section-description
## ---------- i64 instruction generation
  end-section-description *)


  (* begin-procedure-description
---
**ISetTables** maps registers between the RISC5 model machine and the x86_64 actual machine and prepares opcode tables for x86_64.
  end-procedure-description *)
  PROCEDURE ISetTables;
  BEGIN    (* RSP = SP, RBP = MT, RBX = LNK *)
      regmap[0]:=8; regmap[1]:=9; regmap[2]:=10; regmap[3]:=11; regmap[4]:=12; regmap[5]:=13; regmap[6]:=14; regmap[7]:=15;
      regmap[8]:=1; regmap[9]:=2; regmap[10]:=6; regmap[11]:=7; regmap[MT]:=5; regmap[13]:=0; regmap[SP]:=4; regmap[LNK]:=3;

      it0[Mov]:= 089C0H;  it0[Lsl]:= 0C1E0H;  it0[Asr]:= 0C1E8H;  it0[Ror]:= 0C1C8H; 
      it0[And]:= 021F8H;  it0[Ann]:= 021F8H;  it0[Ior]:= 009F8H;  it0[Xor]:= 031F8H;
      it0[Add]:= 001F8H;  it0[Sub]:= 029F8H;  it0[Mul]:= 0F7E0H;  it0[Div]:= 0F7F0H;
      it0[Fad]:= 0F7F0H;  it0[Fsb]:= 0F7F0H;  it0[Fml]:= 0F7F0H;  it0[Fdv]:= 0F7F0H;

      it1[Mov]:= 4C7C0H;  it1[Lsl]:= 1C1E0H;  it1[Asr]:= 1C1E8H;  it1[Ror]:= 1C1C8H; 
      it1[And]:= 481E0H;  it1[Ann]:= 40000H;  it1[Ior]:= 481C8H;  it1[Xor]:= 481F0H;
      it1[Add]:= 481C0H;  it1[Sub]:= 481E8H;  it1[Mul]:= 40000H;  it1[Div]:= 40000H;
      it1[Fad]:= 40000H;  it1[Fsb]:= 40000H;  it1[Fml]:= 40000H;  it1[Fdv]:= 40000H;

      it2[Ldr-8]:= 00000H;  it2[Ldb-8]:= 00000H;  it2[Str-8]:= 00000H;  it2[Stb-8]:= 00000H; 

      it3[BMI]:= 40000H;  it3[BEQ]:= 40000H;  it3[BCS]:= 40000H;  it3[BVS]:= 40000H; 
      it3[BLS]:= 40000H;  it3[BLT]:= 40000H;  it3[BLE]:= 40000H;  it3[B  ]:= 40000H;
      it3[BPL]:= 40000H;  it3[BNE]:= 40000H;  it3[BVC]:= 40000H;  it3[BCC]:= 40000H;
      it3[BHI]:= 40000H;  it3[BGE]:= 40000H;  it3[BGT]:= 40000H;  it3[BNO]:= 40000H;

  END ISetTables;


(* begin-procedure-description
---
**IPut0** places a register <= Register Operation Register instruction in the code array.

When the destination register (ai) is not the same as the first operand register (bi) 
the AX register is used as an intermediate register.

  end-procedure-description *)
  PROCEDURE IPut0*(VAR pc, pcb: LONGINT; op, ai, bi, ci: LONGINT);
    VAR a,b,a0,a1,b1,c,t:INTEGER;
  BEGIN (*emit format-0 instruction*)
    a:=regmap[ai]; b:=regmap[bi]; c:=regmap[ci];

    a1:=a MOD 8; a0:=48H; IF a > 8 THEN a0 := 49H END;
    IF a # b THEN
      b1:=b MOD 8; IF b > 8 THEN a0 := a0 + 2 END;
      Put3Bytes( a0, 89H, 0C0H+(b1*8H)+a1, pc, pcb);  (* MOV ai <= bi *)
      a0:=48H; IF a > 8 THEN a0 := 49H END;
    END;

    b1:=c MOD 8; IF c > 8 THEN a0 := a0 + 2 END;

    IF op < 16 THEN
      Put3Bytes( a0, it0[op] DIV 100H MOD 100H, (it0[op] MOD 100H) + (b1*8H)+a1, pc, pcb )
    ELSE
      Put1Byte( 90H, pc, pcb)
    END

  END IPut0;

  (* begin-procedure-description
---
**IPut1** places a register <= Register Operation Immediate instruction in the code array.

When the destination register (ai) is not the same as the first operand register (bi)
the AX register is used as an intermediate register.

The immediate value may be up to 32-bits in size.

If the 'U' bit is set and the operation is a move, the value is shifted left 32-bits.

  end-procedure-description *)
  PROCEDURE IPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, ai, bi, im: LONGINT);
    VAR a,b,a0,a1,b0,b1,osz:INTEGER;
  BEGIN (*emit format-1 instruction,  -10000H <= im < 10000H*)
    a:=regmap[ai];b:=regmap[bi];

    a1:=a MOD 8; a0:=48H; IF a > 8 THEN a0 := 49H END;
    IF a # b THEN
      b1:=b MOD 8; IF b > 8 THEN a0 := a0 + 2 END;
      Put3Bytes( a0, 89H, 0C0H+(b1*8H)+a1, pc, pcb);  (* MOV ai <= bi *)
      a0:=48H; IF a > 8 THEN a0 := 49H END;
    END;

    osz:=4;
    a1:=a MOD 8; a0:=48H; IF a > 8 THEN a0 := 49H END;

    IF op < 16 THEN
      Put3Bytes( a0, it1[op] DIV 100H MOD 100H, (it1[op] MOD 100H) + a1, pc, pcb ); osz := it1[op] DIV 10000H
    ELSE
      Put1Byte( 90H, pc, pcb)
    END;

    IF osz = 4 THEN
      Put4Integer( im, pc, pcb )
    ELSE
      Put1Byte( im, pc, pcb )
    END

  END IPut1;



  (* begin-procedure-description
---
**IPut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE IPut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as RPut1, but with range test  -10000H <= im < 10000H*)
    IF (im >= -10000H) & (im <= 0FFFFH) THEN IPut1(o, pc, pcb, op, a, b, im);
    ELSE IPut1(o, pc, pcb, Mov+U, RH, 0, im DIV 10000H);
      IF im MOD 10000H # 0 THEN IPut1(o, pc, pcb, Ior, RH, RH, im MOD 10000H) END ;
      IPut0(pc, pcb, op, a, b, RH);
    END

  END IPut1a;



  (* begin-procedure-description
---
**IPut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE IPut2*(VAR pc, pcb: LONGINT; op, ai, bi, off: LONGINT);
    VAR a,b,a0,a1,b0,b1:INTEGER;
  BEGIN (*emit load/store instruction*)
    a:=regmap[ai];b:=regmap[bi];
    a1:=a MOD 8; a0:=48H; IF a > 8 THEN a0 := 49H END;
    IF op = Ldr THEN
      Put3Bytes( a0, 8BH, 80H + a1, pc, pcb ); Put4Integer( off, pc, pcb )
    ELSIF op = Str THEN
      Put3Bytes( a0, 89H, 80H + a1, pc, pcb ); Put4Integer( off, pc, pcb )
    ELSE
     Put3Bytes( 090H, 090H, 090H, pc, pcb )
    END
  END IPut2;



  (* begin-procedure-description
---
**IPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE IPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
    VAR opc,osz,disp: INTEGER;
  BEGIN (*emit branch instruction*)
(*
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;
*)
(*
    disp:=(off * 4) - 4;
    IF    op = BR  THEN (*via register*)
      IF (off = 15) THEN
        Put1Byte( 0C3H, pc, pcb); osz:=0
      ELSE
        opc:=0E9H; osz:=4
      END
    ELSIF op = BLR THEN (*via register and depositing link*)
        Put1Byte( 090H, pc, pcb); osz:=0
    ELSIF op = BC  THEN (*via offset from pc*)

      IF    (cond = 7)  THEN
                       IF (disp < -127) OR (disp > 127) THEN opc:=0E9H; osz:=4  ELSE opc:= 090H; osz:=1 END;
      ELSIF (cond = EQ) THEN
                        IF (disp < -127) OR (disp > 127) THEN opc:=074H; osz:=4  ELSE opc:= 084H; osz:=1 END;
      ELSIF (cond = NE) THEN
                        IF (disp < -127) OR (disp > 127) THEN opc:=075H; osz:=4  ELSE opc:= 085H; osz:=1 END;
      ELSIF (cond = GT) THEN
                        IF (disp < -127) OR (disp > 127) THEN opc:=07FH; osz:=4  ELSE opc:= 08FH; osz:=1 END;
      ELSIF (cond = GE) THEN
                        IF (disp < -127) OR (disp > 127) THEN opc:=07DH; osz:=4  ELSE opc:= 08DH; osz:=1 END;
      ELSIF (cond = LT) THEN
                        IF (disp < -127) OR (disp > 127) THEN opc:=06CH; osz:=4  ELSE opc:= 07CH; osz:=1 END;
      ELSIF (cond = LE) THEN
                        IF (disp < -127) OR (disp > 127) THEN opc:=07EH; osz:=4  ELSE opc:= 08EH; osz:=1 END;
      ELSE opc:=90H; disp:=90H; osz:=1
      END;

    ELSIF op = BL  THEN (*via offset from pc and depositing link -- convert to jsr *)
      opc:=0E8H; osz:=4
    END;


    IF osz = 4 THEN
        Put1Byte( opc, pc, pcb); Put4Integer( disp, pc, pcb)
    ELSIF osz = 1 THEN
        Put1Byte( opc, pc, pcb); Put1Byte( disp, pc, pcb)
    END
*)
  END IPut3;


  (* begin-procedure-description
---
**IHeader** prepares the code introductory sequence for a compiled X8664 module
  end-procedure-description *)
  PROCEDURE IHeader*(VAR pc, pcb, RH, entry, version: LONGINT);
  BEGIN entry := pc*4;
    IF version = 0 THEN
      code[0] := 0E9H + ((entry - 3) * 100H); code[1] := 90909000H; (* 32-bit pc-relative jump *)
      IPut1(121, pc, pcb, Sub, SP, SP, 8); IPut2(pc, pcb, Str, LNK, SP, 0) 
    ELSE 
      IPut1(121, pc, pcb, Sub, SP, SP, 8); IPut2(pc, pcb, Str, LNK, SP, 0)
    END
  END IHeader;

  (* begin-section-description
## ---------- ARM64 instruction generation
  end-section-description *)


  (* begin-procedure-description
---
**ASetTables** maps registers between the RISC5 model machine and the aarch64 actual machine and prepares opcode tables for aarch64.
  end-procedure-description *)
  PROCEDURE ASetTables;
    VAR i: INTEGER;
  BEGIN

      regmap[MT]:=29; regmap[13]:=13; regmap[SP]:=31; regmap[LNK]:=30;

      it0[Mov]:= 0AA000000H;  it0[Lsl]:=         0H;  it0[Asr]:=         0H;  it0[Ror]:=         0H; 
      it0[And]:=         0H;  it0[Ann]:=         0H;  it0[Ior]:=         0H;  it0[Xor]:=         0H;
      it0[Add]:= 0AB000000H;  it0[Sub]:= 0EB000000H;  it0[Mul]:=         0H;  it0[Div]:=         0H;
      it0[Fad]:=         0H;  it0[Fsb]:=         0H;  it0[Fml]:=         0H;  it0[Fdv]:=         0H;

      it1[Mov]:= 0D2000000H;  it1[Lsl]:=         0H;  it1[Asr]:=         0H;  it1[Ror]:=         0H; 
      it1[And]:=         0H;  it1[Ann]:=         0H;  it1[Ior]:=         0H;  it1[Xor]:=         0H;
      it1[Add]:= 091000000H;  it1[Sub]:= 0D1000000H;  it1[Mul]:=         0H;  it1[Div]:=         0H;
      it1[Fad]:=         0H;  it1[Fsb]:=         0H;  it1[Fml]:=         0H;  it1[Fdv]:=         0H;

      it2[Ldr-8]:=     00000H;  it2[Ldb-8]:=     00000H;  it2[Str-8]:=     00000H;  it2[Stb-8]:=     00000H; 

      it3[BMI]:=     40000H;  it3[BEQ]:=     40000H;  it3[BCS]:=     40000H;      it3[BVS]:= 40000H; 
      it3[BLS]:=     40000H;  it3[BLT]:=     40000H;  it3[BLE]:=     40000H;      it3[B  ]:= 40000H;
      it3[BPL]:=     40000H;  it3[BNE]:=     40000H;  it3[BVC]:=     40000H;      it3[BCC]:= 40000H;
      it3[BHI]:=     40000H;  it3[BGE]:=     40000H;  it3[BGT]:=     40000H;      it3[BNO]:= 40000H;

  END ASetTables;


(* begin-procedure-description
---
**APut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE APut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
    IF   op = Mov THEN 
      IF a = SP THEN
        code[pc] := 9100001FH + (regmap[c] * 20H)
      ELSIF c = SP THEN
        code[pc] := 910003E0H + regmap[a] 
      ELSE
        code[pc] := it0[op] + (regmap[c] * 10000H) + (1FH * 20H) + regmap[a]
      END
    ELSIF op < 16 THEN
      code[pc] := it0[op] + (regmap[c] * 10000H) + (regmap[b] * 20H) + regmap[a]
    ELSE
      code[pc] := -1
    END;
    INC(pc)
  END APut0;

  (* begin-procedure-description
---
**APut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE APut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*emit format-1 instruction,  -10000H <= im < 10000H*)
    IF   op = Mov THEN 
      code[pc] := (1A5H * 800000H) + (im * 20H) + regmap[a]
    ELSIF op < 16 THEN
      code[pc] := it1[op] + (im * 400H) + (regmap[b] * 20H) + regmap[a]
    ELSE
      code[pc] := -1
    END;
    INC(pc)
  END APut1;

  (* begin-procedure-description
---
**APut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE APut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as RPut1, but with range test  -100H <= im < 100H*)
    IF (im >= -100H) & (im <= 0FFH) THEN APut1(o, pc, pcb, op, a, b, im);
    ELSE 
      code[pc]:= 0D2800000H + regmap[a]  +  (im MOD 10000H * 20H) ; INC(pc);     (* movw opcode *)
      code[pc]:= 0F2A00000H + regmap[a]  +  (im DIV 10000H MOD 10000H * 20H) ; INC(pc);    (* movt opcode *)
(* need to handle 64-bit and negative values.
      code[pc]:= 0F2C00000H + regmap[a]  +  (im DIV 100000000H MOD 10000H) ; INC(pc);    (* movt opcode *)
      code[pc]:= 0F2E00000H + regmap[a]  +  (im DIV 1000000000000H MOD 10000H) ; INC(pc);    (* movt opcode *)
*)
      IF op MOD 16 # 0 THEN
        APut0(pc, pcb, op, a, b, a)
      END
    END
  END APut1a;

  (* begin-procedure-description
---
**APut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE APut2*(VAR pc, pcb: LONGINT; op, ai, bi, off: LONGINT);
    VAR a,b:INTEGER;
  BEGIN (*emit load/store instruction*)
    a:=regmap[ai];b:=regmap[bi];
    IF op = Ldr THEN
      code[pc]:= 0F8400000H + ((off MOD 200H) * 1000H) + (b * 20H) + a
    ELSIF op = Str THEN
      code[pc]:= 0F8000000H + ((off MOD 200H) * 1000H) + (b * 20H) + a
    ELSE
      code[pc]:=0
    END;
    INC(pc)
  END APut2;

  (* begin-procedure-description
---
**APut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE APut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
    VAR opc,osz,disp: INTEGER;
  BEGIN (*emit branch instruction*)
(*
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;
*)
    disp:=off;
    IF    op = BR  THEN (*via register*)
      IF off = 15 THEN
        code[pc]:= 0D65F03C0H; INC(pc) (* substitute ret *)
      ELSE
        code[pc]:= 0D61FH * 10000H + (regmap[off] * 20H); INC(pc)
      END
    ELSIF op = BLR THEN (*via register and depositing link*)
      code[pc]:= 0D63FH * 10000H + (regmap[off] * 20H); INC(pc)

    ELSIF op = BC  THEN (*via offset from pc*)
      code[pc]:=14000000H + ((off+1 ) MOD 4000000H); INC(pc)
    ELSIF op = BL  THEN (*via offset from pc and depositing link*)
      code[pc]:=94000000H + ((off+1 ) MOD 4000000H); INC(pc)
    END;
END APut3;

  (* begin-procedure-description
---
**AHeader** prepares the code introductory sequence for a compiled module
  end-procedure-description *)
  PROCEDURE AHeader*(VAR pc, pcb, RH, entry, version: LONGINT);
  BEGIN entry := pc*4;
    IF version = 0 THEN 
      code[0] := (14H * 1000000H) + (entry DIV 4); (* 24-bit pc-relative jump *)
(*      APut1(121, pc, pcb, Sub, SP, SP, 16); APut2(pc, pcb, Str, LNK, SP, 0)  *)
    ELSE 
      APut1(121, pc, pcb, Sub, SP, SP, 16); APut2(pc, pcb, Str, LNK, SP, 0)
    END
  END AHeader;


  (* begin-section-description
## ---------- ARM32 instruction generation
  end-section-description *)


  (* begin-procedure-description
---
**aSetTables** maps registers between the RISC5 model machine and the arm actual machine and prepares opcode tables for arm 32-bit.
  end-procedure-description *)
  PROCEDURE aSetTables;
  BEGIN
      regmap[MT]:=12; regmap[SP]:=13; regmap[LNK]:=14;

      it0[Mov]:= 0E1A00000H;  it0[Lsl]:= 0E1A00100H;  it0[Asr]:= 0E1A00000H;  it0[Ror]:= 0E1A00000H; 
      it0[And]:= 0E0000000H;  it0[Ann]:=         0H;  it0[Ior]:=         0H;  it0[Xor]:= 0E0200000H;
      it0[Add]:= 0E0800000H;  it0[Sub]:= 0E0400000H;  it0[Mul]:=         0H;  it0[Div]:=         0H;
      it0[Fad]:=         0H;  it0[Fsb]:=         0H;  it0[Fml]:=         0H;  it0[Fdv]:=         0H;

      it1[Mov]:= 0E3A00000H;  it1[Lsl]:=         0H;  it1[Asr]:=         0H;  it1[Ror]:=         0H; 
      it1[And]:= 0E2000000H;  it1[Ann]:=         0H;  it1[Ior]:= 0E3800000H;  it1[Xor]:= 0E2200000H;
      it1[Add]:= 0E2800000H;  it1[Sub]:= 0E2400000H;  it1[Mul]:=         0H;  it1[Div]:=         0H;
      it1[Fad]:=         0H;  it1[Fsb]:=         0H;  it1[Fml]:=         0H;  it1[Fdv]:=         0H;

      it2[Ldr-8]:=     00000H;  it2[Ldb-8]:=     00000H;  it2[Str-8]:=     00000H;  it2[Stb-8]:=     00000H; 

      it3[BMI]:=     40000H;  it3[BEQ]:=     40000H;  it3[BCS]:=     40000H;  it3[BVS]:=     40000H; 
      it3[BLS]:=     40000H;  it3[BLT]:=     40000H;  it3[BLE]:=     40000H;  it3[B  ]:= 0EA000000H;
      it3[BPL]:=     40000H;  it3[BNE]:=     40000H;  it3[BVC]:=     40000H;  it3[BCC]:=     40000H;
      it3[BHI]:=     40000H;  it3[BGE]:=     40000H;  it3[BGT]:=     40000H;  it3[BNO]:=     40000H;
  END aSetTables;
(*
(* begin-procedure-description
---
**aUMT** convert an integer to mov m/t immediate format
  end-procedure-description *)
  PROCEDURE aUMT( i : LONGINT ): LONGINT;
    VAR c,d:LONGINT;
  BEGIN
        c := (i DIV 1000H MOD 8) * 10000H;
        d := (i MOD 1000H);
  RETURN c + d
  END aUMT;
*)

(* begin-procedure-description
---
**aPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE aPut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
    IF op < 16 THEN code[pc]:= it0[op] + (regmap[a] * 10000H) + (regmap[b] * 1000H) + regmap[c] ; INC(pc) 
    ELSE code[pc]:=-1; INC(pc)
    END;
  END aPut0;


  (* begin-procedure-description
---
**aPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE aPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*emit format-1 instruction,  -100H <= im < 100H*)
    IF op = 0 THEN
      code[pc]:= 0E3000000H + (regmap[a] * 1000H) + (im  DIV 1000H MOD 8) * 10000H + im MOD 1000H ; INC(pc);     (* movw opcode *)
    ELSIF op < 16 THEN
      IF im < 0 THEN (* mvn then reg op *)
        code[pc]:= 0E3E00000H + (regmap[b] * 10000H) + (regmap[a] * 1000H) (* + (s * 100H) *) + ((0-im) MOD 100H); INC(pc);
        IF op # Mov THEN
          aPut0(pc, pcb, op, a, b, a)
        END
      ELSE 
        code[pc]:= it1[op] + (regmap[b] * 10000H) + (regmap[a] * 1000H) (* + (s * 100H) *) + (im MOD 100H); INC(pc)
      END
    ELSE (* op modifier bit set *)
      IF op MOD 16 = 0 THEN (* move to top 16 bits *)
        code[pc]:= 0E3400000H + (im DIV 1000H MOD 10H * 10000H) + (regmap[a] * 1000H) + (im MOD 1000H); INC(pc);    (* movt opcode *)
      ELSE 
        code[pc]:=-1; INC(pc)
      END
    END;
    
  END aPut1;

  (* begin-procedure-description
---
**aPut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE aPut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as RPut1, but with range test  -100H <= im < 100H*)
    IF (im >= -100H) & (im <= 0FFH) THEN aPut1(o, pc, pcb, op, a, b, im);
    ELSE 
      code[pc]:= 0E3000000H + (regmap[a] * 1000H) + (im DIV 1000H MOD 10H) * 10000H + im MOD 1000H ; INC(pc);     (* movw opcode *)
      code[pc]:= 0E3400000H + (regmap[a] * 1000H) + (im DIV 10000000H MOD 10H) * 10000H + (im DIV 10000H MOD 1000H) ; INC(pc);    (* movt opcode *)
      IF op MOD 16 # 0 THEN
        aPut0(pc, pcb, op, a, b, a)
      END
    END

  END aPut1a;

  (* begin-procedure-description
---
**aPut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE aPut2*(VAR pc, pcb: LONGINT; op, ai, bi, off: LONGINT);
    VAR a,b:INTEGER;
  BEGIN (*emit load/store instruction*)
    a:=regmap[ai];b:=regmap[bi];
    IF op = Ldr THEN
      code[pc]:= 0E5900000H + (off MOD 1000H)  + (b * 10000H) + (a * 1000H)
    ELSIF op = Str THEN
      code[pc]:= 0E5800000H + (off MOD 1000H)  + (b * 10000H) + (a * 1000H)
    ELSE
      code[pc]:=0
    END;
    INC(pc)
  END aPut2;

  (* begin-procedure-description
---
**aPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE aPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
    VAR opc,osz,disp: INTEGER;
  BEGIN (*emit branch instruction*)
(*
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;
*)
    disp:=off;
    IF disp < 0 THEN INC(disp,-1) END;
    IF    op = BR  THEN (*via register*)
      code[pc]:= 0E12FFF10H + regmap[off] ; INC(pc)
    ELSIF op = BLR THEN (*via register and depositing link*)
      code[pc]:= 0E12FFF30H + regmap[off] ; INC(pc)
    ELSIF op = BC  THEN (*via offset from pc*)
      code[pc]:= it3[cond] + (disp MOD 1000000H); INC(pc)
    ELSIF op = BL  THEN (*via offset from pc and depositing link*)
      code[pc]:= it3[cond] + 1000000H + (disp MOD 1000000H); INC(pc)
    END;
END aPut3;

  (* begin-procedure-description
---
**aHeader** prepares the code introductory sequence for a compiled module
  end-procedure-description *)
  PROCEDURE aHeader*(VAR pc, pcb, RH, entry, version: LONGINT);
  BEGIN entry := pc*4;
    IF version = 0 THEN 
      code[0] := 0EAH * 1000000H  + (entry - 8) DIV 4 ; (* 24-bit pc-relative jump *)
      (* aPut1(121, pc, pcb, Mov+U, SP, SP, 07FFFH) *)
    ELSE 
      aPut1(121, pc, pcb, Sub, SP, SP, 4); aPut2(pc, pcb, Str, LNK, SP, 0)
    END
  END aHeader;



  (* begin-section-description
## ---------- RISCV64 instruction generation
  end-section-description *)



  (* begin-procedure-description
---
**VSetTables** maps registers between the RISC5 model machine and the rv64 actual machine and prepares opcode tables for riscv64.
  end-procedure-description *)
  PROCEDURE VSetTables;
    VAR i: INTEGER;
  BEGIN
      FOR i:= 0 TO 15 DO regmap[i]:=10+i END; regmap[MT]:=3; regmap[SP]:=2; regmap[LNK]:=1;

      it0[Mov]:=         0H;  it0[Lsl]:=      1033H;  it0[Asr]:=         0H;  it0[Ror]:=         0H; 
      it0[And]:=      7033H;  it0[Ann]:=         0H;  it0[Ior]:=      6033H;  it0[Xor]:=      4033H;
      it0[Add]:=      0033H;  it0[Sub]:=  40000033H;  it0[Mul]:=         0H;  it0[Div]:=         0H;
      it0[Fad]:=         0H;  it0[Fsb]:=         0H;  it0[Fml]:=         0H;  it0[Fdv]:=         0H;

      it1[Mov]:=         0H;  it1[Lsl]:=      1013H;  it1[Asr]:=         0H;  it1[Ror]:=         0H; 
      it1[And]:=      7013H;  it1[Ann]:=         0H;  it1[Ior]:=      6013H;  it1[Xor]:=      4013H;
      it1[Add]:=      0013H;  it1[Sub]:=      0013H;  it1[Mul]:=         0H;  it1[Div]:=         0H;
      it1[Fad]:=         0H;  it1[Fsb]:=         0H;  it1[Fml]:=         0H;  it1[Fdv]:=         0H;

      it2[Ldr-8]:=    2003H;  it2[Ldb-8]:=    0003H;  it2[Str-8]:=    2023H;  it2[Stb-8]:=    0023H; 

      it3[BMI]:=     00063H;  it3[BEQ]:=     00063H;  it3[BCS]:=     00063H;      it3[BVS]:= 00063H; 
      it3[BLS]:=     00063H;  it3[BLT]:=     00063H;  it3[BLE]:=     00063H;      it3[B  ]:= 00063H;
      it3[BPL]:=     00063H;  it3[BNE]:=     00063H;  it3[BVC]:=     00063H;      it3[BCC]:= 00063H;
      it3[BHI]:=     00063H;  it3[BGE]:=     00063H;  it3[BGT]:=     00063H;      it3[BNO]:= 00063H;

  END VSetTables;


(* begin-procedure-description
---
**vUJ** convert an integer to UJ immediate format
  end-procedure-description *)
  PROCEDURE vUJ( i : LONGINT ): LONGINT;
    VAR a,b,c,d:LONGINT;
  BEGIN
	a := (i DIV 100000H) * 40000H;
	b := (i DIV 2 MOD 200H) * 200H;
	c := (i DIV 800H MOD 2) * 100H;
	d := (i DIV 1000H MOD 100H);
  RETURN (a + b + c + d) * 1000H
  END vUJ;

(* begin-procedure-description
---
**VPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE VPut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
    IF op < 16 THEN
      code[pc]:= it0[op] + (regmap[a] * 80H) + (regmap[b] * 8000H) + (regmap[c] * 10000H) 
    ELSE 
      code[pc]:=0
    END;
    INC(pc)
  END VPut0;

  (* begin-procedure-description
---
**VPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE VPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*emit format-1 instruction,  -1000H <= im < 1000H*) (* smaller than RISC5! *)
    IF    op = Mov THEN
      code[pc]:= it1[Ior] + (regmap[a] * 80H) + (im * 100000H)
    ELSIF op = Sub THEN
      code[pc]:= it1[op] + (regmap[a] * 80H) + (regmap[b] * 8000H) + ((0-im) * 100000H)
    ELSIF op < 16  THEN
      code[pc]:= it1[op] + (regmap[a] * 80H) + (regmap[b] * 8000H) + (im * 100000H)
    ELSE
      code[pc]:=0
    END;
    INC(pc)
  END VPut1;

  (* begin-procedure-description
---
**VPut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE VPut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as RPut1, but with range test  -10000H <= im < 10000H*)
    IF (im >= -1000H) & (im <= 0FFFH) THEN VPut1(o, pc, pcb, op, a, b, im);
    ELSE 
      code[pc]:= 00000037H + (regmap[a] * 80H) + (im DIV 1000H * 1000H) ; INC(pc);    (* lui opcode *)
      IF (im MOD 1000H) # 0 THEN VPut1(o,pc,pcb,Ior,a,a,im MOD 1000H) END;
      IF op MOD 16 # 0 THEN
        VPut0(pc, pcb, op, a, b, a)
      END
    END

  END VPut1a;

  (* begin-procedure-description
---
**VPut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE VPut2*(VAR pc, pcb: LONGINT; op, a, b, off: LONGINT);
  BEGIN (*emit load/store instruction*)
    IF op < Str THEN
      code[pc] := it2[op-8] + ((regmap[a] MOD 20H) * 80H) + (regmap[b] * 8000H) + (off MOD 1000H * 100000H); INC(pc);
    ELSE 
      code[pc] := it2[op-8] + ((off MOD 20H) * 80H) + (regmap[b] * 8000H) + (regmap[a] * 100000H) + (off DIV 20H MOD 80H * 2000000H); INC(pc);
    END 
  END VPut2;

  (* begin-procedure-description
---
**VPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE VPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
    VAR opc,osz,disp: INTEGER;
  BEGIN (*emit branch instruction*)
(*
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;
*)
    disp:=off;
    IF    op = BR  THEN (*via register*)
      code[pc]:= 67H + (regmap[off] * 8000H) ; INC(pc)
    ELSIF op = BLR THEN (*via register and depositing link*)
      code[pc]:= 67H + (regmap[off] * 8000H) + (regmap[LNK] * 80H) ; INC(pc)
    ELSIF op = BC  THEN (*via offset from pc*)
      code[pc]:= 6FH + vUJ(off * 4 + 4)  ; INC(pc)
    ELSIF op = BL  THEN (*via offset from pc and depositing link*)
      code[pc]:= 6FH + vUJ(off * 4 + 4) + (regmap[LNK]*80H) ; INC(pc)
    END;
  END VPut3;

  (* begin-procedure-description
---
**VHeader** prepares the code introductory sequence for a compiled module
  end-procedure-description *)
  PROCEDURE VHeader*(VAR pc, pcb, RH, entry, version: LONGINT);
  BEGIN entry := pc*4;
    IF version = 0 THEN 
      code[0] := 6FH + vUJ(entry);
      (* VPut1(121, pc, pcb, Sub, SP, SP, 8);  VPut2(pc, pcb, Str, LNK, SP, 0) *)
    ELSE 
      VPut1(121, pc, pcb, Sub, SP, SP, 8); VPut2(pc, pcb, Str, LNK, SP, 0)
    END
  END VHeader;




  (* begin-section-description
## ---------- RISCV32 instruction generation
  end-section-description *)

  (* begin-procedure-description
---
**vSetTables** configures opcode tables for riscv32.
  end-procedure-description *)
  PROCEDURE vSetTables;
    VAR i: INTEGER;
  BEGIN
      FOR i:= 0 TO 15 DO regmap[i]:=10+i END; regmap[MT]:=3; regmap[SP]:=2; regmap[LNK]:=1;
  END vSetTables;                   


(* begin-procedure-description
---
**vPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE vPut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN VPut0(pc,pcb,op,a,b,c)
  END vPut0;

  (* begin-procedure-description
---
**vPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE vPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
  BEGIN VPut1(o,pc,pcb,op,a,b,im) 
  END vPut1;

  (* begin-procedure-description
---
**vPut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE vPut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN VPut1a(o,pc,pcb,RH,op,a,b,im)
  END vPut1a;

  (* begin-procedure-description
---
**vPut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE vPut2*(VAR pc, pcb: LONGINT; op, a, b, off: LONGINT);
  BEGIN VPut2(pc,pcb,op,a,b,off)
  END vPut2;

  (* begin-procedure-description
---
**vPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE vPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
  BEGIN VPut3(pc,pcb,op,cond,off)
  END vPut3;

  (* begin-procedure-description
---
**vHeader** prepares the code introductory sequence for a compiled module
  end-procedure-description *)
  PROCEDURE vHeader*(VAR pc, pcb, RH, entry, version: LONGINT);
  BEGIN entry := pc*4;
    IF version = 0 THEN
      code[0] := 6FH + vUJ(entry)  ;
      (* vPut1(121, pc, pcb, Sub, SP, SP, 4);  vPut2(pc, pcb, Str, LNK, SP, 0) *)
    ELSE
      vPut1(121, pc, pcb, Sub, SP, SP, 4); vPut2(pc, pcb, Str, LNK, SP, 0)
    END
  END vHeader;



  (* begin-procedure-description
---
**setRegMap**
  end-procedure-description *)
  PROCEDURE setRegMap*;               
    VAR i : INTEGER;
  BEGIN
    FOR i:= 0 TO 15 DO regmap[i]:=i END;  
    IF ORS.ccARCH = ORS.X8664 THEN ISetTables;
    ELSIF ORS.ccARCH = ORS.ARM64 THEN ASetTables;
    ELSIF ORS.ccARCH = ORS.ARM32 THEN aSetTables;
    ELSIF ORS.ccARCH = ORS.RISCV64 THEN VSetTables;
    ELSIF ORS.ccARCH = ORS.RISCV32 THEN vSetTables
    END
  END setRegMap;                     


  PROCEDURE fix*(at, with: LONGINT);
  BEGIN
    IF ORS.ccARCH = ORS.RISC5 THEN
       code[at] := code[at] DIV C24 * C24 + (with MOD C24);
    END
  END fix;

  PROCEDURE FixOne*(pc,pcb,at: LONGINT);
  BEGIN fix(at, pc-at-1)
  END FixOne;

  PROCEDURE FixLink*(pc,pcb,L: LONGINT);
    VAR L1: LONGINT;
  BEGIN
    IF ORS.ccARCH = ORS.RISC5 THEN
      WHILE L # 0 DO L1 := code[L] MOD 40000H; fix(L, pc-L-1); L := L1 END
    END
  END FixLink;

  PROCEDURE FixLinkWith*(L0, dst: LONGINT);
    VAR L1: LONGINT;
  BEGIN
    IF ORS.ccARCH = ORS.RISC5 THEN
      WHILE L0 # 0 DO
        L1 := code[L0] MOD C24;
        code[L0] := code[L0] DIV C24 * C24 + ((dst - L0 - 1) MOD C24); L0 := L1;
      END
    END
  END FixLinkWith;

  PROCEDURE merged*(L0, L1: LONGINT): LONGINT;
    VAR L2, L3: LONGINT;
  BEGIN
    IF ORS.ccARCH = ORS.RISC5 THEN
      IF L0 # 0 THEN L3 := L0;
        REPEAT L2 := L3; L3 := code[L2] MOD 40000H UNTIL L3 = 0;
        code[L2] := code[L2] + L1; L1 := L0;
      END ;
    END ;
    RETURN L1
  END merged;


  (* begin-procedure-description
---
**MakeStringItem** prepares
  end-procedure-description *)
  PROCEDURE InternString*(VAR strx: LONGINT; len: LONGINT); (*copies string from ORS-buffer to ORG-string array*)
    VAR i: LONGINT;
  BEGIN i := 0;
    IF strx + len + 4 < maxStrx THEN
      WHILE len > 0 DO str[strx] := ORS.str[i]; INC(strx); INC(i); DEC(len) END ;
      WHILE strx MOD 4 # 0 DO str[strx] := 0X; INC(strx) END
    ELSE ORS.Mark("too many strings")
    END
  END InternString;


  (* begin-procedure-description
---
**SetCode** prepares
  end-procedure-description *)
  PROCEDURE SetCode*(i,v: LONGINT);
  BEGIN code[i]:=v
  END SetCode;

  (* begin-procedure-description
---
**SetData** prepares
  end-procedure-description *)
  PROCEDURE SetData*(i,v: LONGINT);
  BEGIN data[i]:=v
  END SetData;


  (* begin-procedure-description
---
**NofPtrs** determines the number of Garbage Collection Roots.
  end-procedure-description *)
  PROCEDURE NofPtrs(typ: ORB.Type): LONGINT;
    VAR fld: ORB.Object; n: LONGINT;
  BEGIN
    IF (typ.form = ORB.Pointer) OR (typ.form = ORB.NilTyp) THEN n := 1
    ELSIF typ.form = ORB.Record THEN
      fld := typ.dsc; n := 0;
      WHILE fld # NIL DO n := NofPtrs(fld.type) + n; fld := fld.next END
    ELSIF typ.form = ORB.Array THEN n := NofPtrs(typ.base) * typ.len
    ELSE n := 0
    END ;
    RETURN n
  END NofPtrs;

  (* begin-procedure-description
---
**FindPtrs** locates Garbage Collection roots.
  end-procedure-description *)
  PROCEDURE FindPtrs(VAR R: Files.Rider; typ: ORB.Type; adr: LONGINT);
    VAR fld: ORB.Object; i, s: LONGINT;
  BEGIN
    IF (typ.form = ORB.Pointer) OR (typ.form = ORB.NilTyp) THEN Files.WriteInt(R, adr)
    ELSIF typ.form = ORB.Record THEN
      fld := typ.dsc;
      WHILE fld # NIL DO FindPtrs(R, fld.type, fld.val + adr); fld := fld.next END
    ELSIF typ.form = ORB.Array THEN
      s := typ.base.size;
      FOR i := 0 TO typ.len-1 DO FindPtrs(R, typ.base, i*s + adr) END
    END
  END FindPtrs;


  (* begin-procedure-description
---
**Close** writes the completed binary to disk.
  end-procedure-description *)
  PROCEDURE Close*(VAR pc, pcb: LONGINT; 
                   VAR modid: ORS.Ident; 
                   key, nofent, entry: LONGINT; 
                   version, varsize, tdx, strx: INTEGER);
    VAR obj: ORB.Object;
      i, comsize, nofimps, nofptrs, size: LONGINT;
      name: ORS.Ident;
      F: Files.File; R: Files.Rider;
  BEGIN  
    IF version = 0 THEN (* baremetal module exit code - branch to reset vector via register 0*)
      IF ORS.ccARCH = ORS.RISC5 THEN RPut1(3,  pc, pcb, Mov, 0, 0, 0); RPut3(pc, pcb, BR, 7, 0)   END;
      IF ORS.ccARCH = ORS.X8664 THEN IPut1(3,  pc, pcb, Mov, 0, 0, 0); IPut3(pc, pcb, BR, 7, 0)   END;
      IF ORS.ccARCH = ORS.ARM64 THEN APut1(3,  pc, pcb, Mov, 0, 0, 0); APut3(pc, pcb, BR, 7, 0)   END;
      IF ORS.ccARCH = ORS.ARM32 THEN aPut1(3,  pc, pcb, Mov, 0, 0, 0); aPut3(pc, pcb, BR, 7, 0)   END;
      IF ORS.ccARCH = ORS.RISCV64 THEN VPut1(3,  pc, pcb, Mov, 0, 0, 0); VPut3(pc, pcb, BR, 7, 0) END;
      IF ORS.ccARCH = ORS.RISCV32 THEN vPut1(3,  pc, pcb, Mov, 0, 0, 0); vPut3(pc, pcb, BR, 7, 0) END;
    ELSE (* regular module exit code *)
      IF ORS.ccARCH = ORS.RISC5 THEN RPut2(pc, pcb, Ldr, LNK, SP, 0); RPut1(4,  pc, pcb, Add, SP, SP, 4); RPut3(pc, pcb, BR, 7, LNK)   END;
      IF ORS.ccARCH = ORS.X8664 THEN IPut2(pc, pcb, Ldr, LNK, SP, 0); IPut1(4,  pc, pcb, Add, SP, SP, 4); IPut3(pc, pcb, BR, 7, LNK)   END;
      IF ORS.ccARCH = ORS.ARM64 THEN APut2(pc, pcb, Ldr, LNK, SP, 0); APut1(4,  pc, pcb, Add, SP, SP, 4); APut3(pc, pcb, BR, 7, LNK)   END;
      IF ORS.ccARCH = ORS.ARM32 THEN aPut2(pc, pcb, Ldr, LNK, SP, 0); aPut1(4,  pc, pcb, Add, SP, SP, 4); aPut3(pc, pcb, BR, 7, LNK)   END;
      IF ORS.ccARCH = ORS.RISCV64 THEN VPut2(pc, pcb, Ldr, LNK, SP, 0); VPut1(4,  pc, pcb, Add, SP, SP, 4); VPut3(pc, pcb, BR, 7, LNK) END;
      IF ORS.ccARCH = ORS.RISCV32 THEN vPut2(pc, pcb, Ldr, LNK, SP, 0); vPut1(4,  pc, pcb, Add, SP, SP, 4); vPut3(pc, pcb, BR, 7, LNK) END;
    END ;
(*
    IF version = 0 THEN (* Initial jump to entry point for baremetal module *)
      IF ORS.ccARCH = ORS.RISC5 THEN   END;
      IF ORS.ccARCH = ORS.X8664 THEN code[0] := 0E9H + ((entry -5) * 100H); code[1] := 90909000H  END; (* 32-bit pc-relative jump *)
      IF ORS.ccARCH = ORS.ARM64 THEN code[0] := (14H * 1000000H) + (entry DIV 4) END; (* 24-bit pc-relative jump *)
      IF ORS.ccARCH = ORS.ARM32 THEN code[0] := 0EAH * 1000000H  + (entry - 8) DIV 4 END; (* 24-bit pc-relative jump *)
      IF ORS.ccARCH = ORS.RISCV64 THEN code[0] := 6FH + (vUJ(entry) * 1000H) END;
      IF ORS.ccARCH = ORS.RISCV32 THEN code[0] := 6FH + (vUJ(entry) * 1000H) END;
    END;
*)
    obj := ORB.topScope.next; nofimps := 0; comsize := 4; nofptrs := 0;
    WHILE obj # NIL DO
      IF (obj.class = ORB.Mod) & (obj.dsc # ORB.system) THEN INC(nofimps) (*count imports*)
      ELSIF (obj.exno # 0) & (obj.class = ORB.Const) & (obj.type.form = ORB.Proc)
          & (obj.type.nofpar = 0) & (obj.type.base = ORB.noType) THEN i := 0; (*count commands*)
        WHILE obj.name[i] # 0X DO INC(i) END ;
        i := (i+4) DIV 4 * 4; INC(comsize, i+4)
      ELSIF obj.class = ORB.Var THEN INC(nofptrs, NofPtrs(obj.type))  (*count pointers*)
      END ;
      obj := obj.next
    END ;
    size := varsize + strx + comsize + (pc + nofimps + nofent + nofptrs + 1)*4;  (*varsize includes type descriptors*)
     
    IF ORS.ccARCH = ORS.RISC5 THEN ORB.MakeFileName(name, modid, ".rsc")   END;
    IF ORS.ccARCH = ORS.X8664 THEN ORB.MakeFileName(name, modid, ".i64")   END;
    IF ORS.ccARCH = ORS.ARM64 THEN ORB.MakeFileName(name, modid, ".a64")   END;
    IF ORS.ccARCH = ORS.ARM32 THEN ORB.MakeFileName(name, modid, ".a32")   END;
    IF ORS.ccARCH = ORS.RISCV64 THEN ORB.MakeFileName(name, modid, ".v64") END;
    IF ORS.ccARCH = ORS.RISCV32 THEN ORB.MakeFileName(name, modid, ".v32") END;

    F := Files.New(name); Files.Set(R, F, 0); 
    IF version = 1 THEN
      Files.WriteString(R, modid);
      Files.WriteInt(R, key);
      Files.Write(R, CHR(version));
      Files.WriteInt(R, size);
      obj := ORB.topScope.next;
      WHILE (obj # NIL) & (obj.class = ORB.Mod) DO  (*imports*)
        IF obj.dsc # ORB.system THEN Files.WriteString(R, obj(ORB.Module).orgname); Files.WriteInt(R, obj.val) END ;
        obj := obj.next
      END ;
      Files.Write(R, 0X);
      Files.WriteInt(R, tdx*4);
      i := 0;
      WHILE i < tdx DO Files.WriteInt(R, data[i]); INC(i) END ; (*type descriptors*)
      Files.WriteInt(R, varsize - tdx*4);  (*data*)
      Files.WriteInt(R, strx);
      FOR i := 0 TO strx-1 DO Files.Write(R, str[i]) END ;  (*strings*)
      Files.WriteInt(R, pc);  (*code len*)
    ELSE

      (* do the equivalent of the above for a binary Oberon-0 program *)

    END;

    FOR i := 0 TO pc-1 DO Files.WriteInt(R, code[i]) END ;  (*program*)
    obj := ORB.topScope.next;

    IF version = 1 THEN
      WHILE obj # NIL DO  (*commands*)
        IF (obj.exno # 0) & (obj.class = ORB.Const) & (obj.type.form = ORB.Proc) &
            (obj.type.nofpar = 0) & (obj.type.base = ORB.noType) THEN
          Files.WriteString(R, obj.name); Files.WriteInt(R, obj.val)
        END ;
        obj := obj.next
      END ;
      Files.Write(R, 0X);
      Files.WriteInt(R, nofent); Files.WriteInt(R, entry);
      obj := ORB.topScope.next;
      WHILE obj # NIL DO  (*entries*)
        IF obj.exno # 0 THEN
          IF (obj.class = ORB.Const) & (obj.type.form = ORB.Proc) OR (obj.class = ORB.Var) THEN
            Files.WriteInt(R, obj.val);
          ELSIF obj.class = ORB.Typ THEN
            IF obj.type.form = ORB.Record THEN Files.WriteInt(R,  obj.type.len MOD 10000H)
            ELSIF (obj.type.form = ORB.Pointer) & ((obj.type.base.typobj = NIL) OR (obj.type.base.typobj.exno = 0)) THEN
              Files.WriteInt(R,  obj.type.base.len MOD 10000H)
            END
          END
        END ;
        obj := obj.next
      END ;
      obj := ORB.topScope.next;
      WHILE obj # NIL DO  (*pointer variables*)
        IF obj.class = ORB.Var THEN FindPtrs(R, obj.type, obj.val) END ;
        obj := obj.next
      END ;
      Files.WriteInt(R, -1);
      Files.WriteInt(R, fixorgP); Files.WriteInt(R, fixorgD); Files.WriteInt(R, fixorgT); Files.WriteInt(R, entry);
      Files.Write(R, "O"); Files.Register(F)
    ELSE
    (* do the equivalent for a binary Oberon-0 program *)
      Files.Register(F)
    END
  END Close;



BEGIN
END OXG.

