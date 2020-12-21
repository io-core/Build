(* begin-module-use-description
Module OXG generates the processor-specific instructions for executing an Oberon program.

end-module-use-description *)
(* begin-module-develop-description

(C.Perkins 2020)

**ORG** is called from ORP and generates machine code various Oberon language constructs for the Oberon RISC5 architeture.

end-module-develop-description *)
MODULE OXG; (* C.Perkis 2020*)
  IMPORT SYSTEM, Files, ORS, ORB;

  CONST
    WordSize* = 4;
    StkOrg0 = -64; VarOrg0 = 0;  (*for RISC-0 only*)
    MT = 12; SP = 14; LNK = 15;   (*dedicated registers*)
    maxCode = 8000; maxStrx = 6400; maxTD = 160; C24 = 1000000H;
    Reg = 10; RegI = 11; Cond = 12;  (*internal item modes*)

  (*frequently used opcodes*)  U = 2000H; V = 1000H;
    Mov = 0; Lsl = 1; Asr = 2; Ror= 3; And = 4; Ann = 5; Ior = 6; Xor = 7;
    Add = 8; Sub = 9; Cmp = 9; Mul = 10; Div = 11;
    Fad = 12; Fsb = 13; Fml = 14; Fdv = 15; MovU = 16;
    Ldr = 8; Str = 10;
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;

  TYPE

  VAR
    code*: ARRAY maxCode OF LONGINT;
    data*: ARRAY maxTD OF LONGINT;  (*type descriptors*)
    str*: ARRAY maxStrx OF CHAR;
    fixorgP*, fixorgD*, fixorgT*: LONGINT;   (*origins of lists of locations to be fixed up by loader*)
    err: ARRAY 32 OF CHAR;



  (* begin-section-description
## ---------- Fixup Chains Updating
  end-section-description *)


  (* begin-procedure-description
---
**setFixOrgP**
  end-procedure-description *)
  PROCEDURE setFixOrgP*(v: LONGINT);
  BEGIN 
    fixorgP := v
  END setFixOrgP;

  (* begin-procedure-description
---
**setFixOrgD**
  end-procedure-description *)
  PROCEDURE setFixOrgD*(v: LONGINT);
  BEGIN 
    fixorgD := v
  END setFixOrgD;

  (* begin-procedure-description
---
**setFixOrgT**
  end-procedure-description *)
  PROCEDURE setFixOrgT*(v: LONGINT);
  BEGIN 
    fixorgT := v
  END setFixOrgT;




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


  (* begin-section-description
## ---------- X8664 instruction generation
  end-section-description *)

(* begin-procedure-description
---
**IPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE IPut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
      code[pc] := ((a*10H + b) * 10H + op) * 10000H + c;
    INC(pc);
  END IPut0;

  (* begin-procedure-description
---
**IPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE IPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
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
  PROCEDURE IPut2*(VAR pc, pcb: LONGINT; op, a, b, off: LONGINT);
  BEGIN (*emit load/store instruction*)
    code[pc] := ((op * 10H + a) * 10H + b) * 100000H + (off MOD 100000H); INC(pc);
  END IPut2;

  (* begin-procedure-description
---
**IPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE IPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
  BEGIN (*emit branch instruction*)
    code[pc] := ((op+12) * 10H + cond) * 1000000H + (off MOD 1000000H); INC(pc);
  END IPut3;



  (* begin-section-description
## ---------- ARM64 instruction generation
  end-section-description *)

(* begin-procedure-description
---
**APut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE APut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
      code[pc] := ((a*10H + b) * 10H + op) * 10000H + c;
    INC(pc);
  END APut0;

  (* begin-procedure-description
---
**APut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE APut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
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
 
  END APut1;

  (* begin-procedure-description
---
**APut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE APut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as RPut1, but with range test  -10000H <= im < 10000H*)
    IF (im >= -10000H) & (im <= 0FFFFH) THEN APut1(o, pc, pcb, op, a, b, im);
    ELSE APut1(o, pc, pcb, Mov+U, RH, 0, im DIV 10000H);
      IF im MOD 10000H # 0 THEN APut1(o, pc, pcb, Ior, RH, RH, im MOD 10000H) END ;
      APut0(pc, pcb, op, a, b, RH);
    END

  END APut1a;

  (* begin-procedure-description
---
**APut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE APut2*(VAR pc, pcb: LONGINT; op, a, b, off: LONGINT);
  BEGIN (*emit load/store instruction*)
    code[pc] := ((op * 10H + a) * 10H + b) * 100000H + (off MOD 100000H); INC(pc);
  END APut2;

  (* begin-procedure-description
---
**APut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE APut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
  BEGIN (*emit branch instruction*)
    code[pc] := ((op+12) * 10H + cond) * 1000000H + (off MOD 1000000H); INC(pc);
  END APut3;


  (* begin-section-description
## ---------- ARM32 instruction generation
  end-section-description *)

(* begin-procedure-description
---
**aPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE aPut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
      code[pc] := ((a*10H + b) * 10H + op) * 10000H + c;
    INC(pc);
  END aPut0;

  (* begin-procedure-description
---
**aPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE aPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
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
 
  END aPut1;

  (* begin-procedure-description
---
**aPut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE aPut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as RPut1, but with range test  -10000H <= im < 10000H*)
    IF (im >= -10000H) & (im <= 0FFFFH) THEN aPut1(o, pc, pcb, op, a, b, im);
    ELSE aPut1(o, pc, pcb, Mov+U, RH, 0, im DIV 10000H);
      IF im MOD 10000H # 0 THEN aPut1(o, pc, pcb, Ior, RH, RH, im MOD 10000H) END ;
      aPut0(pc, pcb, op, a, b, RH);
    END

  END aPut1a;

  (* begin-procedure-description
---
**aPut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE aPut2*(VAR pc, pcb: LONGINT; op, a, b, off: LONGINT);
  BEGIN (*emit load/store instruction*)
    code[pc] := ((op * 10H + a) * 10H + b) * 100000H + (off MOD 100000H); INC(pc);
  END aPut2;

  (* begin-procedure-description
---
**aPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE aPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
  BEGIN (*emit branch instruction*)
    code[pc] := ((op+12) * 10H + cond) * 1000000H + (off MOD 1000000H); INC(pc);
  END aPut3;



  (* begin-section-description
## ---------- RISCV64 instruction generation
  end-section-description *)

(* begin-procedure-description
---
**VPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE VPut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
      code[pc] := ((a*10H + b) * 10H + op) * 10000H + c;
    INC(pc);
  END VPut0;

  (* begin-procedure-description
---
**VPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE VPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
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
 
  END VPut1;

  (* begin-procedure-description
---
**VPut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE VPut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as RPut1, but with range test  -10000H <= im < 10000H*)
    IF (im >= -10000H) & (im <= 0FFFFH) THEN VPut1(o, pc, pcb, op, a, b, im);
    ELSE VPut1(o, pc, pcb, Mov+U, RH, 0, im DIV 10000H);
      IF im MOD 10000H # 0 THEN VPut1(o, pc, pcb, Ior, RH, RH, im MOD 10000H) END ;
      VPut0(pc, pcb, op, a, b, RH);
    END

  END VPut1a;

  (* begin-procedure-description
---
**VPut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE VPut2*(VAR pc, pcb: LONGINT; op, a, b, off: LONGINT);
  BEGIN (*emit load/store instruction*)
    code[pc] := ((op * 10H + a) * 10H + b) * 100000H + (off MOD 100000H); INC(pc);
  END VPut2;

  (* begin-procedure-description
---
**VPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE VPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
  BEGIN (*emit branch instruction*)
    code[pc] := ((op+12) * 10H + cond) * 1000000H + (off MOD 1000000H); INC(pc);
  END VPut3;




  (* begin-section-description
## ---------- RISCV32 instruction generation
  end-section-description *)

(* begin-procedure-description
---
**vPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE vPut0*(VAR pc, pcb: LONGINT; op, a, b, c: LONGINT);
  BEGIN (*emit format-0 instruction*)
      code[pc] := ((a*10H + b) * 10H + op) * 10000H + c;
    INC(pc);
  END vPut0;

  (* begin-procedure-description
---
**vPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE vPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, a, b, im: LONGINT);
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
 
  END vPut1;

  (* begin-procedure-description
---
**vPut1a** PutRegFromRegOpImmLargeViaRH
  end-procedure-description *)
  PROCEDURE vPut1a*(o: INTEGER; VAR pc, pcb, RH: LONGINT; op, a, b, im: LONGINT);
  BEGIN (*same as vPut1, but with range test  -10000H <= im < 10000H*)
    IF (im >= -10000H) & (im <= 0FFFFH) THEN vPut1(o, pc, pcb, op, a, b, im);
    ELSE vPut1(o, pc, pcb, Mov+U, RH, 0, im DIV 10000H);
      IF im MOD 10000H # 0 THEN vPut1(o, pc, pcb, Ior, RH, RH, im MOD 10000H) END ;
      vPut0(pc, pcb, op, a, b, RH);
    END

  END vPut1a;

  (* begin-procedure-description
---
**vPut2** PutRegLdStRegOffset
  end-procedure-description *)
  PROCEDURE vPut2*(VAR pc, pcb: LONGINT; op, a, b, off: LONGINT);
  BEGIN (*emit load/store instruction*)
    code[pc] := ((op * 10H + a) * 10H + b) * 100000H + (off MOD 100000H); INC(pc);
  END vPut2;

  (* begin-procedure-description
---
**vPut3** PutBrCondOffset
  end-procedure-description *)
  PROCEDURE vPut3*(VAR pc, pcb: LONGINT; op, cond, off: LONGINT);
  BEGIN (*emit branch instruction*)
    code[pc] := ((op+12) * 10H + cond) * 1000000H + (off MOD 1000000H); INC(pc);
  END vPut3;




  PROCEDURE fix*(at, with: LONGINT);
  BEGIN code[at] := code[at] DIV C24 * C24 + (with MOD C24);
  END fix;

  PROCEDURE FixOne*(pc,pcb,at: LONGINT);
  BEGIN fix(at, pc-at-1)
  END FixOne;

  PROCEDURE FixLink*(pc,pcb,L: LONGINT);
    VAR L1: LONGINT;
  BEGIN
    WHILE L # 0 DO L1 := code[L] MOD 40000H; fix(L, pc-L-1); L := L1 END
  END FixLink;

  PROCEDURE FixLinkWith*(L0, dst: LONGINT);
    VAR L1: LONGINT;
  BEGIN
    WHILE L0 # 0 DO
      L1 := code[L0] MOD C24;
      code[L0] := code[L0] DIV C24 * C24 + ((dst - L0 - 1) MOD C24); L0 := L1;
    END
  END FixLinkWith;

  PROCEDURE merged*(L0, L1: LONGINT): LONGINT;
    VAR L2, L3: LONGINT;
  BEGIN
    IF L0 # 0 THEN L3 := L0;
      REPEAT L2 := L3; L3 := code[L2] MOD 40000H UNTIL L3 = 0;
      code[L2] := code[L2] + L1; L1 := L0;
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
  BEGIN  (*exit code*)
    IF version = 0 THEN RPut1(3,  pc, pcb, Mov, 0, 0, 0); RPut3(pc, pcb, BR, 7, 0)  (*RISC-0*)
    ELSE RPut2(pc, pcb, Ldr, LNK, SP, 0); RPut1(4,  pc, pcb, Add, SP, SP, 4); RPut3(pc, pcb, BR, 7, LNK)
    END ;
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
     
    IF ORS.ccARCH = ORS.RISC5 THEN ORB.MakeFileName(name, modid, ".rsc") END;
    IF ORS.ccARCH = ORS.X8664 THEN ORB.MakeFileName(name, modid, ".i64") END;
    IF ORS.ccARCH = ORS.ARM64 THEN ORB.MakeFileName(name, modid, ".a64") END;
    IF ORS.ccARCH = ORS.ARM32 THEN ORB.MakeFileName(name, modid, ".a32") END;
    IF ORS.ccARCH = ORS.RISCV64 THEN ORB.MakeFileName(name, modid, ".v64") END;
    IF ORS.ccARCH = ORS.RISCV32 THEN ORB.MakeFileName(name, modid, ".v32") END;

    F := Files.New(name); Files.Set(R, F, 0); Files.WriteString(R, modid); Files.WriteInt(R, key); Files.Write(R, CHR(version));
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
    FOR i := 0 TO pc-1 DO Files.WriteInt(R, code[i]) END ;  (*program*)
    obj := ORB.topScope.next;
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
  END Close;



BEGIN
END OXG.

