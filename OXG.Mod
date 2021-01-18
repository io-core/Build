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
    Ldr = 8; Str = 10;
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;
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

  PROCEDURE setRegMap*;               (*%P *)
  (* begin-procedure-description
---
**setRegMap**
  end-procedure-description *)
    VAR i : INTEGER;
  BEGIN
    FOR i:= 0 TO 15 DO regmap[i]:=i END;   (*   MT = 12; SP = 14; LNK = 15;   *)
    IF ORS.ccARCH = ORS.X8664 THEN (* RSP = SP, RBP = MT, RBX = LNK *)

      regmap[0]:=8; regmap[1]:=9; regmap[2]:=10; regmap[3]:=11; regmap[4]:=12; regmap[5]:=13; regmap[6]:=14; regmap[7]:=15;
      regmap[8]:=1; regmap[9]:=2; regmap[10]:=6; regmap[11]:=7; regmap[MT]:=5; regmap[13]:=0; regmap[SP]:=4; regmap[LNK]:=3;

    ELSIF ORS.ccARCH = ORS.ARM64 THEN regmap[MT]:=29; regmap[13]:=13; regmap[SP]:=31; regmap[LNK]:=30;
    ELSIF ORS.ccARCH = ORS.ARM32 THEN regmap[MT]:=12; regmap[SP]:=13; regmap[LNK]:=14;
    ELSIF ORS.ccARCH = ORS.RISCV64 THEN FOR i:= 0 TO 15 DO regmap[i]:=10+i END; regmap[MT]:=3; regmap[SP]:=2; regmap[LNK]:=1;
    ELSIF ORS.ccARCH = ORS.RISCV32 THEN FOR i:= 0 TO 15 DO regmap[i]:=10+i END; regmap[MT]:=3; regmap[SP]:=2; regmap[LNK]:=1;
    END
  END setRegMap;                     (* P%*)

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
## ---------- X8664 instruction generation
  end-section-description *)

(* begin-procedure-description
---
**IPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE IPut0*(VAR pc, pcb: LONGINT; op, ai, bi, c: LONGINT);
    VAR a,b,a0,a1:INTEGER;
  BEGIN (*emit format-0 instruction*)
    a:=regmap[ai];b:=regmap[bi];
    a1:=a MOD 8; a0:=48H; IF a > 8 THEN a0 := 49H END;
    IF    op = Mov THEN Put3Bytes( a0, 089H, 0C0H+a1, pc, pcb ) 
    ELSIF op = Lsl THEN Put3Bytes( a0, 0C1H, 0E0H+a1, pc, pcb ) 
    ELSIF op = Asr THEN Put3Bytes( a0, 0C1H, 0E8H+a1, pc, pcb ) 
    ELSIF op = Ror THEN Put3Bytes( a0, 0C1H, 0C8H+a1, pc, pcb ) 
    ELSIF op = And THEN Put3Bytes( a0, 021H, 0F8H+a1, pc, pcb ) 
    ELSIF op = Ann THEN Put3Bytes( a0, 021H, 0F8H+a1, pc, pcb )  (* and not *)
    ELSIF op = Ior THEN Put3Bytes( a0, 009H, 0F8H+a1, pc, pcb ) 
    ELSIF op = Xor THEN Put3Bytes( a0, 031H, 0F8H+a1, pc, pcb ) 
    ELSIF op = Add THEN Put3Bytes( a0, 001H, 0F8H+a1, pc, pcb ) 
    ELSIF op = Sub THEN Put3Bytes( a0, 029H, 0F8H+a1, pc, pcb ) 
(*  ELSIF op = Cmp THEN Put3Bytes( a0, 039H, 0F8H+a1, pc, pcb )  *)
    ELSIF op = Mul THEN Put3Bytes( a0, 0F7H, 0E0H+a1, pc, pcb )  (* EAX mul by reg *)
    ELSIF op = Div THEN Put3Bytes( a0, 0F7H, 0F0H+a1, pc, pcb )  (* EAX div by reg *)
    ELSIF op = Fad THEN Put3Bytes( 090H, 090H, 090H, pc, pcb )  
    ELSIF op = Fsb THEN Put3Bytes( 090H, 090H, 090H, pc, pcb )  
    ELSIF op = Fml THEN Put3Bytes( 090H, 090H, 090H, pc, pcb )  
    ELSIF op = Fdv THEN Put3Bytes( 090H, 090H, 090H, pc, pcb ) 
    END;
  END IPut0;

  (* begin-procedure-description
---
**IPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE IPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, ai, bi, im: LONGINT);
    VAR a,b,a0,a1,b0,b1:INTEGER;
  BEGIN (*emit format-1 instruction,  -10000H <= im < 10000H*)
    a:=regmap[ai];b:=regmap[bi];
    a1:=a MOD 8; a0:=48H; IF a > 8 THEN a0 := 49H END;
    IF    op = Mov THEN Put3Bytes( a0, 0C7H, 0C0H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Lsl THEN Put3Bytes( a0, 0C1H, 0E0H + a1, pc, pcb ); Put1Byte( im, pc, pcb )
    ELSIF op = Asr THEN Put3Bytes( a0, 0C1H, 0E8H + a1, pc, pcb ); Put1Byte( im, pc, pcb )
    ELSIF op = Ror THEN Put3Bytes( a0, 0C1H, 0C8H + a1, pc, pcb ); Put1Byte( im, pc, pcb )
    ELSIF op = And THEN Put3Bytes( a0, 081H, 0E0H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Ann THEN Put3Bytes( a0, 000H, 000H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Ior THEN Put3Bytes( a0, 081H, 0C8H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Xor THEN Put3Bytes( a0, 081H, 0F0H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Add THEN Put3Bytes( a0, 081H, 0C0H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Sub THEN Put3Bytes( a0, 081H, 0E8H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
(*  ELSIF op = Cmp THEN Put3Bytes( a0, 081H, 0F8H + a1, pc, pcb ); Put4Integer( im, pc, pcb ) *)
    ELSIF op = Mul THEN Put3Bytes( a0, 000H, 000H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Div THEN Put3Bytes( a0, 000H, 000H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Fad THEN Put3Bytes( a0, 000H, 000H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Fsb THEN Put3Bytes( a0, 000H, 000H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Fml THEN Put3Bytes( a0, 000H, 000H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    ELSIF op = Fdv THEN Put3Bytes( a0, 000H, 000H + a1, pc, pcb ); Put4Integer( im, pc, pcb )
    END;
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
    disp:=(off * 4) - 1;
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
**APut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE APut0*(VAR pc, pcb: LONGINT; op, ai, bi, ci: LONGINT);
    VAR a,b,c:INTEGER;
  BEGIN (*emit format-0 instruction*)
    a:=regmap[ai];b:=regmap[bi];c:=regmap[ci];
    IF    op = Mov THEN code[pc]:= (0AAH * 1000000H) + (c * 10000H) + (1FH * 20H) + a; INC(pc)
    ELSIF op = Lsl THEN  
    ELSIF op = Asr THEN  
    ELSIF op = Ror THEN  
    ELSIF op = And THEN  
    ELSIF op = Ann THEN   (* and not *)
    ELSIF op = Ior THEN  
    ELSIF op = Xor THEN  
    ELSIF op = Add THEN code[pc]:= (0ABH * 1000000H) + (c * 10000H) + (b * 20H) + a; INC(pc)
    ELSIF op = Sub THEN code[pc]:= (0EBH * 1000000H) + (c * 10000H) + (b * 20H) + a; INC(pc)  
(*  ELSIF op = Cmp THEN   *)
    ELSIF op = Mul THEN   (* EAX mul by reg *)
    ELSIF op = Div THEN   (* EAX div by reg *)
    ELSIF op = Fad THEN  
    ELSIF op = Fsb THEN  
    ELSIF op = Fml THEN  
    ELSIF op = Fdv THEN  
    END;
  END APut0;

  (* begin-procedure-description
---
**APut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE APut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, ai, bi, im: LONGINT);
    VAR a,b:INTEGER;
  BEGIN (*emit format-1 instruction,  -10000H <= im < 10000H*)
    a:=regmap[ai];b:=regmap[bi];
   
    IF    op = Mov THEN code[pc]:= (1A5H * 800000H) + (im * 20H) + a; INC(pc)
    ELSIF op = Lsl THEN 
    ELSIF op = Asr THEN 
    ELSIF op = Ror THEN 
    ELSIF op = And THEN 
    ELSIF op = Ann THEN 
    ELSIF op = Ior THEN 
    ELSIF op = Xor THEN 
    ELSIF op = Add THEN code[pc]:= (0B1H * 1000000H) + (im * 400H) + (b * 20H) + a; INC(pc)
    ELSIF op = Sub THEN code[pc]:= (0F1H * 1000000H) + (im * 400H) + (b * 20H) + a; INC(pc)
    ELSIF op = Cmp THEN 
    ELSIF op = Mul THEN 
    ELSIF op = Div THEN 
    ELSIF op = Fad THEN 
    ELSIF op = Fsb THEN 
    ELSIF op = Fml THEN 
    ELSIF op = Fdv THEN 
    END;
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
    VAR opc,osz,disp: INTEGER;
  BEGIN (*emit branch instruction*)
(*
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;
*)
    disp:=off;
    IF    op = BR  THEN (*via register*)
      code[pc]:= 0D61FH * 10000H + (regmap[off] * 20H); INC(pc)
    ELSIF op = BLR THEN (*via register and depositing link*)
      code[pc]:= 0D63FH * 10000H + (regmap[off] * 20H); INC(pc)
    ELSIF op = BC  THEN (*via offset from pc*)
      INC(pc)
    ELSIF op = BL  THEN (*via offset from pc and depositing link*)
      INC(pc)
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
      APut1(121, pc, pcb, Sub, SP, SP, 16); APut2(pc, pcb, Str, LNK, SP, 0) 
    ELSE 
      APut1(121, pc, pcb, Sub, SP, SP, 16); APut2(pc, pcb, Str, LNK, SP, 0)
    END
  END AHeader;


  (* begin-section-description
## ---------- ARM32 instruction generation
  end-section-description *)

(* begin-procedure-description
---
**aPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE aPut0*(VAR pc, pcb: LONGINT; op, ai, bi, ci: LONGINT);
    VAR a,b,c:INTEGER;
  BEGIN (*emit format-0 instruction*)
    a:=regmap[ai];b:=regmap[bi];c:=regmap[ci];
    IF    op = Mov THEN code[pc]:= (0E18H * 100000H) + (a * 10000H) + (b * 1000H) + b ; INC(pc)
    ELSIF op = Lsl THEN  
    ELSIF op = Asr THEN  
    ELSIF op = Ror THEN  
    ELSIF op = And THEN code[pc]:= (0E00H * 100000H) + (a * 10000H) + (b * 1000H) + c ; INC(pc) 
    ELSIF op = Ann THEN   (* and not *)
    ELSIF op = Ior THEN code[pc]:= (0E18H * 100000H) + (a * 10000H) + (b * 1000H) + c ; INC(pc)  
    ELSIF op = Xor THEN code[pc]:= (0E02H * 100000H) + (a * 10000H) + (b * 1000H) + c ; INC(pc)  
    ELSIF op = Add THEN code[pc]:= (0E08H * 100000H) + (a * 10000H) + (b * 1000H) + c ; INC(pc) 
    ELSIF op = Sub THEN code[pc]:= (0E04H * 100000H) + (a * 10000H) + (b * 1000H) + c ; INC(pc)  
(*  ELSIF op = Cmp THEN   *)
    ELSIF op = Mul THEN   
    ELSIF op = Div THEN   
    ELSIF op = Fad THEN  
    ELSIF op = Fsb THEN  
    ELSIF op = Fml THEN  
    ELSIF op = Fdv THEN  
    END;
(*
  BEGIN (*emit format-0 instruction*)
      code[pc] := ((a*10H + b) * 10H + op) * 10000H + c;
    INC(pc);
*)
  END aPut0;

  (* begin-procedure-description
---
**aPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE aPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, ai, bi, im: LONGINT);
    VAR a,b,s:INTEGER;
  BEGIN (*emit format-1 instruction,  -100H <= im < 100H*)
    s:=0;
    a:=regmap[ai];b:=regmap[bi];
   
    IF    op = Mov THEN code[pc]:= (0E30H * 100000H) + (a * 10000H) + (b * 1000H) + (s * 100H) + (im MOD 100H) ; INC(pc)
    ELSIF op = Lsl THEN 
    ELSIF op = Asr THEN 
    ELSIF op = Ror THEN 
    ELSIF op = And THEN code[pc]:= (0E20H * 100000H) + (a * 10000H) + (b * 1000H) + (s * 100H) + (im MOD 100H) ; INC(pc)
    ELSIF op = Ann THEN   (* and not *)
    ELSIF op = Ior THEN code[pc]:= (0E38H * 100000H) + (a * 10000H) + (b * 1000H) + (s * 100H) + (im MOD 100H) ; INC(pc)
    ELSIF op = Xor THEN code[pc]:= (0E22H * 100000H) + (a * 10000H) + (b * 1000H) + (s * 100H) + (im MOD 100H) ; INC(pc)
    ELSIF op = Add THEN code[pc]:= (0E28H * 100000H) + (a * 10000H) + (b * 1000H) + (s * 100H) + (im MOD 100H) ; INC(pc)
    ELSIF op = Sub THEN code[pc]:= (0E24H * 100000H) + (a * 10000H) + (b * 1000H) + (s * 100H) + (im MOD 100H) ; INC(pc)
    ELSIF op = Cmp THEN 
    ELSIF op = Mul THEN 
    ELSIF op = Div THEN 
    ELSIF op = Fad THEN 
    ELSIF op = Fsb THEN 
    ELSIF op = Fml THEN 
    ELSIF op = Fdv THEN 
    END;
(*
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
*) 
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
    VAR opc,osz,disp: INTEGER;
  BEGIN (*emit branch instruction*)
(*
    BR = 0; BLR = 1; BC = 2; BL = 3;
    MI = 0; PL = 8; EQ = 1; NE = 9; LT = 5; GE = 13; LE = 6; GT = 14;
*)
    disp:=off;
    IF    op = BR  THEN (*via register*)
      code[pc]:= 0E12FFF10H + regmap[off] ; INC(pc)
    ELSIF op = BLR THEN (*via register and depositing link*)
      code[pc]:= 0E12FFF30H + regmap[off] ; INC(pc)
    ELSIF op = BC  THEN (*via offset from pc*)
      INC(pc)
    ELSIF op = BL  THEN (*via offset from pc and depositing link*)
      INC(pc)
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
      aPut1(121, pc, pcb, Sub, SP, SP, 4); aPut2(pc, pcb, Str, LNK, SP, 0)
    ELSE 
      aPut1(121, pc, pcb, Sub, SP, SP, 4); aPut2(pc, pcb, Str, LNK, SP, 0)
    END
  END aHeader;



  (* begin-section-description
## ---------- RISCV64 instruction generation
  end-section-description *)




(* begin-procedure-description
---
**vUJ** convert an integer to UJ immediate format
  end-procedure-description *)
  PROCEDURE vUJ( i : LONGINT ): LONGINT;
    VAR a,b,c,d:LONGINT;
  BEGIN
	a := (i DIV 100000H MOD 2) * 40000H;
	b := (i DIV 2 MOD 200H) * 200H;
	c := (i DIV 800H MOD 2) * 100H;
	d := (i DIV 1000H MOD 100H);
  RETURN a + b + c + d
  END vUJ;

(* begin-procedure-description
---
**VPut0** PutRegFromRegOpReg
  end-procedure-description *)
  PROCEDURE VPut0*(VAR pc, pcb: LONGINT; op, ai, bi, ci: LONGINT);
    VAR a,b,c:INTEGER;
  BEGIN (*emit format-0 instruction*)
    a:=regmap[ai];b:=regmap[bi];c:=regmap[ci];
    IF    op = Mov THEN
    ELSIF op = Lsl THEN  
    ELSIF op = Asr THEN  
    ELSIF op = Ror THEN  
    ELSIF op = And THEN code[pc]:= 33H + (a * 80H) + (7 * 1000H) + (b * 8000H) + (c * 10000H) ; INC(pc) 
    ELSIF op = Ann THEN   (* and not *)
    ELSIF op = Ior THEN code[pc]:= 33H + (a * 80H) + (6 * 1000H) + (b * 8000H) + (c * 10000H) ; INC(pc)  
    ELSIF op = Xor THEN code[pc]:= 33H + (a * 80H) + (4 * 1000H) + (b * 8000H) + (c * 10000H) ; INC(pc)  
    ELSIF op = Add THEN code[pc]:= 33H + (a * 80H) + (0 * 1000H) + (b * 8000H) + (c * 10000H) ; INC(pc) 
    ELSIF op = Sub THEN code[pc]:= 33H + (a * 80H) + (1 * 40000000H) + (b * 8000H) + (c * 10000H) ; INC(pc)  
(*  ELSIF op = Cmp THEN   *)
    ELSIF op = Mul THEN   
    ELSIF op = Div THEN   
    ELSIF op = Fad THEN  
    ELSIF op = Fsb THEN  
    ELSIF op = Fml THEN  
    ELSIF op = Fdv THEN  
    END;
(*
  BEGIN (*emit format-0 instruction*)
      code[pc] := ((a*10H + b) * 10H + op) * 10000H + c;
    INC(pc);
*)
  END VPut0;

  (* begin-procedure-description
---
**VPut1** PutRegFromRegOpImmSmall
  end-procedure-description *)
  PROCEDURE VPut1*(o: INTEGER; VAR pc, pcb: LONGINT; op, ai, bi, im: LONGINT);
    VAR a,b:INTEGER;
  BEGIN (*emit format-1 instruction,  -1000H <= im < 1000H*) (* smaller than RISC5! *)
    a:=regmap[ai];b:=regmap[bi];
   
    IF    op = Mov THEN code[pc]:= 37H + (a * 80H) + (im * 1000H) ; INC(pc)
    ELSIF op = Lsl THEN 
    ELSIF op = Asr THEN 
    ELSIF op = Ror THEN 
    ELSIF op = And THEN code[pc]:= 13H + (a * 80H) + (7 * 1000H) + (b * 8000H) + (im * 100000H) ; INC(pc) 
    ELSIF op = Ann THEN   (* and not *)
    ELSIF op = Ior THEN code[pc]:= 13H + (a * 80H) + (6 * 1000H) + (b * 8000H) + (im * 100000H) ; INC(pc)  
    ELSIF op = Xor THEN code[pc]:= 13H + (a * 80H) + (4 * 1000H) + (b * 8000H) + (im * 100000H) ; INC(pc)  
    ELSIF op = Add THEN code[pc]:= 13H + (a * 80H) + (0 * 1000H) + (b * 8000H) + (im * 100000H) ; INC(pc) 
    ELSIF op = Sub THEN code[pc]:= 13H + (a * 80H) + (0 * 1000H) + (b * 8000H) + ((0-im) * 100000H) ; INC(pc)
    ELSIF op = Cmp THEN 
    ELSIF op = Mul THEN 
    ELSIF op = Div THEN 
    ELSIF op = Fad THEN 
    ELSIF op = Fsb THEN 
    ELSIF op = Fml THEN 
    ELSIF op = Fdv THEN 
    END;
(*
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
*) 
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
      code[pc]:= 6FH + (vUJ(off) * 1000H) ; INC(pc)
    ELSIF op = BL  THEN (*via offset from pc and depositing link*)
      INC(pc)
    END;
  END VPut3;

  (* begin-procedure-description
---
**VHeader** prepares the code introductory sequence for a compiled module
  end-procedure-description *)
  PROCEDURE VHeader*(VAR pc, pcb, RH, entry, version: LONGINT);
  BEGIN entry := pc*4;
    IF version = 0 THEN 
      code[0] := 6FH + (vUJ(entry) * 1000H);
      VPut1(121, pc, pcb, Sub, SP, SP, 8); VPut2(pc, pcb, Str, LNK, SP, 0)
    ELSE 
      VPut1(121, pc, pcb, Sub, SP, SP, 8); VPut2(pc, pcb, Str, LNK, SP, 0)
    END
  END VHeader;




  (* begin-section-description
## ---------- RISCV32 instruction generation
  end-section-description *)

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
      code[0] := 6FH + (vUJ(entry) * 1000H) ;
      vPut1(121, pc, pcb, Sub, SP, SP, 4); vPut2(pc, pcb, Str, LNK, SP, 0)
    ELSE
      vPut1(121, pc, pcb, Sub, SP, SP, 4); vPut2(pc, pcb, Str, LNK, SP, 0)
    END
  END vHeader;




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

