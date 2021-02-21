(* begin-module-short-description
provides for RISC5 disassembly.
end-module-short-description *)

(* begin-module-use-description
Module ORDis disassembles RISC5 opcodes.

end-module-use-description *)
(* begin-module-develop-description

(CP 2020)

**ORDis** is a disassembler of RISC5 opcodes.
The module sets up a state machine that operates on an input via repeated calls to decode.

end-module-develop-description *)
MODULE ORDis;   (*CP 2020*)
  IMPORT SYSTEM, Files, Oberon;
  CONST 
    OK* = 0; FINISH* = 1; BAD* = 2;
    BADARCH=0; RISC5=1; X8664=2; AARCH64=3; ARM32=4; RISCV64=5; RISCV32=6;
    BYTEORIENTED=0; WORDORIENTED=1;

  TYPE

  VAR
    E*, at*, pc*, isz*, wo*: INTEGER;
    ibytes*: ARRAY 32 OF BYTE;
    istr*: ARRAY 32 OF CHAR;
    mnemo0, mnemo1, reg: ARRAY 16, 4 OF CHAR;  (*mnemonics*)
    vendor*, mode*, cfo*, cfe*: INTEGER;
    R*: Files.Rider;
    F*: Files.File;

  PROCEDURE append(VAR s1: ARRAY OF CHAR; s2: ARRAY OF CHAR);
    VAR c1,c2: INTEGER;
  BEGIN
    c1:=0; WHILE (c1 < LEN(s1)) & (s1[c1] # 0X) DO INC(c1) END;
    c2:=0; WHILE (c1 < LEN(s1)) & (c2 < LEN(s2)) & (s2[c2] # 0X) DO s1[c1]:=s2[c2];INC(c1);INC(c2) END;
    IF c1 < LEN(s1) THEN s1[c1]:=0X END
  END append;


  PROCEDURE strInt (x: LONGINT; VAR s: ARRAY OF CHAR);
    VAR i,c: INTEGER; x0: LONGINT;
      a: ARRAY 12 OF CHAR;
  BEGIN
    IF ROR(x, 31) = 1 THEN s:= " -2147483648"
    ELSE i := 0;
      IF x < 0 THEN x0 := -x ELSE x0 := x END;
      REPEAT
        a[i] := CHR(x0 MOD 10 + 30H); x0 := x0 DIV 10; INC(i)
      UNTIL x0 = 0;
      s[0] := " ";
      c:=1;
      IF x < 0 THEN s[c]:= "-"; INC(c) END;
      REPEAT DEC(i); s[c]:= a[i]; INC(c) UNTIL i = 0;
      s[c]:=0X;
    END
  END strInt;

  PROCEDURE strHex (x: LONGINT; VAR s: ARRAY OF CHAR);
    VAR t:INTEGER;
  BEGIN
    s[10]:=0X;
    s[9]:="H";
    t:=x MOD 10H;       IF t<10 THEN s[8]:=CHR(t+48) ELSE s[8]:=CHR(t+55) END;
    t:=x DIV 10H MOD 10H;IF t<10 THEN s[7]:=CHR(t+48) ELSE s[7]:=CHR(t+55) END;
    t:=x DIV 100H MOD 10H;IF t<10 THEN s[6]:=CHR(t+48) ELSE s[6]:=CHR(t+55) END;
    t:=x DIV 1000H MOD 10H;IF t<10 THEN s[5]:=CHR(t+48) ELSE s[5]:=CHR(t+55) END;
    t:=x DIV 10000H MOD 10H;IF t<10 THEN s[4]:=CHR(t+48) ELSE s[4]:=CHR(t+55) END;
    t:=x DIV 100000H MOD 10H;IF t<10 THEN s[3]:=CHR(t+48) ELSE s[3]:=CHR(t+55) END;
    t:=x DIV 1000000H MOD 10H;IF t<10 THEN s[2]:=CHR(t+48) ELSE s[2]:=CHR(t+55) END;
    t:=x DIV 10000000H MOD 10H;IF t<10 THEN s[1]:=CHR(t+48) ELSE s[1]:=CHR(t+55) END;
    s[0]:=" ";
  END strHex;

  PROCEDURE WriteReg(r: INTEGER; p: INTEGER; VAR s: ARRAY OF CHAR);
  BEGIN 
    IF r < 10 THEN s[p]:="R"; s[p+1]:= CHR(ORD("0")+((r MOD 16) MOD 10)); s[p+2]:=" "
    ELSIF r < 12 THEN s[p]:="R"; s[p+1]:= CHR(ORD("0")+((r MOD 16) DIV 10));s[p+2]:= CHR(ORD("0")+((r MOD 16) MOD 10));
    ELSIF r = 12 THEN s[p]:="M"; s[p+1]:= "T"; s[p+2]:="R"
    ELSIF r = 13 THEN s[p]:="S"; s[p+1]:= "B"; s[p+2]:="R"  
    ELSIF r = 14 THEN s[p]:="S"; s[p+1]:= "P"; s[p+2]:="R"
    ELSE s[p]:="L"; s[p+1]:= "N"; s[p+2]:="K"
    END
  END WriteReg;

  PROCEDURE opcode(w: LONGINT; VAR s:ARRAY OF CHAR);
    VAR k, op, u, a, b, c: LONGINT; t: ARRAY 32 OF CHAR; 
  BEGIN
      k := w DIV 40000000H MOD 4;
      a := w DIV 1000000H MOD 10H;
      b := w DIV 100000H MOD 10H;
      op := w DIV 10000H MOD 10H;
      u := w DIV 20000000H MOD 2;
      IF k = 0 THEN
        s[0]:=mnemo0[op][0];  s[1]:=mnemo0[op][1]; s[2]:=mnemo0[op][2]; s[3]:=" ";
        IF u = 1 THEN s[3]:="'" ELSE s[3]:=" " END ; s[4]:=" "; s[5]:=0X;
        append(s,reg[a]); append(s,reg[b]); append(s,reg[w MOD 10H]);
      ELSIF k = 1 THEN
        s[0]:=mnemo0[op][0];  s[1]:=mnemo0[op][1]; s[2]:=mnemo0[op][2]; s[3]:=" ";
        IF u = 1 THEN s[3]:="'" ELSE s[3]:=" " END ; s[4]:=" "; s[5]:=0X;
        append(s,reg[a]); append(s,reg[b]); w := w MOD 10000H;
        IF w >= 8000H THEN w := w - 10000H END ;
        strHex(w,t);
        append(s,t);
      ELSIF k = 2 THEN  (*LDR/STR*)
        IF u = 1 THEN s[0]:="S"; s[1]:="T" ELSE s[0]:="L"; s[1]:="D"  END ; 
        s[2]:="R"; 
        IF ODD(w DIV 10000000H ) THEN s[3]:="'" ELSE s[3]:=" " END; s[4]:=" "; s[5]:=0X;
        append(s,reg[a]); append(s,reg[b]);   w := w MOD 100000H;
        IF w >= 80000H THEN w := w - 100000H END ;
        strHex(w,t);
        append(s,t);
        
      ELSIF k = 3 THEN  (*Branch instr*)
        s[0]:= "B"; s[1]:=0X;
        append(s, mnemo1[a]); 
        IF ODD(w DIV 10000000H) THEN append(s,"L") END ;
        IF u = 0 THEN append(s,reg[w MOD 10H]) ELSE
          w := w MOD 100000H;
          IF w >= 80000H THEN w := w - 100000H END ;
          strHex(w, t);  
          append(s,t)
        END 
       
      END
  END opcode;

  PROCEDURE decode*():INTEGER;
    VAR e,i: INTEGER; b: CHAR; t: ARRAY 32 OF CHAR;
  BEGIN
    e := OK;
    at :=pc;
    isz := 0;
    WHILE isz < 4 DO
      Files.Set(R,F,cfo+pc);
      Files.Read(R, b);
      ibytes[isz]:=ORD(b);
      INC(pc);
      INC(isz)
    END;
    i:=ibytes[0]+(ibytes[1]*100H)+(ibytes[2]*10000H)+(ibytes[3]*1000000H);
    opcode(i,istr);
    IF pc >= cfe THEN e:= FINISH END;
    IF R.eof THEN e:= FINISH END;
    E:=e;
    RETURN e
  END decode;

  PROCEDURE init*(VAR f: Files.File; i, o, e: INTEGER);
  BEGIN
    F := f;
    E:=OK;
    pc := i;
    at := i;
    cfo := o;
    cfe := e;
    Files.Set(R, f, cfo+pc);
  END init;

  PROCEDURE originate*(r: Files.Rider; f: Files.File; offset, extent, index: INTEGER): INTEGER;
    VAR e: INTEGER;
  BEGIN
    e:=OK;
    init(f,index,offset,extent);
    E:=e;
    RETURN e
  END originate;

BEGIN 
  E := OK;
  wo:= WORDORIENTED;
  vendor := 0;
  mode := 64;
  at := 0;
  pc := 0;
  isz := 0;
  istr := "undecoded risc5";
  cfo := 0;
  cfe := 0;
  mnemo0[0] := "MOV";
  mnemo0[1] := "LSL";
  mnemo0[2] := "ASR";
  mnemo0[3] := "ROR";
  mnemo0[4] := "AND";
  mnemo0[5] := "ANN";
  mnemo0[6] := "IOR";
  mnemo0[7] := "XOR";
  mnemo0[8] := "ADD";
  mnemo0[9] := "SUB";
  mnemo0[10] := "MUL";
  mnemo0[11] := "DIV";
  mnemo0[12] := "FAD";
  mnemo0[13] := "FSB";
  mnemo0[14] := "FML";
  mnemo0[15] := "FDV";
  mnemo1[0] := "MI ";
  mnemo1[8] := "PL";
  mnemo1[1] := "EQ ";
  mnemo1[9] := "NE ";
  mnemo1[2] := "LS ";
  mnemo1[10] := "HI ";
  mnemo1[5] := "LT ";
  mnemo1[13] := "GE ";
  mnemo1[6] := "LE ";
  mnemo1[14] := "GT ";
  mnemo1[15] := "NO ";
  reg[0]:="R0 ";
  reg[1]:="R1 ";
  reg[2]:="R2 ";
  reg[3]:="R3 ";
  reg[4]:="R4 ";
  reg[5]:="R5 ";
  reg[6]:="R6 ";
  reg[7]:="R7 ";
  reg[8]:="R8 ";
  reg[9]:="R9 ";
  reg[10]:="RA ";
  reg[11]:="RB ";
  reg[12]:="MT ";
  reg[13]:="SB ";
  reg[14]:="SP ";
  reg[15]:="LR ";

END ORDis.
