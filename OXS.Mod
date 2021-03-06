(* begin-module-short-description
implements lexical analysis for the Oberon language.
end-module-short-description *)

(* begin-module-use-description
Module OXS does lexical analysis of the Oberon source code and defines symbols and operations

end-module-use-description *)
(* begin-module-develop-description

(NW 19.9.93 / 20.3.2017  Scanner in Oberon-07)

**OXS** is called from ORP, OXG, and OXB and converts the source text to symbols for their consumption.

Oberon Scanner does lexical analysis. Input is Oberon-Text, output is
sequence of symbols, i.e identifiers, numbers, strings, and special symbols.
Recognises all Oberon keywords and skips comments. The keywords are recorded in a table.

`Get(sym)` delivers next symbol from input text with Reader R.

`Mark(msg)` records error and delivers error message with Writer W.

If Get delivers ident, then the identifier (a string) is in variable id, 
if int or char in ival, if real in rval, and if string in str (and slen) 

end-module-develop-description *)
MODULE OXS; (* NW 19.9.93 / 15.3.2017  Scanner in Oberon-07*)
  IMPORT SYSTEM, Texts, Oberon;

(* Oberon Scanner does lexical analysis. Input is Oberon-Text, output is
  sequence of symbols, i.e identifiers, numbers, strings, and special symbols.
  Recognises all Oberon keywords and skips comments. The keywords are
  recorded in a table.
  Get(sym) delivers next symbol from input text with Reader R.
  Mark(msg) records error and delivers error message with Writer W.
  If Get delivers ident, then the identifier (a string) is in variable id, if int or char
  in ival, if real in rval, and if string in str (and slen) *)
  
  CONST 
    IdLen* = 32;
    NKW = 34;  (*nof keywords*)
    maxExp = 38; stringBufSize = 256;
  
    (*lexical symbols*)
    null = 0; times* = 1; rdiv* = 2; div* = 3; mod* = 4;
    and* = 5; plus* = 6; minus* = 7; or* = 8; eql* = 9;
    neq* = 10; lss* = 11; leq* = 12; gtr* = 13; geq* = 14;
    in* = 15; is* = 16; arrow* = 17; period* = 18;
    char* = 20; int* = 21; real* = 22; false* = 23; true* = 24;
    nil* = 25; string* = 26; not* = 27; lparen* = 28; lbrak* = 29;
    lbrace* = 30; ident* = 31;
    if* = 32; while* = 34; repeat* = 35; case* = 36; for* = 37;
    comma* = 40; colon* = 41; becomes* = 42; upto* = 43; rparen* = 44;
    rbrak* = 45; rbrace* = 46; then* = 47; of* = 48; do* = 49;
    to* = 50; by* = 51; semicolon* = 52; end* = 53; bar* = 54;
    else* = 55; elsif* = 56; until* = 57; return* = 58;
    array* = 60; record* = 61; pointer* = 62; const* = 63; type* = 64;
    var* = 65; procedure* = 66; begin* = 67; import* = 68; module* = 69; eot = 70;
    notasymbol* = -1;
    go* = 100; on* = 101; def* = 102; dim* = 103; let* = 104; rem* = 105; sub* = 106; base* = 107;
    data* = 108; goto* = 109;  next* = 110;  read* = 110;  step* = 112; stop* = 113; gosub* = 114;
    input* = 115; print* = 116; option* = 117; restore* = 118; randomize* = 119;
    BADARCH* = 0; RISC5* = 1; X8664* = 2; ARM64* = 3; ARM32* = 4; RISCV64* = 5; RISCV32* = 6;
    BYTEORIENTED* = 0; WORDORIENTED* = 1;
    nostyle* = 0; oberonstyle* = 1; basicstyle* = 2; cstyle* = 3; 

  TYPE 
    Ident* = ARRAY IdLen OF CHAR;

  VAR ival*, slen*: LONGINT;  (*results of Get*)
    rval*: REAL;
    id*: Ident;  (*for identifiers*)
    str*: ARRAY stringBufSize OF CHAR;
    errcnt*: INTEGER;
    ccARCH*, ccWordsize, ccStackalign: INTEGER;
    ch: CHAR;  (*last character read*)
    errpos: LONGINT;
    R: Texts.Reader;
    W: Texts.Writer;
    commentstyle: INTEGER;
    k: INTEGER;
    KWX: ARRAY 10 OF INTEGER;
    keyTab: ARRAY NKW OF
        RECORD sym: INTEGER; id: ARRAY 12 OF CHAR END;
  
  (* begin-section-description
## ---------- Lexer
  end-section-description *)

  (* begin-procedure-description
---
**SetCommentStyle** sets the style of comments in the parser.
  end-procedure-description *)
  PROCEDURE SetCommentStyle*(style: INTEGER);
  BEGIN commentstyle := style
  END SetCommentStyle;

  (* begin-procedure-description
---
**CopyId** duplicates an identifier.
  end-procedure-description *)
  PROCEDURE CopyId*(VAR ident: Ident);
  BEGIN ident := id
  END CopyId;

  (* begin-procedure-description
---
**Pos** reports the location in the source text not couting the most current character.
  end-procedure-description *)
  PROCEDURE Pos*(): LONGINT;
  BEGIN RETURN Texts.Pos(R) - 1
  END Pos;

  (* begin-procedure-description
---
**Mark** reports an error to the Oberon system log.
  end-procedure-description *)
  PROCEDURE Mark*(msg: ARRAY OF CHAR);
    VAR p: LONGINT;
  BEGIN p := Pos();
    IF (p > errpos) & (errcnt < 25) THEN
      Texts.WriteLn(W); Texts.WriteString(W, "  pos "); Texts.WriteInt(W, p, 1); Texts.Write(W, " ");
      Texts.WriteString(W, msg); Texts.Append(Oberon.Log, W.buf)
    END ;
    INC(errcnt); errpos := p + 4
  END Mark;

  (* begin-procedure-description
---
**Identifier** matches an alphanumeric identifier.
  end-procedure-description *)
  PROCEDURE Identifier(VAR sym: INTEGER);
    VAR i, k: INTEGER;
  BEGIN i := 0;
    REPEAT
      IF i < IdLen-1 THEN id[i] := ch; INC(i) END ;
      Texts.Read(R, ch)
    UNTIL (ch < "0") OR (ch > "9") & (ch < "A") OR (ch > "Z") & (ch < "a") OR (ch > "z");
    id[i] := 0X; 
    IF i < 10 THEN k := KWX[i-1];  (*search for keyword*)
      WHILE (id # keyTab[k].id) & (k < KWX[i]) DO INC(k) END ;
      IF k < KWX[i] THEN sym := keyTab[k].sym ELSE sym := ident END
    ELSE sym := ident
    END
  END Identifier;

  (* begin-procedure-description
---
**String** matches a quote delimeted string.
  end-procedure-description *)
  PROCEDURE String;
    VAR i: INTEGER;
  BEGIN i := 0; Texts.Read(R, ch);
    WHILE ~R.eot & (ch # 22X) DO
      IF ch >= " " THEN
        IF i < stringBufSize-1 THEN str[i] := ch; INC(i) ELSE Mark("string too long") END ;
      END ;
      Texts.Read(R, ch)
    END ;
    str[i] := 0X; INC(i); Texts.Read(R, ch); slen := i
  END String;

  (* begin-procedure-description
---
**HexString** matches a hex string.
  end-procedure-description *)
  PROCEDURE HexString;
    VAR i, m, n: INTEGER;
  BEGIN i := 0; Texts.Read(R, ch);
    WHILE ~R.eot & (ch # "$") DO
      WHILE ~R.eot  & (ch <= " ") DO Texts.Read(R, ch) END ;  (*skip*)
      IF ("0" <= ch) & (ch <= "9") THEN m := ORD(ch) - 30H
      ELSIF ("A" <= ch) & (ch <= "F") THEN m := ORD(ch) - 37H
      ELSE m := 0; Mark("hexdig expected")
      END ;
      Texts.Read(R, ch);
      IF ("0" <= ch) & (ch <= "9") THEN n := ORD(ch) - 30H
      ELSIF ("A" <= ch) & (ch <= "F") THEN n := ORD(ch) - 37H
      ELSE n := 0; Mark("hexdig expected")
      END ;
      IF i < stringBufSize THEN str[i] := CHR(m*10H + n); INC(i) ELSE Mark("string too long") END ;
      Texts.Read(R, ch)
    END ;
    Texts.Read(R, ch); slen := i  (*no 0X appended!*)
  END HexString;

  (* begin-procedure-description
---
**Ten** ??
  end-procedure-description *)
  PROCEDURE Ten(e: LONGINT): REAL;
    VAR x, t: REAL;
  BEGIN x := 1.0; t := 10.0;
    WHILE e > 0 DO
      IF ODD(e) THEN x := t * x END ;
      t := t * t; e := e DIV 2
    END ;
    RETURN x
  END Ten;

  (* begin-procedure-description
---
**Number** matches a number.
  end-procedure-description *)
  PROCEDURE Number(VAR sym: INTEGER);
    CONST max = 2147483647 (*2^31 - 1*);
    VAR i, k, e, n, s, h: LONGINT; x: REAL;
      d: ARRAY 16 OF INTEGER;
      negE: BOOLEAN;
  BEGIN ival := 0; i := 0; n := 0; k := 0;
    REPEAT
      IF n < 16 THEN d[n] := ORD(ch)-30H; INC(n) ELSE Mark("too many digits"); n := 0 END ;
      Texts.Read(R, ch)
    UNTIL (ch < "0") OR (ch > "9") & (ch < "A") OR (ch > "F");
    IF (ch = "H") OR (ch = "R") OR (ch = "X") THEN  (*hex*)
      REPEAT h := d[i];
        IF h >= 10 THEN h := h-7 END ;
        k := k*10H + h; INC(i) (*no overflow check*)
      UNTIL i = n;
      IF ch = "X" THEN sym := char;
        IF k < 100H THEN ival := k ELSE Mark("illegal value"); ival := 0 END
      ELSIF ch = "R" THEN sym := real; rval := SYSTEM.VAL(REAL, k)
      ELSE sym := int; ival := k
      END ;
      Texts.Read(R, ch)
    ELSIF ch = "." THEN
      Texts.Read(R, ch);
      IF ch = "." THEN (*double dot*) ch := 7FX;  (*decimal integer*)
        REPEAT
          IF d[i] < 10 THEN
            IF k <= (max-d[i]) DIV 10 THEN k := k *10 + d[i] ELSE Mark("too large"); k := 0 END
          ELSE Mark("bad integer")
          END ;
          INC(i)
        UNTIL i = n;
        sym := int; ival := k
      ELSE (*real number*) x := 0.0; e := 0;
        REPEAT  (*integer part*) x := x * 10.0 + FLT(d[i]); INC(i) UNTIL i = n;
        WHILE (ch >= "0") & (ch <= "9") DO  (*fraction*)
          x := x * 10.0 + FLT(ORD(ch) - 30H); DEC(e); Texts.Read(R, ch)
        END ;
        IF (ch = "E") OR (ch = "D") THEN  (*scale factor*)
          Texts.Read(R, ch); s := 0; 
          IF ch = "-" THEN negE := TRUE; Texts.Read(R, ch)
          ELSE negE := FALSE;
            IF ch = "+" THEN Texts.Read(R, ch) END
          END ;
          IF (ch >= "0") & (ch <= "9") THEN
            REPEAT s := s*10 + ORD(ch)-30H; Texts.Read(R, ch)
            UNTIL (ch < "0") OR (ch >"9");
            IF negE THEN e := e-s ELSE e := e+s END
          ELSE Mark("digit?")
          END
        END ;
        IF e < 0 THEN
          IF e >= -maxExp THEN x := x / Ten(-e) ELSE x := 0.0 END
        ELSIF e > 0 THEN
          IF e <= maxExp THEN x := Ten(e) * x ELSE x := 0.0; Mark("too large") END
        END ;
        sym := real; rval := x
      END
    ELSE  (*decimal integer*)
      REPEAT
        IF d[i] < 10 THEN
          IF k <= (max-d[i]) DIV 10 THEN k := k*10 + d[i] ELSE Mark("too large"); k := 0 END
        ELSE Mark("bad integer")
        END ;
        INC(i)
      UNTIL i = n;
      sym := int; ival := k
    END
  END Number;

  (* begin-procedure-description
---
**Comment** matches comments.
  end-procedure-description *)
  PROCEDURE comment;
  BEGIN Texts.Read(R, ch);
    REPEAT
      WHILE ~R.eot & (ch # "*") DO
        IF ch = "(" THEN Texts.Read(R, ch);
          IF ch = "*" THEN comment END
        ELSE Texts.Read(R, ch)
        END
      END ;
      WHILE ch = "*" DO Texts.Read(R, ch) END
    UNTIL (ch = ")") OR R.eot;
    IF ~R.eot THEN Texts.Read(R, ch) ELSE Mark("unterminated comment") END
  END comment;

  (* begin-procedure-description
---
**Get** gets the next symbol from the source text.
  end-procedure-description *)
  PROCEDURE Get*(VAR sym: INTEGER);
  BEGIN
    REPEAT
      WHILE ~R.eot & (ch <= " ") DO Texts.Read(R, ch) END;
      IF R.eot THEN sym := eot
      ELSIF ch < "A" THEN
        IF ch < "0" THEN
          IF ch = 22X THEN String; sym := string
          ELSIF ch = "#" THEN Texts.Read(R, ch); sym := neq
          ELSIF ch = "$" THEN HexString; sym := string
          ELSIF ch = "&" THEN Texts.Read(R, ch); sym := and
          ELSIF ch = "(" THEN Texts.Read(R, ch); 
            IF ch = "*" THEN sym := null; comment ELSE sym := lparen END
          ELSIF ch = ")" THEN Texts.Read(R, ch); sym := rparen
          ELSIF ch = "*" THEN Texts.Read(R, ch); sym := times
          ELSIF ch = "+" THEN Texts.Read(R, ch); sym := plus
          ELSIF ch = "," THEN Texts.Read(R, ch); sym := comma
          ELSIF ch = "-" THEN Texts.Read(R, ch); sym := minus
          ELSIF ch = "." THEN Texts.Read(R, ch);
            IF ch = "." THEN Texts.Read(R, ch); sym := upto ELSE sym := period END
          ELSIF ch = "/" THEN Texts.Read(R, ch); sym := rdiv
          ELSE Texts.Read(R, ch); (* ! % ' *) sym := null
          END
        ELSIF ch < ":" THEN Number(sym)
        ELSIF ch = ":" THEN Texts.Read(R, ch);
          IF ch = "=" THEN Texts.Read(R, ch); sym := becomes ELSE sym := colon END 
        ELSIF ch = ";" THEN Texts.Read(R, ch); sym := semicolon
        ELSIF ch = "<" THEN  Texts.Read(R, ch);
          IF ch = "=" THEN Texts.Read(R, ch); sym := leq ELSE sym := lss END
        ELSIF ch = "=" THEN Texts.Read(R, ch); sym := eql
        ELSIF ch = ">" THEN Texts.Read(R, ch);
          IF ch = "=" THEN Texts.Read(R, ch); sym := geq ELSE sym := gtr END
        ELSE (* ? @ *) Texts.Read(R, ch); sym := null
        END
      ELSIF ch < "[" THEN Identifier(sym)
      ELSIF ch < "a" THEN
        IF ch = "[" THEN sym := lbrak
        ELSIF ch = "]" THEN  sym := rbrak
        ELSIF ch = "^" THEN sym := arrow
        ELSE (* _ ` *) sym := null
        END ;
        Texts.Read(R, ch)
      ELSIF ch < "{" THEN Identifier(sym) ELSE
        IF ch = "{" THEN sym := lbrace
        ELSIF ch = "}" THEN sym := rbrace
        ELSIF ch = "|" THEN sym := bar
        ELSIF ch = "~" THEN  sym := not
        ELSIF ch = 7FX THEN  sym := upto
        ELSE sym := null
        END ;
        Texts.Read(R, ch)
      END
    UNTIL sym # null
  END Get;

  (* begin-section-description
## ---------- Initialization
  end-section-description *)

  (*instruction assemblers according to formats*)

  (* begin-procedure-description
---
**Init** opens the source text for reading and gets the first character.
  end-procedure-description *)
  PROCEDURE Init*(T: Texts.Text; pos: LONGINT; a,b,c: INTEGER);
  BEGIN ccARCH := a; ccWordsize := b; ccStackalign := c; 
        errpos := pos; errcnt := 0; 
        Texts.OpenReader(R, T, pos); 
        Texts.Read(R, ch)
  END Init;

  (* begin-procedure-description
---
**EnterKW** adds a symbol to the keyword table.
  end-procedure-description *)
  PROCEDURE EnterKW*(sym: INTEGER; name: ARRAY OF CHAR; kl: INTEGER);
  VAR i:INTEGER;
  BEGIN
    IF sym > -1 THEN 
      keyTab[k].id := name; keyTab[k].sym := sym; INC(k); 
    END;
    KWX[kl] := k;
  END EnterKW;

  (* begin-procedure-description
---
**The initialzation code for this module** populats the table of reserved keywords.
  end-procedure-description *)
BEGIN Texts.OpenWriter(W); k := 0; KWX[0]:=0; KWX[1]:=0; 
(*
  EnterKW(if, "IF",2);
  EnterKW(do, "DO",2);
  EnterKW(of, "OF",2);
  EnterKW(or, "OR",2);
  EnterKW(to, "TO",2);
  EnterKW(in, "IN",2);
  EnterKW(is, "IS",2);
  EnterKW(by, "BY",2);
  EnterKW(end, "END",3);
  EnterKW(nil, "NIL",3);
  EnterKW(var, "VAR",3);
  EnterKW(div, "DIV",3);
  EnterKW(mod, "MOD",3);
  EnterKW(for, "FOR",3);
  EnterKW(else, "ELSE",4);
  EnterKW(then, "THEN",4);
  EnterKW(true, "TRUE",4);
  EnterKW(type, "TYPE",4);
  EnterKW(case, "CASE",4);
  EnterKW(elsif, "ELSIF",5);
  EnterKW(false, "FALSE",5);
  EnterKW(array, "ARRAY",5);
  EnterKW(begin, "BEGIN",5);
  EnterKW(const, "CONST",5);
  EnterKW(until, "UNTIL",5);
  EnterKW(while, "WHILE",5);
  EnterKW(record, "RECORD",6);
  EnterKW(repeat, "REPEAT",6);
  EnterKW(return, "RETURN",6);
  EnterKW(import, "IMPORT",6);
  EnterKW(module, "MODULE",6);
  EnterKW(pointer, "POINTER",7);
  EnterKW(notasymbol, "",8); 
  EnterKW(procedure, "PROCEDURE",9);
*)
END OXS.
