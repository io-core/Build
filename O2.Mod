MODULE O2;   (*CP 2020*)
  IMPORT Texts, Oberon;

  TYPE 
       I* = POINTER TO IDesc;
       IDesc* = RECORD
            h: INTEGER
       END ;

       R* = POINTER TO RDesc;
       RDesc* = RECORD
            h: REAL
       END ;

       C* = POINTER TO CDesc;
       CDesc* = RECORD
            h: INTEGER
       END ;

       D* = POINTER TO DDesc;
       DDesc* = RECORD
            h: REAL
       END ;

       Stringer* = INTERFACE OF
            PROCEDURE Nop* () ;
            PROCEDURE String* (VAR a: ARRAY OF CHAR) ; 
       END ;

       FooBarer* = INTERFACE OF
            PROCEDURE Foo* (VAR f: ARRAY OF CHAR) ; 
            PROCEDURE Bar* (VAR f: ARRAY OF CHAR) ; 
       END ;

       Empty* = RECORD
       END ;

  VAR W: Texts.Writer;

  PROCEDURE ( i : I ) Nop* () ;
  BEGIN
  END Nop;

  PROCEDURE ( r : R ) Nop* () ;
  BEGIN
  END Nop;
 
  PROCEDURE ( i : I ) String* (VAR a: ARRAY OF CHAR) ;
  BEGIN a := "integer"
  END String;

  PROCEDURE ( r : R ) String* (VAR a: ARRAY OF CHAR) ;
  BEGIN a := "real"
  END String;
 
  PROCEDURE ( c : C ) Foo* (VAR a: ARRAY OF CHAR) ;
  BEGIN a := "iFoo"
  END Foo;

  PROCEDURE ( c : C ) Bar* (VAR a: ARRAY OF CHAR) ;
  BEGIN a := "iBar"
  END Bar;

  PROCEDURE ( d : D ) Foo* (VAR a: ARRAY OF CHAR) ;
  BEGIN a := "rFoo"
  END Foo;
 
  PROCEDURE ( d : D ) Bar* (VAR a: ARRAY OF CHAR) ;
  BEGIN a := "rBar"
  END Bar;
 
  PROCEDURE Test*;
      VAR i: I; r: R; c: C; d: D; t: ARRAY 32 OF CHAR; 
        s,s2: Stringer; f: FooBarer;
        x0, x1, u: REAL;
        S: Texts.Scanner;
  BEGIN Texts.OpenScanner(S, Oberon.Par.text, Oberon.Par.pos); Texts.Scan(S);
    IF (S.class = Texts.Int) & (S.i > 0) THEN
      NEW(i); NEW(r); NEW(c); NEW(d);
      
     

      Texts.WriteString(W, "O2 Test Start");
      Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf);
      i.h := 0;
      r.h := 0.0;
      c.h := 0;
      d.h := 0.0;

      s:=s2;

      i.String( t ); Texts.WriteString(W,t); Texts.WriteLn(W); 
      r.String( t ); Texts.WriteString(W,t); Texts.WriteLn(W); 
      c.Foo( t ); Texts.WriteString(W,t); Texts.WriteLn(W);
      d.Foo( t ); Texts.WriteString(W,t); Texts.WriteLn(W);
      c.Bar( t ); Texts.WriteString(W,t); Texts.WriteLn(W);
      d.Bar( t ); Texts.WriteString(W,t); Texts.WriteLn(W);


      s := i; (*  s.Nop();    s.String( t );  *)
      s := r;
      f := c;
      f := d;


      Texts.WriteString(W, "O2 Test End");
      Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf);
    END
  END Test;

BEGIN Texts.OpenWriter(W)
END O2.

