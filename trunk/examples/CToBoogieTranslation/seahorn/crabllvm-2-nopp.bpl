implementation ULTIMATE.init() returns (){
    ~x := 5bv32;
    ~y := 3bv32;
    ~a[0bv32] := 0bv32;
    ~a[1bv32] := 0bv32;
    ~a[2bv32] := 0bv32;
    ~a[3bv32] := 0bv32;
    ~a[4bv32] := 0bv32;
    ~a[5bv32] := 0bv32;
    ~a[6bv32] := 0bv32;
    ~a[7bv32] := 0bv32;
    ~a[8bv32] := 0bv32;
    ~a[9bv32] := 0bv32;
}

implementation ULTIMATE.start() returns (){
    var #t~ret4 : C_INT;

    call ULTIMATE.init();
    call #t~ret4 := main();
}

type { :isUnsigned false } { :bitsize 8 } C_CHAR = bv8;
type { :isUnsigned false } { :bitsize 8 } C_SCHAR = bv8;
type { :isUnsigned true } { :bitsize 8 } C_UCHAR = bv8;
type { :isUnsigned false } { :bitsize 16 } C_SHORT = bv16;
type { :isUnsigned true } { :bitsize 16 } C_USHORT = bv16;
type { :isUnsigned false } { :bitsize 32 } C_INT = bv32;
type { :isUnsigned true } { :bitsize 32 } C_UINT = bv32;
type { :isUnsigned false } { :bitsize 64 } C_LONG = bv64;
type { :isUnsigned true } { :bitsize 64 } C_ULONG = bv64;
type { :isUnsigned false } { :bitsize 64 } C_LONGLONG = bv64;
type { :isUnsigned true } { :bitsize 64 } C_ULONGLONG = bv64;
type { :isUnsigned true } { :bitsize 8 } C_BOOL = bv8;
implementation foo() returns (){
    var #t~post0 : C_INT;

    #t~post0 := ~x;
    ~x := ~bvadd32(#t~post0, 1bv32);
    havoc #t~post0;
}

implementation bar() returns (){
    var #t~post1 : C_INT;

    #t~post1 := ~y;
    ~y := ~bvadd32(#t~post1, 1bv32);
    havoc #t~post1;
}

implementation main() returns (#res : C_INT){
    var #t~ret3 : C_INT;
    var #t~post2 : C_INT;
    var ~i~4 : C_INT;
    var ~res~4 : C_INT;

    havoc ~i~4;
    call foo();
    ~i~4 := 0bv32;
    while (true)
    {
        if (!~bvslt32(~i~4, 10bv32)) {
            break;
        }
        call #t~ret3 := nd();
        if (#t~ret3 != 0bv32) {
            havoc #t~ret3;
            ~a[~i~4] := ~y;
        } else {
            havoc #t~ret3;
            ~a[~i~4] := ~x;
        }
      Loop~0:
        #t~post2 := ~i~4;
        ~i~4 := ~bvadd32(#t~post2, 1bv32);
        havoc #t~post2;
    }
    call bar();
    ~res~4 := ~a[~bvsub32(~i~4, 1bv32)];
    assert ~bvsge32(~res~4, 0bv32) && ~bvsle32(~res~4, 6bv32);
    #res := ~res~4;
    return;
}

var ~x : C_INT;

var ~y : C_INT;

var ~a : [C_INT]C_INT;

type $Pointer$ = { base : C_INT, offset : C_INT };
procedure nd() returns (#res : C_INT);
modifies ;

procedure foo() returns ();
modifies ~x;

procedure bar() returns ();
modifies ~y;

procedure main() returns (#res : C_INT);
modifies ~a, ~x, ~y;

procedure ULTIMATE.init() returns ();
modifies ~x, ~y, ~a;
modifies ;

procedure ULTIMATE.start() returns ();
modifies ~x, ~y, ~a, ~a;
modifies ~x, ~y, ~a;

function { :builtin "bvadd" } ~bvadd32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
function { :builtin "bvslt" } ~bvslt32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvsub" } ~bvsub32(in0 : C_INT, in1 : C_INT) returns (out : C_INT);
function { :builtin "bvsge" } ~bvsge32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvsle" } ~bvsle32(in0 : C_INT, in1 : C_INT) returns (out : bool);
function { :builtin "bvadd" } ~bvadd8(in0 : C_CHAR, in1 : C_CHAR) returns (out : C_CHAR);
function { :builtin "bvadd" } ~bvadd16(in0 : C_SHORT, in1 : C_SHORT) returns (out : C_SHORT);
function { :builtin "bvadd" } ~bvadd64(in0 : C_LONG, in1 : C_LONG) returns (out : C_LONG);
