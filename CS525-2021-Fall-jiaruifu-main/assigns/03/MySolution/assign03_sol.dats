(* ****** ****** *)
#include
"share/atspre_staload.hats"
(* ****** ****** *)
//
#include
"./../../../mylib/mylib.dats"
//
#include
"./../lambda0.dats"
//
(*
#include
"./../../mylib2/mylib2.dats"
*)
//
(* ****** ****** *)
//
// Total points: 100 points
//


extern
fun
print_type0: (type0) -> void
extern
fun
fprint_type0
(out: FILEref, typ: type0): void

overload print with print_type0
overload fprint with fprint_type0

implement
print_type0(typ) =
fprint_type0(stdout_ref, typ)
implement
fprint_type0(out, typ) =
(
case+ typ of
//
| T0Pbas(tnm) =>
  fprint!(out, "T0Pbas(", tnm, ")")
| T0Pfun(T1, T2) =>
  fprint!(out, "T0Pfun(", T1, "; ", T2, ")")
| T0Ptup(ts) =>
    let val () = fprint!(out, "T0Ptup(")
    in
      let fun loop(xs: mylist(type0)) : void =
        case+ xs of
        | mylist_nil() => fprint!(out, ")")
        | mylist_cons(x, xss) => 
          let val () = fprint!(out, x, ", ")
          in loop(xss)
          end
      in loop(ts)
      end
    end
)

(******************  starting implementation of print_term0 and fprint  ********************)

implement
print_term0(trm) =
fprint_term0(stdout_ref, trm)
implement
fprint_term0(out, trm) =
(
case- trm of
//
| T0Mint(i0) =>
  fprint!(out, "T0Mint(", i0, ")")
| T0Mbtf(b0) =>
  fprint!(out, "T0Mbtf(", b0, ")")
//
| T0Mvar(x0) =>
  fprint!(out, "T0Mvar(", x0, ")")
| T0Mlam(x1, T1, t2) =>
  fprint!(out, "T0Mlam(", x1, "; ", T1, "; ", t2, ")")
| T0Mapp(t1, t2) =>
  fprint!(out, "T0Mapp(", t1, "; ", t2, ")")
//
| T0Mfix(f1, T1, t2) =>
  fprint!(out, "T0Mlam(", f1, "; ", T1, "; ", t2, ")")
//
| T0Mopr(nm, ts) =>
  let val () = fprint!(out, "T0Mopr(", nm, "; (")
  in
    let fun loop(xs: mylist(term0)) : void =
      case+ xs of
        | mylist_nil() => fprint!(out, ")")
        | mylist_cons(x, xss) => 
          let val () = fprint!(out, x, ", ")
          in loop(xss)
          end
    in loop(ts)
    end
  end
  (*fprint!(out, "T0Mopr(", nm, "; ", "...", ")") *)
//
| T0Mifb(t1, t2, t3) =>
  fprint!(out, "T0Mifb(", t1, "; ", t2, "; ", t3, ")")
//
| T0Mtup(ts) => 
  let val () = fprint!(out, "T0Mtup(")
    in
      let fun loop(xs: mylist(term0)) : void =
        case+ xs of
        | mylist_nil() => fprint!(out, ")")
        | mylist_cons(x, xss) => 
          let val () = fprint!(out, x, ", ")
          in loop(xss)
          end
      in loop(ts)
      end
    end
//
| T0Msel(t1, t2) =>
  fprint!(out, "T0Msel(", t1, "; ", t2, ")") 
)

(** END of print functions**)

extern
fun
tvar0_teval1
( x0: tvar0
, ctx0: tctx0): myoptn(type0)

implement
tvar0_teval1
(x0, ctx0) =
(
case+ ctx0 of
| CTXnil() => myoptn_nil()
| CTXcons
  (x1, T1, ctx1) =>
  if (x0 = x1)
  then myoptn_cons(T1)
  else tvar0_teval1(x0, ctx1)
)

extern
fun
type0_equal
(T1: type0, T2: type0): bool


implement
type0_equal(T1, T2) = 
(
  case- (T1, T2) of
| (T0Pbas(x1), T0Pbas(x2)) => if (x1 = x2)
                              then true
                              else false
                              
| (T0Pfun(x1, x2), T0Pfun(x3,x4)) => if (type0_equal(x1,x3) && type0_equal(x2,x4))
                                      then true
                                      else false

                                    
| (T0Ptup(xs), T0Ptup(ys)) => let
                              fun helper(x: mylist(type0), y: mylist(type0)): bool=
                                case- (x,y) of
                                | (mylist_nil(), mylist_nil()) => true
                                
                                | ( mylist_cons(x1,xss) , mylist_cons(y1,yss) ) =>
                                
                                  if (type0_equal(x1,y1))
                                  then (true && helper(xss,yss))
                                  else false 
                                  
                                | (_,_) => false

                              in helper(xs, ys)
                              end
| (_, _) => false
)

(******* starting implementation of term0/1_teval *******)

val T0Pint = T0Pbas("int")
val T0Pbtf = T0Pbas("bool")


implement
term0_teval0(prgm) =
term0_teval1(prgm, CTXnil())

implement
term0_teval1
(trm0, ctx0) =
(
case+ trm0 of
//
| T0Mint(i0) => T0Pint
| T0Mbtf(b0) => T0Pbtf
//
| T0Mvar(x0) =>
  let
//
(*
  val () =
  println!
  ("term0_eval1: trm0 = ", trm0)
*)
//
  val opt =
  tvar0_teval1(x0, ctx0)
  in
    case- opt of
    | myoptn_cons(v0) => v0
  end
//
| T0Mlam(x0, T0, t1) =>
  let
    val ctx1 =
    CTXcons(x0, T0, ctx0)
    val T1 =
    term0_teval1(t1, ctx1)
  in
    T0Pfun(T0, T1)
  end
//
| T0Mapp(t1, t2) =>
  let
    val T1 =
    term0_teval1(t1, ctx0)
    val T2 =
    term0_teval1(t2, ctx0)
  in
    case- T1 of
    | T0Pfun(T11, T12) =>
      T12 where
      { val-true = type0_equal(T11, T2) }
  end
//
| T0Mfix(f0, T0, tdef) =>
  let
    val ctx1 =
    CTXcons(f0, T0, ctx0)
    val T1 = term0_teval1(tdef, ctx1)
  in
    T0 where { val- true = type0_equal(T0, T1) }
  end
//
| T0Mopr(nm, ts) =>
  let
    val Ts =
    mylist_map<term0><type0>
    (ts, lam(t1) => term0_teval1(t1, ctx0))
  in
    case+ nm of
    | "+" =>
      let
      val-
      mylist_cons(T1, Ts) = Ts
      val-
      mylist_cons(T2, Ts) = Ts
//
      val-true =
        type0_equal(T1, T0Pint)
      val-true =
        type0_equal(T2, T0Pint)
//
      in
        T0Pint
      end
    | "-" =>
      let
      val-
      mylist_cons(T1, Ts) = Ts
      val-
      mylist_cons(T2, Ts) = Ts
//
      val-true =
        type0_equal(T1, T0Pint)
      val-true =
        type0_equal(T2, T0Pint)
//
      in
        T0Pint
      end
    | "*" =>
      let
      val-
      mylist_cons(T1, Ts) = Ts
      val-
      mylist_cons(T2, Ts) = Ts
//
      val-true =
        type0_equal(T1, T0Pint)
      val-true =
        type0_equal(T2, T0Pint)
//
      in
        T0Pint
      end
    | "/" =>
      let
      val-
      mylist_cons(T1, Ts) = Ts
      val-
      mylist_cons(T2, Ts) = Ts
//
      val-true =
        type0_equal(T1, T0Pint)
      val-true =
        type0_equal(T2, T0Pint)
//
      in
        T0Pint
      end
    | ">" =>
      let
      val-
      mylist_cons(T1, Ts) = Ts
      val-
      mylist_cons(T2, Ts) = Ts
//
      val-true =
        type0_equal(T1, T0Pint)
      val-true =
        type0_equal(T2, T0Pint)
//
      in
        T0Pbtf
      end
    | ">=" =>
      let
      val-
      mylist_cons(T1, Ts) = Ts
      val-
      mylist_cons(T2, Ts) = Ts
//
      val-true =
        type0_equal(T1, T0Pint)
      val-true =
        type0_equal(T2, T0Pint)
//
      in
        T0Pbtf
      end
    | "<" =>
      let
      val-
      mylist_cons(T1, Ts) = Ts
      val-
      mylist_cons(T2, Ts) = Ts
//
      val-true =
        type0_equal(T1, T0Pint)
      val-true =
        type0_equal(T2, T0Pint)
//
      in
        T0Pbtf
      end
    | "<=" =>
      let
      val-
      mylist_cons(T1, Ts) = Ts
      val-
      mylist_cons(T2, Ts) = Ts
//
      val-true =
        type0_equal(T1, T0Pint)
      val-true =
        type0_equal(T2, T0Pint)
//
      in
        T0Pbtf
      end
    | _ (*unknown operator*) =>
      exit(1) where
      {
      val () = println!("term0_eval1: T0Mopr: nm = ", nm)
      }
  end
//
| T0Mifb(t1, t2, t3) =>
  let
    val T1 = term0_teval1(t1, ctx0)
    val-true = type0_equal(T1, T0Pbtf)
    val T2 = term0_teval1(t2, ctx0)
    val T3 = term0_teval1(t3, ctx0)
  in
    T2 where { val- true = type0_equal(T2, T3) }
  end
//
| T0Mtup(ts) => let fun loop(xs: mylist(term0)) : mylist(type0) =
                  case+ xs of
                  | mylist_nil() => mylist_nil()
                  | mylist_cons(x, xss) => 
                      let val xt = term0_teval1(x, ctx0)
                      in mylist_cons(xt, loop(xss))
                      end
                in T0Ptup(loop(ts))
                end

| T0Msel(t1, i0) =>
                    let 
                    val ttup = term0_teval1(t1, ctx0)
                    fun remove_wrapper(tup: type0): mylist(type0)=
                        case- tup of
                        | T0Ptup(ls) => ls
                    fun loop(xs: mylist(type0), counter: int): type0 =
                      case+ xs of
                        | mylist_nil() => (
                          if counter = 0 then 
                            exit(1) where
                            {
                              val () = println!("term0_teval1: T0Msel: empty tuple")
                            }
                          else
                            exit(1) where
                            {
                              val () = println!("term0_teval1: T0Msel: index out of bounds")
                            }
                        )
                        | mylist_cons(x1, xss) => if i0 = counter
                            then x1 else loop(xss, counter + 1)
                    in loop(remove_wrapper(ttup), 0)
                    end

)


//
(* ****** ****** *)

(* end of [assign03_sol.dats] *)


val 
tester = T0Mtup(T0Mint(0)::T0Mint(1)::T0Mint(2)::T0Mint(3)::T0Mint(4)::nil())

val () = println!("testing print_term with print_type0")
val () = println!("")
val testprint = T0Mlam("testlam", T0Pbas("testlam_type"), tester)
val () = print_term0(testprint)
val () = println!("")

val tester1 = type0_equal(T0Pint, T0Pint)
val tester2 = type0_equal(T0Pbtf, T0Pint)
val tester3 = T0Pfun(T0Pint, T0Pint)
val tester4 = T0Pfun(T0Pint, T0Pbtf)
val tester5 = type0_equal(tester3, tester3)
val tester6 = type0_equal(tester3, tester4)
val tester7 = T0Ptup(T0Pint::T0Pbtf::nil())
val tester8 = T0Ptup(T0Pint::T0Pint::T0Pint::nil())
val tester9 = type0_equal(tester7, tester7)
val tester10 = type0_equal(tester7, tester8)

val () = println!("Tester1, type0_equal T0Pint * 2, expected true: ",tester1)
val () = println!("Tester2, type0_equal btf vs int, expected false: ",tester2)
val () = println!("Tester5, type0_equal fun(int->int) * 2, expected true: ",tester5)
val () = println!("Tester6, type0_equal different fun, expected false: ",tester6)
val () = println!("Tester9, type0_equal identical tuple, expected true: ",tester9)
val () = println!("Tester10, type0_equal different tuple, expected false: ",tester10)

val tester11 = T0Mtup(T0Mint(0)::T0Mint(1)::T0Mbtf(true)::nil())
val tester12 = term0_teval0(tester11)
val tester13 = term0_teval0(T0Msel(tester11, 2))

val () = println!("Tester12, term_teval of tuple int::int::bool::nil: ", tester12)
val () = println!("Tester13, term_teval of sel index=2 of tuple int::int::bool::nil: ", tester13)

val tester14 = CTXcons("z", T0Pint, CTXnil())
val z = T0Mvar("z")
val zint = term0_teval1(z, tester14)
val () = println!("Test on teval1, expected result is T0Pbas(int): ", zint)

implement main0() = println!("")
