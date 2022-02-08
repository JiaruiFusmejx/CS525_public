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
    | "%" =>
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
    | "=" =>
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
(* ****** ****** *)
(*
//
// HX: 20 points
// Please implement a term
// that test whether a given
// natural number is a prime
// You should use the typechecker
// implemented in Assign03 to
// type-check this implementation
// of 'isprime'.
//
fun
isprime(x: int): bool =
(
if x >= 2 then test(2) else false
) where
{
fun
test(i: int): bool =
if
i < x
then
(if x % i = 0 then false else test(i+1))
else true
}
//
*)


extern
val TMisprime : term0


extern
fun 
T0Madd(T1: term0, T2: term0): term0

implement
T0Madd(T1, T2) = T0Mopr("+", T1:: T2 :: nil() )

extern
fun 
T0Mige(T1: term0, T2: term0): term0

implement
T0Mige(T1, T2) = T0Mopr(">=", T1:: T2 :: nil() )

extern
fun 
T0Milt(T1: term0, T2: term0): term0

implement
T0Milt(T1, T2) = T0Mopr("<", T1:: T2 :: nil() )

extern
fun 
T0Mmod(T1: term0, T2: term0): term0

implement
T0Mmod(T1, T2) = T0Mopr("%", T1:: T2 :: nil() )

extern
fun 
T0Mequ(T1: term0, T2: term0): term0

implement
T0Mequ(T1, T2) = T0Mopr("=", T1:: T2 :: nil() )

val T0Pint = T0Pbas("int")
val T0Pbtf = T0Pbas("bool")


local
val x = T0Mvar("x")
val i = T0Mvar("i")
val f = T0Mvar("f")


in
val test = T0Mfix("f", T0Pfun(T0Pint, T0Pbtf), T0Mlam("i", T0Pint, 
      T0Mifb(
        //if
        T0Milt(i, x), (**T0Mint(3) should be x**)
        //then
        T0Mifb(
          //if
          T0Mequ(T0Mmod(x, i), T0Mint(0)), (*same here*)
          //then
          T0Mbtf(false),
          //else
          T0Mapp(f, T0Madd(i, T0Mint(1)))
        ),
        //else
        T0Mbtf(true)
      )
    )
    )

//val () = println!("printing type check: ")
//val tc_test = term0_teval0(test) // this will not work here, since test has unbounded var x
//val () = println!("printing type check: ", tc_test)

  implement TMisprime =
  T0Mlam("x", T0Pint, T0Mifb(
    //if
    T0Mige(x, T0Mint(2)),
    //then
    (*T0Mbtf(false),*)
    
    
    T0Mapp(test, T0Mint(2)),
    //else
    T0Mbtf(false)
  )


  )

end

val tc_result = term0_teval0(TMisprime)
val () = println!("printing type check of TMisprime, expecting int->bool: ", tc_result)



//
// The term essentially encodes 'isprime'
//
(* ****** ****** *)
(*
//
// HX: 20 points
// Please implement 'isprime' in C using
// the boxed data representation covered
// in the lectures on 10/27 and 10/29.
//
*)
(* ****** ****** *)




(* end of [assign04_sol.dats] *)


implement main0() = println!("")
