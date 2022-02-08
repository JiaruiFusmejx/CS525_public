(* ****** ****** *)
#include
"share/atspre_staload.hats"
(* ****** ****** *)
#include
"./../../../mylib/mylib.dats"
(**** ****)
#include
"./../lambda0.dats"

(* ****** ****** *)
//
// Total points: 120 points
//
(* ****** ****** *)


implement
print_tval0(tvl) =
fprint_tval0(stdout_ref, tvl)

implement
fprint_tval0(out, v0) =
(
case+ v0 of
| T0Vint(i0) =>
  fprintln!(out, "T0Vint(", i0, ")")
| T0Vbtf(b0) =>
  fprintln!(out, "T0Vbtf(", b0, ")")
| T0Vlam _ =>
  fprintln!(out, "T0Vlam(", "...", ")")
| T0Vfix _ =>
  fprintln!(out, "T0Vfix(", "...", ")")
| T0Vtup(ts) =>
    let val () = fprint!(out, "T0Vtup(")
    in
      let fun loop(xs: mylist(tval0)) : void =
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


(* ****** ****** *)



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
| T0Mlam(x1, t2) =>
  fprint!(out, "T0Mlam(", x1, "; ", t2, ")")
| T0Mapp(t1, t2) =>
  fprint!(out, "T0Mapp(", t1, "; ", t2, ")")
//
| T0Mfix(f1, t2) =>
  fprint!(out, "T0Mlam(", f1, "; ", t2, ")")
//
| T0Mopr(nm, ts) =>
  fprint!(out, "T0Mopr(", nm, "; ", "...", ")")
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



(* ****** ************************************************************ *)

(*
fun
tvar0_eval1
(x0: tvar0, env0: tenv0) : myoptn(tval0) =
(
case+ env0 of
| ENVnil() => myoptn_nil()
| ENVcons
  (x1, v1, env1) =>
  if (x0 = x1)
  then myoptn_cons(v1)
  else tvar0_eval1(x0, env1)
)
*)
fun
tvar0_eval1
(x0: tvar0, env0: tenv0) : myoptn(tval0) =
(
case+ env0 of
| ENVnil() => myoptn_nil()
| ENVcons
  (x1, v1, env1) =>
  if (x0 = x1)
  then myoptn_cons(v1)
  else tvar0_eval1(x0, env1)
)
(* ****** ****** *)



implement
term0_eval0(prgm) =
term0_eval1(prgm, ENVnil())

(********)



(********)

implement
term0_eval1
(trm0, env0) =
(
case+ trm0 of
//
| T0Mint(i0) => T0Vint(i0)
| T0Mbtf(b0) => T0Vbtf(b0)
//
| T0Mvar(x0) =>
  let
    val opt =
    tvar0_eval1(x0, env0)
  in
    case- opt of
    | myoptn_cons(v0) => v0
  end
//
| T0Mlam(x0, t1) => T0Vlam(trm0, env0)
//
| T0Mapp(t1, t2) =>
  let
    val v1 = term0_eval1(t1, env0)
    val v2 = term0_eval1(t2, env0)
  in
    case- v1 of
    | T0Vlam(tlam, env1) =>
      let
        val-
        T0Mlam(x1, t1bd) = tlam
      in
        term0_eval1(t1bd, ENVcons(x1, v2, env1))
      end
    | T0Vfix(tfix, env1) =>
      let
        val-
        T0Mfix(f1, tdef) = tfix
        val-
        T0Mlam(x1, t1bd) = tdef
      in
        term0_eval1
        (t1bd, ENVcons(x1, v2, ENVcons(f1, v1, env1)))
      end
  end
//
| T0Mfix(f1, tdef) =>
  T0Vlam(tdef, ENVcons(f1, T0Vfix(trm0, env0), env0))
//
| T0Mopr(nm, ts) =>
  let
    val vs =
    mylist_map<term0><tval0>
    (ts, lam(t1) => term0_eval1(t1, env0))
  in
    case+ nm of
    | "+" =>
      let
      val-
      mylist_cons(T0Vint(i1), vs) = vs
      val-
      mylist_cons(T0Vint(i2), vs) = vs
      in
        T0Vint(i1+i2)
      end
    | "-" =>
      let
      val-
      mylist_cons(T0Vint(i1), vs) = vs
      val-
      mylist_cons(T0Vint(i2), vs) = vs
      in
        T0Vint(i1-i2)
      end
    | "*" =>
      let
      val-
      mylist_cons(T0Vint(i1), vs) = vs
      val-
      mylist_cons(T0Vint(i2), vs) = vs
      in
        T0Vint(i1*i2)
      end
    | "/" =>
      let
      val-
      mylist_cons(T0Vint(i1), vs) = vs
      val-
      mylist_cons(T0Vint(i2), vs) = vs
      in
        T0Vint(i1/i2)
      end
    | ">" =>
      let
      val-
      mylist_cons(T0Vint(i1), vs) = vs
      val-
      mylist_cons(T0Vint(i2), vs) = vs
      in
        T0Vbtf(i1 > i2)
      end
    | ">=" =>
      let
      val-
      mylist_cons(T0Vint(i1), vs) = vs
      val-
      mylist_cons(T0Vint(i2), vs) = vs
      in
        T0Vbtf(i1 >= i2)
      end
    | "<" =>
      let
      val-
      mylist_cons(T0Vint(i1), vs) = vs
      val-
      mylist_cons(T0Vint(i2), vs) = vs
      in
        T0Vbtf(i1 < i2)
      end
    | "<=" =>
      let
      val-
      mylist_cons(T0Vint(i1), vs) = vs
      val-
      mylist_cons(T0Vint(i2), vs) = vs
      in
        T0Vbtf(i1 <= i2)
      end
    | _ (*unknown operator*) =>
      exit(1) where
      {
      val () = println!("term0_eval1: T0Mopr: nm = ", nm, "unknown")
      }
      (*kept since its case + and there is the possibility of invalid operators*)
  end
  //
  | T0Mifb(t1, t2, t3) =>
  let
    val v1 = term0_eval1(t1, env0)
  in
    case- v1 of
    | T0Vbtf(b0) =>
      if b0 then term0_eval1(t2, env0) else term0_eval1(t3, env0)
  end
//
| T0Mtup(ts) => 
    let fun looper(xs: mylist(term0)) : mylist(tval0) =
      case+ xs of
      | mylist_nil() => mylist_nil
      | mylist_cons(x, xss) => (
          let 
            val tv1 = term0_eval1(x, env0)
          in
            mylist_cons(tv1, looper(xss))
          end
      )
    in
    T0Vtup(looper(ts))
    end
  
//
| T0Msel(t1, t2) =>
  let 
    val v1 = term0_eval1(t1, env0)
    val v2 = term0_eval1(t2, env0)
  in 
    case- v2 of
    |T0Vint(i0) => (
      case- v1 of
      | T0Vtup(ts) => (
        let fun loop(xs: mylist(tval0), i1: int) : tval0 =
          case+ xs of
          | mylist_nil() => (
            if i1 = 0 then 
              exit(1) where
              {
                val () = println!("term0_eval1: T0Msel: empty tuple")
              }
            else
              exit(1) where
              {
                val () = println!("term0_eval1: T0Msel: index out of bounds")
              }
          )
          | mylist_cons(x1, xss) => if i0 = i1
            then x1 else loop(xss, i1 + 1)
        in loop(ts, 0)
        end
      )
      | _ => exit(1) where
              {
                val () = println!("term0_eval1: T0Msel: term 1 not a tuple")
              }
    )
    | _ => exit(1) where
              {
                val () = println!("term0_eval1: T0Msel: term 2 not a int")
              }
  end
)

//
(* ****** ****** *)
//
// HX-2021-10-16: 10 points
// Please construct a term0-value that
// encodes a tail-recursive implementation
// of the factorial function.
//
(*extern val term0_fact_trec: term0*)
(*
Reference from previous tfact
T0Mfix("f", T0Mlam("x", T0Mifb(T0Migt(x, T0Mint(0)), T0Mmul(x, T0Mapp(f, T0Madd(x, T0Mint(~1)))), T0Mint(1))))

*)

local
val x = T0Mvar("x")
val f = T0Mvar("f")
in 
  implement
  term0_fact_trec =
    T0Mfix( "f",
      T0Mlam("x", 
        T0Mifb(
          //if
            T0Mopr(">", T0Msel(x, T0Mint(0)) :: T0Mint(1) :: nil()),
          //then
            T0Mapp(f, T0Mtup(
              T0Mopr("-", T0Msel(x, T0Mint(0)):: T0Mint(1) :: nil() )  :: T0Mopr("*", T0Msel(x, T0Mint(0)):: T0Msel(x, T0Mint(1)) :: nil() ) :: nil()
            )),
          //else
            T0Msel(x, T0Mint(1))
        )
      )
    )
end
(* attempt on eliminating tuple-ing helper function from tail recursion factorial
   let
      val t = T0Mlam("x", x)
      //val y = T0Mtup(mylist_cons( T0Mint(t) , mylist_cons(T0Mint(1),mylist_nil())))
    in
      print_term0(t)
    end
*)
//
(* ****** ****** *)
//
// HX-2021-10-16: 10 points
// Please construct a term0-value that
// encodes an implemenation of the so-called
// map function on a tuple.
// For instance, given (1, 2, 3) and the function
// lam x => x*x, this map function returns
// (1, 4, 9)
//
(*extern val term0_tuple_map: term0*)
//
(* ****** ****** *)

val x = T0Mtup(
    mylist_cons(
        T0Mint(10),
        mylist_cons(
            T0Mint(1),
            mylist_nil()
        ) 
    )
)
val
tfac10_abs =
T0Mapp(
    term0_fact_trec, x
)
val
tfac_val = term0_eval0(tfac10_abs)

val 
tester1 = T0Mtup(T0Mint(0)::T0Mint(1)::T0Mint(2)::T0Mint(3)::T0Mint(4)::nil())
val () = print_term0(tester1)
val () = println!("printing tuple of 0-4")
val 
tester2 = T0Msel(tester1, T0Mint(3))

val 
tester3 = T0Msel(tester1, T0Mint(4))

val 
tester4 = T0Msel(tester1, T0Mint(5))

val () = print_term0(tester2)
val () = println!("testing print_term0 on sel")
val () = print_term0(tester3)
val () = println!("testing print_term0 on sel")
val () = print_term0(tester4)
val () = println!("testing print_term0 on sel")

val () = print_tval0(term0_eval0(tester2))
val () = println!("testing print_tval0 & eval0 on sel expected output above is 3")

val () = print_tval0(term0_eval0(tester3))
val () = println!("expected output above is 4")
(*
val () = print_tval0(term0_eval0(tester4))
val () = println!("expected output above index out of bounds")
//prints the expected error message but also aborts the program
*)
val testenv = ENVcons("z", T0Vint(12), ENVnil())
val z = T0Mvar("z")
val z12 = term0_eval1(z, testenv)
val () = print_tval0(z12)
val () = println!("testing eval1, expected output above is T0Vint(12)")

//print_term0(trm)
implement main0() = 
println!("term0_factorial(10) = ",  tfac_val)
(* end of [lambda0.dats] *)
