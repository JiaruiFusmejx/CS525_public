(* ****** ****** *)
(*
Due:
Wednesday
the 6th of October
*)
(* ****** ****** *)
#staload "./lambda0.sats"
(* ****** ****** *)
#include
"share/atspre_staload.hats"
(* ****** ****** *)
#staload "./../../../mylib/mylib.dats"
(* ****** ****** *)
//
// Please finish
// the implementation of
// of the function term0_fvset
//
(*
Note that you need to implement
mylist_append and mylist_remove
If you are not clear about what
these functions are supposed to do,
please ask your questions on Piazza
*)
//
(* ****** ****** *)

implement
{tvar0}
mylist_sing(x0) =
mylist_cons(x0, mylist_nil())

(* ****** ****** *)

implement
{tvar0}
mylist_append(xs, ys) =
mylist_rappend<tvar0>
(mylist_reverse<tvar0>(xs), ys)

(* ****** ****** *)

implement
{tvar0}
mylist_reverse(xs) =
mylist_rappend<tvar0>(xs, mylist_nil())

(* ****** ****** *)

implement
{tvar0}
mylist_rappend(xs, ys) =
case+ xs of
|
mylist_nil() => ys
|
mylist_cons(x1, xs) =>
mylist_rappend<tvar0>(xs, mylist_cons(x1, ys))

(* ****** ****** *)


implement
{tvar0}
mylist_remove(xs, x0) =
let 
fun 
helper(xs: mylist(tvar0)): mylist(tvar0)=
(
  case+ xs of
  | mylist_nil() => mylist_nil()
  | mylist_cons(x1, xs) => if geq_val_val<tvar0>(x0, x1) then helper(xs) else mylist_cons(x1, helper(xs))
)
in
helper(xs)
end

extern
fun
term0_fvset(t0: term0): mylist(tvar0)
(*
HX: 20 points
*)

implement
term0_fvset(t0) =
(
case+ t0 of
| T0Mint _ =>
  mylist_nil()
| T0Mbtf _ =>
  mylist_nil()
//
| T0Mvar(x0) =>
  mylist_sing(x0)
| T0Mapp(t1, t2) =>
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
| T0Mlam(x0, t1) =>
  mylist_remove(term0_fvset(t1), x0)
//
| T0Mneg(t1) => 
  term0_fvset(t1)
| T0Madd(t1, t2) => 
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
| T0Msub(t1, t2) => 
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
| T0Mmul(t1, t2) => 
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
| T0Mdiv(t1, t2) => 
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
//
| T0Milt(t1, t2) => 
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
| T0Mile(t1, t2) => 
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
| T0Migt(t1, t2) => 
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
| T0Mige(t1, t2) => 
  mylist_append
  (term0_fvset(t1), term0_fvset(t2))
//
| T0Mifb(t1, t2, t3) =>
  mylist_append
  (term0_fvset(t1),
   mylist_append
   (term0_fvset(t2), term0_fvset(t3))
  )
//
| T0Mfix(x0, t1) =>
  mylist_remove(term0_fvset(t1), x0)
)

//mylist_append(mylist_sing(x0), term0_fvset(t1))
(* ****** ****** *)

(*
//
HX: 10 points
Please construct a term in LAMBDA0 that
computes the following function fibo:
//
fun
fibo(n: int): int =
if n >= 2 then fibo(n-1)+fibo(n-2) else n
//
*)
extern
val tfibo : term0 // See [tfact] as an example

local
val x = T0Mvar("x")
val f = T0Mvar("f")
in
val tfibo = T0Mfix("f", T0Mlam("x", T0Mifb( T0Mige(x, T0Mint(2)),T0Madd(T0Mapp(f, T0Madd(x, T0Mint(~1))), T0Mapp(f, T0Madd(x, T0Mint(~2))) ),x)))
end
(* ****** ****** *)
//
(*
HX: 70 points
//
please
implement an interpreter for LAMBDA0
//
fun term0_interp(prgm: term0): term0
//
Note that term0_interp is the same as
term0_eval given during lectures. This problem
asks you to read the code of term0_eval and use
it (mostly, copy/paste it) to implement term0_interp
//
*)

extern
fun
term0_subst
( t0: term0
, x0: tvar0, sub: term0): term0

implement
term0_subst
(t0, x0, sub) =
(
case+ t0 of
//
| T0Mint _ => t0
//
| T0Mneg(t1) =>
  T0Mneg(t1) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
  }
| T0Madd(t1, t2) =>
  T0Madd(t1, t2) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
    val t2 =
    term0_subst(t2, x0, sub)
  }
| T0Msub(t1, t2) =>
  T0Msub(t1, t2) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
    val t2 =
    term0_subst(t2, x0, sub)
  }
| T0Mmul(t1, t2) =>
  T0Mmul(t1, t2) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
    val t2 =
    term0_subst(t2, x0, sub)
  }
| T0Mdiv(t1, t2) =>
  T0Mdiv(t1, t2) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
    val t2 =
    term0_subst(t2, x0, sub)
  }
//
| T0Milt(t1, t2) =>
  T0Milt(t1, t2) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
    val t2 =
    term0_subst(t2, x0, sub)
  }
| T0Mile(t1, t2) =>
  T0Mile(t1, t2) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
    val t2 =
    term0_subst(t2, x0, sub)
  }
| T0Migt(t1, t2) =>
  T0Migt(t1, t2) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
    val t2 =
    term0_subst(t2, x0, sub)
  }
| T0Mige(t1, t2) =>
  T0Mige(t1, t2) where
  {
    val t1 =
    term0_subst(t1, x0, sub)
    val t2 =
    term0_subst(t2, x0, sub)
  }
//
| T0Mbtf _ => t0
| T0Mvar(x1) =>
  if x0 = x1 then sub else t0
| T0Mlam(x1, t2) =>
  if x0 = x1
  then t0 else T0Mlam(x1, term0_subst(t2, x0, sub))
| T0Mapp(t1, t2) =>
  T0Mapp(term0_subst(t1, x0, sub), term0_subst(t2, x0, sub))
//
| T0Mfix(f1, t2) =>
  if x0 = f1
  then t0 else T0Mfix(f1, term0_subst(t2, x0, sub))
//
| T0Mifb(t1, t2, t3) =>
  T0Mifb(term0_subst(t1, x0, sub), term0_subst(t2, x0, sub), term0_subst(t3, x0, sub))
)


//decleration of term0_interp and corresponding functions
extern
fun
term0_interp(prgm: term0): term0
extern
fun
term0_interp_app(prgm: term0): term0
extern
fun
term0_interp_fix(prgm: term0): term0

(* ****** ****** *)
implement
term0_interp(t0) =
(
case+ t0 of
| T0Mint _ => t0
//
| T0Mneg(t1) =>
(
  T0Mint(~i1)
) where
{
    val t1 =
    term0_interp(t1)
    val- T0Mint(i1) = t1
}
| T0Madd(t1, t2) =>
  let
    val t1 =
    term0_interp(t1)
    val t2 =
    term0_interp(t2)
    val- T0Mint(i1) = t1
    val- T0Mint(i2) = t2
  in
    T0Mint(i1 + i2)
  end
| T0Msub(t1, t2) =>
  let
    val t1 =
    term0_interp(t1)
    val t2 =
    term0_interp(t2)
    val- T0Mint(i1) = t1
    val- T0Mint(i2) = t2
  in
    T0Mint(i1 - i2)
  end
| T0Mmul(t1, t2) =>
  let
    val t1 =
    term0_interp(t1)
    val t2 =
    term0_interp(t2)
    val- T0Mint(i1) = t1
    val- T0Mint(i2) = t2
  in
    T0Mint(i1 * i2)
  end
| T0Mdiv(t1, t2) =>
  let
    val t1 =
    term0_interp(t1)
    val t2 =
    term0_interp(t2)
    val- T0Mint(i1) = t1
    val- T0Mint(i2) = t2
  in
    T0Mint(i1 / i2)
  end
//
| T0Mbtf _ => t0
| T0Mvar _ => t0
//
| T0Milt(t1, t2) =>
  let
    val t1 =
    term0_interp(t1)
    val t2 =
    term0_interp(t2)
    val- T0Mint(i1) = t1
    val- T0Mint(i2) = t2
  in
    T0Mbtf(i1 < i2)
  end
| T0Mile(t1, t2) =>
  let
    val t1 =
    term0_interp(t1)
    val t2 =
    term0_interp(t2)
    val- T0Mint(i1) = t1
    val- T0Mint(i2) = t2
  in
    T0Mbtf(i1 <= i2)
  end
| T0Migt(t1, t2) =>
  let
    val t1 =
    term0_interp(t1)
    val t2 =
    term0_interp(t2)
    val- T0Mint(i1) = t1
    val- T0Mint(i2) = t2
  in
    T0Mbtf(i1 > i2)
  end
| T0Mige(t1, t2) =>
  let
    val t1 =
    term0_interp(t1)
    val t2 =
    term0_interp(t2)
    val- T0Mint(i1) = t1
    val- T0Mint(i2) = t2
  in
    T0Mbtf(i1 >= i2)
  end
//
| T0Mlam _ => t0
//
| T0Mapp _ =>
  term0_interp_app(t0)
//
| T0Mfix _ =>
  term0_interp_fix(t0)
//
| T0Mifb(t1, t2, t3) =>
  let
  val t1 = term0_interp(t1)
  in
    case- t1 of
    | T0Mbtf(tf) =>
      if tf then term0_interp(t2)
            else term0_interp(t3)
  end
//
)
(* ****** ****** *)

implement
term0_interp_app(tapp) =
let
val-
T0Mapp(t1, t2) = tapp
//
val t1 = term0_interp(t1) // fun
val t2 = term0_interp(t2) // arg
//
in
case- t1 of
| T0Mlam(x1, body) =>
  term0_interp(term0_subst(body, x1, t2))
end
(* ****** ****** *)

implement
term0_interp_fix(tfix) =
let
val-
T0Mfix(f1, t2) = tfix
in
term0_interp(term0_subst(t2, f1, tfix))
end


//
(* ****** ****** *)
implement main0() = ()


(* end of [assign01.dats] *)
