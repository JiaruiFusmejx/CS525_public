(* ****** ****** *)
//
#include
"./../lambda2.dats"
//
(* ****** ****** *)
#dynload
"./../lambda1.dats"
(* ****** ****** *)
implement
main0() = ((*dummy*))
(* ****** ****** *)

typedef stamp = int

(* ****** ****** *)

local

assume
t2var_type =
ref@{
t2var_t1var= t1var
,
t2var_t1ype= t1ype
,
t2var_stamp= stamp
}

val
the_t2var_stamp =
ref_make_elt<stamp>(1)

fun
t2var_stamp_new
((*void*)): int =
let
val
stamp =
!the_t2var_stamp
in
!the_t2var_stamp := stamp+1; stamp
end // end of [t2var_stamp_new]

in

(* ****** ****** *)
implement
t2var_get_stamp
(X) = X->t2var_stamp
implement
t2var_get_t1ype
(X) = X->t2var_t1ype
(* ****** ****** *)

implement
t2var_new() =
ref@{
t2var_t1var= ""
,
t2var_t1ype= t1ype_new_ext()
,
t2var_stamp= t2var_stamp_new()
}

(* ****** ****** *)

implement
t2var_new_t1var
(name) =
let
val X = t2var_new()
in
  X->t2var_t1var := name; X
end

(* ****** ****** *)
implement
fprint_t2var(out, X) =
{
val () =
fprint!(out, X->t2var_t1var)
val () =
fprint!(out, "[", X->t2var_stamp, "]")
}
(* ****** ****** *)

end // end of [local]

(* ****** ****** *)
extern
fun
t1env_find
( t1env
, t1var): myoptn(t2var)
(* ****** ****** *)

(*said need to mod this*)
implement
t1env_find
(env0, x0) = (
  case+ env0 of
| T1ENVnil() => myoptn_nil()
| T1ENVcons(x1, y1, env1) => 
  if (x1 = x0)
  then myoptn_cons(y1)
  else t1env_find(env1, x0)
)

(* ****** ****** *)



implement
trans12_env
(trm0, env0) =
(
case+ trm0 of
//
| T1Memp() => T2Memp()
| T1Mint(i0) => T2Mint(i0)
| T1Mbtf(b0) => T2Mbtf(b0)
| T1Mstr(s0) => T2Mstr(s0)
//
| T1Mvar(x1) =>
  T2Mvar(y1) where
  { val-
    myoptn_cons(y1) =
    t1env_find(env0, x1) }
//
| T1Mlam(x1, T1, t2) =>
  T2Mlam(y1, T1, t2) where
  {
    val y1 =
    t2var_new_t1var(x1)
    val t2 =
    trans12_env(t2, env1) where
    {
      val
      env1 =
      T1ENVcons( x1, y1, env0 )
    }
  }
//
| T1Mapp(t1, t2) =>
  T2Mapp(t1, t2) where
  {
    val t1 = trans12_env(t1, env0)
    val t2 = trans12_env(t2, env0)
  }
//
| T1Mlet(t1v, t1e1, t1e2) => T2Mlet(t2v, t2e1, t2e2) where {
  val t2v = t2var_new_t1var(t1v)
  val env1 = T1ENVcons( t1v, t2v, env0 )
  val t2e1 = trans12_env(t1e1, env1)
  val t2e2 = trans12_env(t1e2, env1)
}
//
| T1Mopr(opr, ls) => T2Mopr(opr, t2ls) where {
  val t2ls = mylist_map<t1erm><t2erm> (ls, lam(t1) => trans12_env(t1, env0))
}
//
| T1Mifb(t1, t2, t3) => T2Mift(t12, t22, t32) where {
  val t12 = trans12_env(t1, env0)
  val t22 = trans12_env(t2, env0)
  val t32 = trans12_env(t3, env0)
}
//
| T1Mfix(t1v1, t1v2, opty1, opty2, t1e) => T2Mfix(t2v1, t2v2, opty1, opty2, t2e) where {
  val t2v1 =
    t2var_new_t1var(t1v1)
  val t2v2 = t2var_new_t1var(t1v2)
  val env1 = T1ENVcons( t1v1, t2v1, env0 )
  val env2 = T1ENVcons( t1v2, t2v2, env1 )
  val t2e = trans12_env(t1e, env2)

}
//
| T1Mtup(fst, sec) => T2Mtup(t2f, t2s) where {
  val t2f = trans12_env(fst, env0)
  val t2s = trans12_env(sec, env0)
}
//
| T1Mfst(t1e) => T2Mfst(t2e) where {
  val t2e = trans12_env(t1e, env0)
}
//
| T1Msnd(t1e) => T2Msnd(t2e) where {
  val t2e = trans12_env(t1e, env0)
}
//
| T1Mann(t1e, t1y) => T2Mann(t2e, t1y) where {
  val t2e = trans12_env(t1e, env0)
}
//
| T1Mnil() => T2Mnil()
| T1Mcons(t1e1, t1e2) => T2Mcons(t2e1, t2e2) where {
  val t2e1 = trans12_env(t1e1, env0)
  val t2e2 = trans12_env(t1e2, env0)
}
| T1Misnil(t1e) => T2Misnil(t2e) where {
  val t2e = trans12_env(t1e, env0)
}
| T1Mhead(t1e) => T2Mhead(t2e) where {
  val t2e = trans12_env(t1e, env0)
}
| T1Mtail(t1e) => T2Mtail(t2e) where {
  val t2e = trans12_env(t1e, env0)
}
//
| T1Mref_new(t1e) => T2Mref_new(t2e) where {
  val t2e = trans12_env(t1e, env0)
}
| T1Mref_get(t1e) => T2Mref_get(t2e) where {
  val t2e = trans12_env(t1e, env0)
}

| T1Mref_set(t1e1, t1e2) => T2Mref_set(t2e1, t2e2) where {
  val t2e1 = trans12_env(t1e1, env0)
  val t2e2 = trans12_env(t1e2, env0)
}


) (* end of [trans12_env] *)

(* ****** ****** *)
(*TEST CODE*)
val t1emp = T1Memp()
val t1lam = T1Mlam("test2", none, t1emp)
val t1let = T1Mlet("test3", t1emp, t1lam)
val t1cons = T1Mcons(t1emp, t1emp)
val t1refn = T1Mref_new(T1Mint(3))
val t1fix = T1Mfix("f", "x", none, none, t1lam)


val t2emp = trans12(t1emp)
val t2lam = trans12(t1lam)
val t2let = trans12(t1let)
val t2cons = trans12(t1cons)
val t2refn = trans12(t1refn)
val t2fix = trans12(t1fix)

val () = println!("t1emp: ", t1emp, " T2emp after trans12: ", t2emp)
val () = println!("t1lam: ", t1lam, " T2lam after trans12: ", t2lam)
val () = println!("t1let: ", t1let, " T2let after trans12: ", t2let)
val () = println!("t1cons: ", t1cons, " T2cons after trans12: ", t2cons)
val () = println!("t1refn: ", t1refn, " T2refn after trans12: ", t2refn)
val () = println!("t1fix: ", t1fix, " T2fix after trans12: ", t2fix)

(* end of [lambda2_sol.dats] *)
