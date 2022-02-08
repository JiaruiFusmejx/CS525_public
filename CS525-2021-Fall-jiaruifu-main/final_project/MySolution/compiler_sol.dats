
(* ****** ****** *)
//
#include
"./../lambda2_tinfer.dats"
//
(* ****** ****** *)

(* ****** ****** *)
//
//#include
#include
"./../lambda2.dats"
//
(* ****** ****** *)


#dynload
"./../lambda1.dats"

(* ****** ****** *)
//
#include
"./../lambda2_interp.dats"

(*from interp_sol*)

//
(* ****** ****** *)
implement main0() = ((*dummy*))
(* ****** ****** *)


typedef stamp = int
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


extern
fun
t2var_get_name(t2var): string
implement
t2var_get_name
(X) = X->t2var_t1var
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
(*
implement
t2var_equal
(X1, X2) = (X1.stamp() = X2.stamp())
*)

(*
extern
fun
t2var_infer1
( x0: t2var
, ctx0: t2ctx): myoptn(t1ype)
implement
t2var_infer1
(x0, ctx0) =
(
case+ ctx0 of
| CTXnil() => myoptn_nil()
| CTXcons
  (x1, T1, ctx1) =>
  if (t2var_equal(x0, x1))//(x0 = x1)
  then myoptn_cons(T1)
  else t2var_infer1(x0, ctx1)
)
*)
(* NOTE coppied from tinfer section*)

fun t2var_eval1
(x0: t2var, env0: t2env) : myoptn(t2val) = (
  case+ env0 of
| ENVnil() => myoptn_nil()
| ENVcons(x1, v1, env1) => (
  if (x0 = x1)
  then myoptn_cons(v1)
  else t2var_eval1(x0, env1)
)
)


implement
interp0(trm0) = interp0_env(trm0, ENVnil())
//
implement
interp0_env
(trm0, env0) =
(
case trm0 of
//
| T2Memp() => T2Vemp() //need to add in T2V
| T2Mint(i0) => T2Vint(i0)
| T2Mbtf(b0) => T2Vbtf(b0)
| T2Mstr(s0) => T2Vstr(s0) //need to add in T2V
//
| T2Mref_new(t1) =>
  (
    T2Vref(ref(v1))) where
  {
    val v1 = interp0_env(t1, env0)
  }
| T2Mann(t1, T1) => interp0_env(t1, env0)
//

| T2Mvar(t2v) => 
  let 
    val opt = t2var_eval1(t2v, env0)
  in 
    case- opt of
    | myoptn_cons(v0) => v0
  end

//
| T2Mlam(t2v, opty1, t2e) => T2Vlam(trm0, env0) // need to add in T2V
| T2Mapp(t2e1, t2e2) => (
  let 
  val v1 = interp0_env(t2e1, env0)
  val v2 = interp0_env(t2e2, env0)
  in 
  case- v1 of
  | T2Vlam(tlam, env1) =>
    let
      val- T2Mlam(x1, ty1, t2bd) = tlam
    in
      interp0_env(t2bd, ENVcons(x1, v2, env1))
    end
  //
  | T2Vfix(tfix, env1) =>
    let 
      val- T2Mfix(t2v1, t2v2, opty1, opty2, t2def) = tfix
      val- T2Mlam(x1, ty1, t2bd) = t2def
    in 
      interp0_env(t2bd, ENVcons(x1, v2, ENVcons(t2v1, v1, env1))) // might need to come back to this
    end
  end
)

| T2Mlet(t2v, t2e1, t2e2) => 
  let
    val t1 = interp0_env(t2e1, env0)
  in
    interp0_env(t2e2, ENVcons(t2v, t1, env0))
  end
//
| T2Mopr(opr, ls) => (
  let
    val vs =
    mylist_map<t2erm><t2val>
    (ls, lam(t1) => interp0_env(t1, env0))
  in
    case- opr of
    | "+" => 
      let
        val-
          mylist_cons(T2Vint(i1), vs) = vs
        val-
          mylist_cons(T2Vint(i2), vs) = vs
      in
        T2Vint(i1+i2)
      end
    | ">" => 
      let
        val-
        mylist_cons(T2Vint(i1), vs) = vs
        val-
        mylist_cons(T2Vint(i2), vs) = vs
      in
        T2Vbtf(i1 > i2)
      end
    | _ (*unknown operator*)=> exit(1) where
        {
        val () = println!("term0_eval1: T0Mopr: nm = ", opr, "unknown")
        }
  end
)

//
| T2Mift(t2e1, t2e2, t2e3) =>
  let 
    val v1 = interp0_env(t2e1, env0)
  in
    case- v1 of
    | T2Vbtf(b0) =>
      if b0 then interp0_env(t2e2, env0) else interp0_env(t2e3, env0)
  end
//
| T2Mfix(t2v1, t2v2, opty1, opty2, tdef) => T2Vlam(tdef, ENVcons(t2v1, T2Vfix(trm0, env0), env0)) // might need to come back to here
//
| T2Mtup(t2e1, t2e2) => T2Vtup(v1, v2) where {
  val v1 = interp0_env(t2e1, env0)
  val v2 = interp0_env(t2e2, env0)
}
//
| T2Mfst(t2e) => (
  let 
    val- T2Vtup(x1, x2) = interp0_env(t2e, env0)
  in 
    x1
  end
)
//
| T2Msnd(t2e) => (
  let 
    val- T2Vtup(x1, x2) = interp0_env(t2e, env0)
  in 
    x2
  end
)
//
| T2Mnil() => T2Vnil() // need to add this to T2V
| T2Mcons(t2e1, t2e2) => T2Vcons(head, tail) where {   // need to add this to T2V
  val head = interp0_env(t2e1, env0)
  val tail = interp0_env(t2e2, env0)
}
| T2Misnil(t2e) => (
  let
    val n = interp0_env(t2e, env0)
  in
    case- n of
    | T2Vnil() => T2Vbtf(true)
    | T2Vcons(_, _) => T2Vbtf(false)
    | _ => T2Vnil() // just a flag for special case
  end
)
| T2Mhead(t2e) => (
  let
    val lst = interp0_env(t2e, env0)
  in 
    case- lst of 
    | T2Vcons(h, t) => h
  end
)
| T2Mtail(t2e) => (
  let
    val lst = interp0_env(t2e, env0)
  in 
    case- lst of 
    | T2Vcons(h, t) => t
  end
)
//
| T2Mref_get(t2e) => (
  let 
    val- T2Vref(x) = interp0_env(t2e, env0)
  in
    !x 
  end

)
| T2Mref_set(t2e1, t2e2) => (
  let 
    val- T2Vref(x) = interp0_env(t2e1, env0)
    val update = interp0_env(t2e2, env0)
  in
    (!x := update; T2Vemp()) // fixed based on email

  end
)
)
//
(**************************************** End of Interp************************************************)
extern
fun
interp0_env2
(prgm: t2erm, env0: t2env): (t2val, t2env)
//
implement
interp0_env2
(trm0, env0) =
(
case- trm0 of
//
| T2Memp() => (T2Vemp(), env0) //need to add in T2V


| T2Mint(i0) => (T2Vint(i0), env0)
| T2Mbtf(b0) => (T2Vbtf(b0), env0)
| T2Mstr(s0) => (T2Vstr(s0), env0) //need to add in T2V
//
| T2Mref_new(t1) =>
  (
    (T2Vref(ref(v1)), env1)) where
  {
    val- (v1, env1) = interp0_env2(t1, env0)
  }

| T2Mann(t1, T1) => interp0_env2(t1, env0)
//

| T2Mvar(t2v) => 
  let 
    val opt = t2var_eval1(t2v, env0)
  in 
    case- opt of
    | myoptn_cons(v0) => (v0, env0)
  end

//
| T2Mlam(t2v, opty1, t2e) => (T2Vlam(trm0, env0), env0) // need to add in T2V
| T2Mapp(t2e1, t2e2) => (
  let 
  val (v1, e1) = interp0_env2(t2e1, env0)
  val (v2, e2) = interp0_env2(t2e2, env0)
  in 
  case- v1 of
  | T2Vlam(tlam, env1) =>
    let
      val- T2Mlam(x1, ty1, t2bd) = tlam
    in
      interp0_env2(t2bd, ENVcons(x1, v2, env1))
    end
  //
  | T2Vfix(tfix, env1) =>
    let 
      val- T2Mfix(t2v1, t2v2, opty1, opty2, t2def) = tfix
      val- T2Mlam(x1, ty1, t2bd) = t2def
    in 
      interp0_env2(t2bd, ENVcons(x1, v2, ENVcons(t2v1, v1, env1))) // might need to come back to this
    end
  end
)

| T2Mlet(t2v, t2e1, t2e2) => 
  let
    val (t1, e1) = interp0_env2(t2e1, env0)
  in
    interp0_env2(t2e2, ENVcons(t2v, t1, env0))
  end
//
| T2Mopr(opr, ls) => (
  let
    val vs =
    mylist_map<t2erm><t2val>
    (ls, lam(t1) => interp0_env(t1, env0))
  in
    case- opr of
    | "+" => 
      let
        val-
          mylist_cons(T2Vint(i1), vs) = vs
        val-
          mylist_cons(T2Vint(i2), vs) = vs
      in
        (T2Vint(i1+i2), env0)
      end
    | ">" => 
      let
        val-
        mylist_cons(T2Vint(i1), vs) = vs
        val-
        mylist_cons(T2Vint(i2), vs) = vs
      in
        (T2Vbtf(i1 > i2), env0)
      end
    | _ (*unknown operator*)=> exit(1) where
        {
        val () = println!("term0_eval1: T0Mopr: nm = ", opr, "unknown")
        }
  end
)

//
| T2Mift(t2e1, t2e2, t2e3) =>
  let 
    val (v1, e1) = interp0_env2(t2e1, env0)
  in
    case- v1 of
    | T2Vbtf(b0) =>
      if b0 then interp0_env2(t2e2, env0) else interp0_env2(t2e3, env0)
  end
//
| T2Mfix(t2v1, t2v2, opty1, opty2, tdef) => (T2Vlam(tdef, ENVcons(t2v1, T2Vfix(trm0, env0), env0)), ENVcons(t2v1, T2Vfix(trm0, env0), env0)) // might need to come back to here
//
| T2Mtup(t2e1, t2e2) => (T2Vtup(v1, v2), env0) where {
  val (v1, _) = interp0_env2(t2e1, env0)
  val (v2, _) = interp0_env2(t2e2, env0)
}
//
| T2Mfst(t2e) => (
  let 
    val- (T2Vtup(x1, x2), e1) = interp0_env2(t2e, env0)
  in 
    (x1, e1)
  end
)
//
| T2Msnd(t2e) => (
  let 
    val- (T2Vtup(x1, x2), e1) = interp0_env2(t2e, env0)
  in 
    (x2, e1)
  end
)
//
| T2Mnil() => (T2Vnil(), env0) // need to add this to T2V
| T2Mcons(t2e1, t2e2) => (T2Vcons(head, tail), env0) where {   // need to add this to T2V
  val (head, _) = interp0_env2(t2e1, env0)
  val (tail, _) = interp0_env2(t2e2, env0)
}
| T2Misnil(t2e) => (
  let
    val (n, e1) = interp0_env2(t2e, env0)
  in
    case- n of
    | T2Vnil() => (T2Vbtf(true), e1)
    | T2Vcons(_, _) => (T2Vbtf(false), e1)
    | _ => (T2Vnil(), env0) // just a flag for special case
  end
)
| T2Mhead(t2e) => (
  let
    val (lst, e) = interp0_env2(t2e, env0)
  in 
    case- lst of 
    | T2Vcons(h, t) => (h, e)
  end
)
| T2Mtail(t2e) => (
  let
    val (lst, e) = interp0_env2(t2e, env0)
  in 
    case- lst of 
    | T2Vcons(h, t) => (t, e)
  end
)
//
| T2Mref_get(t2e) => (
  let 
    val- (T2Vref(x), e) = interp0_env2(t2e, env0)
  in
    (!x, e)
  end

)
| T2Mref_set(t2e1, t2e2) => (
  let 
    val- (T2Vref(x), e) = interp0_env2(t2e1, env0)
    val (update, _) = interp0_env2(t2e2, env0)
  in
    (!x := update; (T2Vemp(), env0)) // fixed based on email

  end
)
)

(**************************************** Start of Trans12************************************************)
(*
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
*)

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
  val t2e1 = trans12_env(t1e1, env0)  // fixed based on email
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

(**************************************** End of trans12************************************************)

(**************************************** Start of tinfer************************************************)
implement
t1xyz_equal
(X1, X2) =
(
$UNSAFE.cast{ptr}(X1)
=
$UNSAFE.cast{ptr}(X2)
)

(* ****** ************ ************ ************ ************ ****** *)

extern
fun
t1ype_occurs
(T1: t1ype, X2: t1xyz): bool

implement
t1ype_occurs
(T1, X2) =
(
case+ T1 of
| T1Pbas _ => false
| T1Pfun(T11, T12) =>
  t1ype_occurs(T11, X2)||t1ype_occurs(T12, X2)
| T1Ptup(T11, T12) =>
  t1ype_occurs(T11, X2)||t1ype_occurs(T12, X2)
| T1Plst(T11) => t1ype_occurs(T11, X2)
| T1Pref(T11) => t1ype_occurs(T11, X2)
| T1Pext(X1) =>
  (if t1xyz_equal(X1, X2) then true else false)
)
(* ****** ************ ************ ************ ************ ****** *)

extern
fun
t1ype_eval
(T1: t1ype): t1ype

implement
t1ype_eval(T1) =
(
case+ T1 of
|
T1Pext(X1) => // modified so that type0_eval recursively evaluates T0Pext within T0Pfun/tup/lst/ref
(
case+ !X1 of
| none() => T1
| some(T1) => (
  let
  val T1 = t1ype_eval(T1)
  in 
  case+ T1 of
  | T1Plst(T11) => t1ype_eval(T11)
  | T1Pref(T11) => t1ype_eval(T11)
  | T1Pfun(T11, T12) => T1Pfun(t1ype_eval(T11),t1ype_eval(T12))
  | T1Ptup(T11, T12) => T1Ptup(t1ype_eval(T11),t1ype_eval(T12))
  | _ => T1
  end
)
  //type0_eval(T1)
)
| _(*non-T0Pext*) => T1
)

(* ****** ************ ************ ************ ************ ****** *)

extern
fun
t1ype_unify
(T1: t1ype, T2: t1ype): int
extern
fun
t1ype_unify_ext1
(T1: t1ype, T2: t1ype): int
extern
fun
t1ype_unify_ext2
(T1: t1ype, T2: t1ype): int
extern
fun
t1ype_unify_main
(T1: t1ype, T2: t1ype): int

(* ****** ****** *)

implement
t1ype_unify
(T1, T2) =
let
val T1 = t1ype_eval(T1)
val T2 = t1ype_eval(T2)
in
//
case+ T1 of
|
T1Pext _ =>
t1ype_unify_ext1(T1, T2)
//
| _(*non-T1Pext*) =>
(
case+ T2 of
T1Pext _ =>
t1ype_unify_ext2(T1, T2)
| _(*non-T1Pext*) =>
  t1ype_unify_main(T1, T2)
)
//
end // end of [type0_unify]


(* ****** ****** *)

implement
t1ype_unify_ext1
(T1, T2) =
let
val-T1Pext(X1) = T1
in
if
t1ype_occurs(T2, X1)
then
(
case+ T2 of
| T1Pext _ => 0
| _(*non-T1Pext*) => 1
)  
else
  (!X1 := some(T2); 0)
end

implement
t1ype_unify_ext2
(T1, T2) =
t1ype_unify_ext1(T2, T1)

(* ****** ****** *)

implement
t1ype_unify_main
(T1, T2) =
(
case+ T1 of
//
|
T1Pbas(nm1) =>
(
case+ T2 of
| T1Pbas(nm2) =>
  if nm1 = nm2 then 0 else 1
| _ (*non-T1Pbas*) => 1
)
//
|
T1Pfun
(T11, T12) =>
(
case+ T2 of
|
T1Pfun
(T21, T22) =>
t1ype_unify(T11, T21) // modified so that type_unify correctly handles T0Pfun(T0Pext(...); T0Pext(...))
+
t1ype_unify(T12, T22) // same here
| _ (*non-T0Pfun*) => 1
)
//
|
T1Ptup
(T11, T12) =>
(
case+ T2 of
|
T1Ptup
(T21, T22) =>
t1ype_unify(T11, T21) // modified so that type_unify correctly handles T0Ptup(T0Pext(...); T0Pext(...))
+
t1ype_unify(T12, T22) // same here
| _ (*non-T0Ptup*) => 1
)
//
|
T1Plst
(T11) =>
(
case+ T2 of
|
T1Plst
(T21) =>
t1ype_unify(T11, T21)
| _ (*non-T0Plst*) => 1
)
//
|
T1Pref
(T11) =>
(
case+ T2 of
|
T1Pref
(T21) =>
t1ype_unify(T11, T21)
| _ (*non-T0Plst*) => 1
)
//
| T1Pext _ => 1 // HX: deadcode
//
) (* end of [type0_unify_main] *)

(* ****** ************ ************ ************ ************ ****** *)
(*
typedef stamp = int
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
*)

(*
implement
t2var_equal
(X1, X2) = (X1.stamp() = X2.stamp())
*)

(* ****** ************ ************ end of code supporting t2var_equal ************ ************ ****** *)
(*
extern
fun
t2var_infer1
( x0: t2var
, ctx0: t2ctx): myoptn(t1ype)
implement
t2var_infer1
(x0, ctx0) =
(
case+ ctx0 of
| CTXnil() => myoptn_nil()
| CTXcons
  (x1, T1, ctx1) =>
  if (t2var_equal(x0, x1))//(x0 = x1)
  then myoptn_cons(T1)
  else t2var_infer1(x0, ctx1)
)
*)
(* ****** ************ ************ ************ ************ ****** *)
(*
val T1Pvoid = T1Pbas("void")
val T1Pint = T1Pbas("int")
val T1Pbtf = T1Pbas("btf")
val T1Pstr = T1Pbas("str")
*)

(*TEST CODE*)
val t1emp = T1Memp()
val t1lam = T1Mlam("test2", none, t1emp)
val t1let = T1Mlet("test3", t1emp, t1lam)
val t1cons = T1Mcons(t1emp, t1emp)
val t1refn = T1Mref_new(T1Mint(3))
val t1fix = T1Mfix("f", "x", none, none, t1lam)
val t1int = T1Mint(4)


val t2emp = trans12(t1emp)
val t2lam = trans12(t1lam)
val t2let = trans12(t1let)
val t2cons = trans12(t1cons)
val t2refn = trans12(t1refn)
val t2fix = trans12(t1fix)
val t2int = trans12(t1int)
val t2vi = interp0(t2int)

val () = println!("t1emp: ", t1emp, " T2emp after trans12: ", t2emp)
val () = println!("t1lam: ", t1lam, " T2lam after trans12: ", t2lam)
val () = println!("t1let: ", t1let, " T2let after trans12: ", t2let)
val () = println!("t1cons: ", t1cons, " T2cons after trans12: ", t2cons)
val () = println!("t1refn: ", t1refn, " T2refn after trans12: ", t2refn)
val () = println!("t1fix: ", t1fix, " T2fix after trans12: ", t2fix)

extern
fun
print_t2val : (t2val) -> void
and
prerr_t2val : (t2val) -> void
extern
fun
fprint_t2val : (FILEref, t2val) -> void

overload print with print_t2val
overload prerr with prerr_t2val
overload fprint with fprint_t2val

(* ****** ****** *)

implement
print_t2val(t0) = 
fprint_t2val(stdout_ref, t0)
implement
prerr_t2val(t0) = 
fprint_t2val(stderr_ref, t0)

local

implement
fprint_val<t2val> = fprint_t2val

in (* in-of-local *)
implement
fprint_t2val
  (out, t0) =
(
case+ t0 of
| T2Vint(i0) => fprint!(out, "T2Vint(", i0, ")")
| T2Vref(x) => fprint!(out, "T2Vref(", !x, ")")
| _ => fprint!(out, "Not Yet implemented")
)

end (* end of local*)

val () = println!("t1int(4): ", t1int, " T2int after trans12 & interp: ", t2vi)

(*
abstype instr_type = ptr
typedef instr_var = instr_type

local

assume
instr_type =
ref@{
name= t1var
,
instr_mark= stamp
}

val
the_instr_mark =
ref_make_elt<stamp>(0)

fun
instr_mark_new
((*void*)): int =
let
val
mark =
!the_instr_mark
in
!the_instr_mark := mark+1; mark
end // end of [instr_mark_new]

in

(* ****** ****** *)
fun//implement
instr_get_mark
(X) = X->instr_mark
(*
implement
t2var_get_t1ype
(X) = X->t2var_t1ype
(* ****** ****** *) *)

fun//implement
instr_var_new() =
ref@{
name= ""
,
instr_mark= instr_mark_new()
}

(* ****** ****** *)

fun//implement
instr_new_t2var
(t2v) =
let
val X = instr_var_new()
val name_in = t2v->t2var_t1var
in
  X->name := name_in; X
end

(* ****** ****** *)
fun//implement
fprint_instr_var(out, X) =
{
val () =
fprint!(out, X->name)
val () =
fprint!(out, "[", X->instr_mark, "]")
}
(* ****** ****** *)

end // end of [local]

fun//implement
instr_equal
(X1, X2) = (instr_get_mark(X1) = instr_get_mark(X2))
*)
(*
fun instr_var_eval1
(x0: t2var, env0: t2env) : myoptn(t2val) = (
  case+ env0 of
| ENVnil() => myoptn_nil()
| ENVcons(x1, v1, env1) => (
  if (x0 = x1)
  then myoptn_cons(v1)
  else t2var_eval1(x0, env1)
)
)
*)
extern
fun
instruction_const(prgm: t2erm, env0: t2env): void
extern
fun
finstruction_const(prgm: t2erm, env0: t2env, out: FILEref): void
extern
fun
tt_instr_wrap(prgm: t1erm, env0: t1env): void
extern
fun
ftt_instr_wrap(prgm: t1erm, env0: t1env, out: FILEref): void

fun t2var_app_instr
(x0: t2var, env0: t2env) : myoptn(t2val) = (
  case+ env0 of
| ENVnil() => myoptn_nil()
| ENVcons(x1, v1, env1) => (
  if (x0 = x1)
  then myoptn_cons(v1)
  else t2var_app_instr(x0, env1)
)
)

implement
tt_instr_wrap
(prgm1, env0) = (
    let
        val prgm2 = trans12_env(prgm1, env0)
        //val t1ype_res = tinfer0(prgm2) Couldn't run this, otherwise this would function as type checking
        //assuming that type checking has been done, all following terms are correct.
        //also need to construct suitable environment for instruction_const
        //using env0 as place holder for now
    in
        instruction_const(prgm2, ENVnil())
    end
)

implement
ftt_instr_wrap
(prgm1, env0, out) = (
    let
        val prgm2 = trans12_env(prgm1, env0)
        //val t1ype_res = tinfer0(prgm2) Couldn't run this, otherwise this would function as type checking
        //assuming that type checking has been done, all following terms are correct.
        //also need to construct suitable environment for instruction_const
        //using env0 as place holder for now
    in
        finstruction_const(prgm2, ENVnil(), out)
    end
)

implement
instruction_const
(prgm1, env0) = finstruction_const(prgm1, env0, stdout_ref)




implement
finstruction_const
(prgm1, env0, out) = 
(
    case+ prgm1 of
    | T2Mint(i0) => fprint!(out, "LAMVAL_int(" , i0, ")")
    | T2Memp() => fprint!(out, "LAMVAL_emp()")
    | T2Mbtf(b0) => fprint!(out, "LAMVAL_btf(", b0, ")")
    | T2Mstr(s0) => fprint!(out, "LAMVAL_str('", s0, "')")
    | T2Mvar(t2var) => ( // need interp, then pattern match t2v values, i think
        let
          val (_, e1) = interp0_env2(prgm1, env0)
          val- myoptn_cons(v0) = t2var_app_instr(t2var, e1)
        in
          case- v0 of
          | T2Vemp() => finstruction_const(T2Memp(), e1, out)
          | T2Vint(i) => finstruction_const(T2Mint(i), e1, out)
          | T2Vbtf(b) => finstruction_const(T2Mbtf(b), e1, out)
          | T2Vstr(s) => finstruction_const(T2Mstr(s), e1, out)
          | _ => (
            let
              val var_name = t2var_get_name(t2var)
            in
              fprint!(out, var_name)
            end
          ) // other types are not handled, unable to or not handled here
        end
    ) 
    | T2Mift(f, t, e) => (
        let
            //val () = fprint!(out, )
            val () = fprint!(out, "if((lamval_btf)")
            val () = finstruction_const(f, env0, out)
            val () = fprint!(out, ")->data){")
            val () = finstruction_const(t, env0, out)
            val () = fprint!(out, " }else{ ")
            val () = finstruction_const(e, env0, out)
            val () = fprint!(out, " }")
        in
            ()
        end
    )
    | T2Mtup(a, b) => (
        let
            val () = fprint!(out, "LAMVAL_tup(")
            val () = finstruction_const(a, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(b, env0, out)
            val () = fprint!(out, " )")
        in
            ()
        end
    )
    | T2Mfst(tup) => (
        let
            val () = fprint!(out, "LAMOPR_fst(")
            val () = finstruction_const(tup, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
    )
    | T2Msnd(tup) => (
        let
            val () = fprint!(out, "LAMOPR_snd(")
            val () = finstruction_const(tup, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
    ) 
    
    | T2Mopr(opr, ls) => (
    let
      //val vs = ls
      (*mylist_map<t2erm><t2val>
      (ls, lam(t1) => interp0(t1))*)
      val- mylist_cons(t1, vs) = ls
      val- mylist_cons(t2, ks) = vs
      
    in
      case- opr of
        | "+" =>
        let

            val () = fprint!(out, "LAMOPR_add(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end 
        | "-" =>
        let

            val () = fprint!(out, "LAMOPR_sub(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | "*" =>
        let

            val () = fprint!(out, "LAMOPR_mul(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | "/" =>
        let

            val () = fprint!(out, "LAMOPR_div(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | "%" =>
        let

            val () = fprint!(out, "LAMOPR_mod(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | ">" =>
        let

            val () = fprint!(out, "LAMOPR_igt(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | ">=" =>
        let

            val () = fprint!(out, "LAMOPR_ige(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | "<" =>
        let

            val () = fprint!(out, "LAMOPR_ilt(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | "<=" =>
        let

            val () = fprint!(out, "LAMOPR_ile(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | "==" =>
        let

            val () = fprint!(out, "LAMOPR_ieq(")
            val () = finstruction_const(t1, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t2, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
        | _ (*unknown operator*)=> exit(1) where
            {
            val () = println!("fintstruction_const: T2Mopr: nm = ", opr, "unknown")
            } 
    end
    ) 
    | T2Mnil() => fprint!(out, "LAMVAL_nil()")
    | T2Mcons(h, t) => (
        let
            val () = fprint!(out, "LAMVAL_con(")
            val () = finstruction_const(h, env0, out)
            val () = fprint!(out, ", ")
            val () = finstruction_const(t, env0, out)
            val () = fprint!(out, " )")
        in
            ()
        end
    ) 
    | T2Misnil(term) => (
        let
            val () = fprint!(out, "LAMOPR_isn(")
            val () = finstruction_const(term, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
    )
    | T2Mhead(term) => (
        let
            val () = fprint!(out, "LAMOPR_head(")
            val () = finstruction_const(term, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
    )
    | T2Mtail(term) => (
        let
            val () = fprint!(out, "LAMOPR_tail(")
            val () = finstruction_const(term, env0, out)
            val () = fprint!(out, ")")
        in
            ()
        end
    )
    | T2Mlet(t2v, t2e1, t2e2) => (
        let 
          val (_, env1) = interp0_env2(prgm1, env0)

        in
          finstruction_const(t2e2, env1, out)
        end
    )
    | T2Mann(t2e, t1p) => () // not sure what to put here
    | T2Mlam(t2v, _, t2e) => (
      let
        val () = fprint!(out, "lamval fun(lamval ")
        val name = t2var_get_name(t2v)
        val () = fprint!(out, name)
        val () = fprint!(out, "){ ")
        val () = fprint!(out, " return ")
        val () = finstruction_const(t2e, env0, out)
        val () = fprint!(out, "; }")
      in
        ()
      end
    )
    | T2Mfix(fvar, xvar, _, _, t2e) => (
      let
        val (_, env1) = interp0_env2(prgm1, env0)
        val fname = t2var_get_name(fvar)
        val xname = t2var_get_name(xvar)
        val () = fprint!(out, "lamval ")
        val () = fprint!(out, fname)
        val () = fprint!(out, "(lamval ")
        val () = fprint!(out, xname)
        val () = fprint!(out, "){")
        val- T2Mlam(t2v, _, bdy) = t2e
        val () = finstruction_const(bdy, env1, out)
        val () = fprint!(out, "}")
      in
        ()
      end
    )
    | T2Mapp(func, arg) => (
      let
        (* // Unfortunately this section of code could not compile and the issue was not found in the limited time.
        case- func of
        | T2Mlam(t2v, _,t2e) => (
          let
            val () = finstruction_const(func, env0, out)
            val () = fprint!(out, "  fun( ")
            val () = finstruction_const(arg, env0, out)
            val () = fprint!(out, " )")
            
          in
            ()
          end
        )
        | T2Mfix(fvar, xvar, _,_, t2e) => (
          let
            val () = finstruction_const(func, env0, out)
            val fname = t2var_get_name(fvar)
            val () = fprint!(out, "  ")
            val () = fprint!(out, fname)
            val () = fprint!(out, "(")
            val () = finstruction_const(arg, env0, out)
            val () = fprint!(out, " )")
          in
            ()
          end
        )
        | T2Mvar(t2v) => ( // This is for special case of T2Mvar, where it is evaluated to a lam or a fix
        //assuming that these cases only occur within a declared function (therefore there is no need to declare the entire function again)
        // in theory, the code attempts to only trigger the function call, where as above it would declare the function first and then make
        // the call.
          let
            val- myoptn_cons(v0) = t2var_app_instr(t2v, env0)
            case- v0 of
            | T2Vlam(tlam, env1) => (
              let
                val () = fprint!(out, "fun( ")
                val () = finstruction_const(arg, env0, out)
                val () = fprint!(out, " )")
              in
                ()
              end
            )
            | T2Vfix(tfix, env1) => (
              let
                val- T2Mfix(fvar, xvar, opty1, opty2, t2def) = tfix
                val fname = t2var_get_name(fvar)
                val () = fprint!(out, fname)
                val () = fprint!(out, "(")
                val () = finstruction_const(arg, env0, out)
                val () = fprint!(out, " )")
              in
              end
            )
          in
            ()
          end
        )
        *)
      in
        ()
      end
    )
    | T2Mref_new(_) => () //unable to produce boxed c-representation
    | T2Mref_get(_) => () //unable to produce boxed c-representation
    | T2Mref_set(_,_) => () //unable to produce boxed c-representation

) (******* ************ ************ [end of finstruction_const] ************ ************ *******)

(*TEST CODE*)
val t1emp = T1Memp()
val t1add = T1Mopr("+", T1Mint(2)::T1Mint(3)::nil())
val t1sub = T1Mopr("-", T1Mint(25)::T1Mint(4)::nil())
val t1lam_emp = T1Mlam("test2", none, T1Mstr("returned something"))

val t1let = T1Mlet("test3", t1emp, t1lam)
val t1cons = T1Mcons(t1emp, t1emp)

val t1fix = T1Mfix("fix_recur", "x", none, none, t1lam)
val t1int = T1Mint(4)
val t1tup = T1Mtup(t1int, t1emp)
val t1fst = T1Mfst(t1tup)

val t1if = T1Mifb(T1Mopr(">", T1Mint(2)::T1Mint(3)::nil()), T1Mstr("first is greater"), T1Mstr("second is greater"))

val t1bdy = T1Mopr("-", T1Mint(25)::T1Mvar("test3")::nil())

val t1lam = T1Mlam("test3", none, t1bdy)

val () = println!()
val () = tt_instr_wrap(t1emp ,T1ENVnil())
val () = println!()
val () = tt_instr_wrap(t1add ,T1ENVnil())
val () = println!()
val () = tt_instr_wrap(t1sub ,T1ENVnil())
val () = println!()
val () = tt_instr_wrap(t1lam_emp ,T1ENVnil())
val () = println!()
//val () = tt_instr_wrap(t1lam ,T1ENVnil())
//val () = println!()
val () = tt_instr_wrap(t1let ,T1ENVnil())
val () = println!()
val () = tt_instr_wrap(t1cons ,T1ENVnil())
val () = println!()
val () = tt_instr_wrap(t1fix ,T1ENVnil())
val () = println!()
val () = tt_instr_wrap(t1tup ,T1ENVnil())
val () = println!()
val () = tt_instr_wrap(t1fst ,T1ENVnil())
val () = println!()
val () = tt_instr_wrap(t1if ,T1ENVnil())
val () = println!()

(*

(* ****** ****** *)
//
implement
tinfer0(trm0) = tinfer0_env(trm0, CTXnil())

implement
tinfer0_env(trm0, ctx0) =
(
case- trm0 of
//
| T2Memp() => T1Pvoid
| T2Mint(i0) => T1Pint
| T2Mbtf(b0) => T1Pbtf
| T2Mstr(s0) => T1Pstr
//
| T2Mvar(t2v) => (
    let
        val opt = t2var_infer1(t2v, ctx0)
    in 
        case- opt of
        | myoptn_cons(v0) => v0
    end
)
//
| T2Mlam(t2v, opty, t2e) => (
    let
        val T01 = (
        case+ opty of
        | myoptn_nil() => t1ype_new_ext()
        | myoptn_cons(T01) => T01
        )
        val ctx1 =
        CTXcons(t2v, T01, ctx0)
        val T1 =
        tinfer0_env(t2e, ctx1)
        val T012 = t1ype_eval(T01)
    in
    
        T1Pfun(T012, T1)
    end
)
//
| T2Mapp(t2e1, t2e2) => (
    let
        val T1 =
        tinfer0_env(t2e1, ctx0)
        val T2 =
        tinfer0_env(t2e2, ctx0)

    
        val-00 =
        t1ype_unify
        ( T1, t1ype_new_fun() ) 
        //val () = println!("app type_eval T1 after unify with new_fun: ", type0_eval(T1))
        val T1 = t1ype_eval(T1)
//
    in
        case- T1 of
        | T1Pfun(T11, T12) =>
          T12 where
          { val-00 = t1ype_unify(T11, T2) }
    end
)
//
| T2Mlet(t2v, t2e1, t2e2) => (
    let 
        val T1 = tinfer0_env(t2e1, ctx0)
        val ctx1 = CTXcons(t2v, T1, ctx0)
    in
        tinfer0_env(t2e2, ctx1)
    end
)
//
| T2Mopr(opr, ls) => (
    let
        val Ts =
        mylist_map<t2erm><t1ype>
        (ls, lam(t1) => tinfer0_env(t1, ctx0))
    in
        case+ opr of
        | "+" =>
        let
            val-
             mylist_cons(T1, Ts) = Ts
            val-
             mylist_cons(T2, Ts) = Ts
//
            val-00 =
            t1ype_unify(T1, T1Pint)
            val-00 =
            t1ype_unify(T2, T1Pint)
//
        in
            T1Pint
        end
        | ">" =>
        let
            val-
             mylist_cons(T1, Ts) = Ts
            val-
             mylist_cons(T2, Ts) = Ts
//
            val-00 =
            t1ype_unify(T1, T1Pint)
            val-00 =
            t1ype_unify(T2, T1Pint)
//
        in
            T1Pbtf
        end
        | _ (*unknown operator*)=> exit(1) where {
            val () = println!("tinfer0_env: T2Mopr: opr = ", opr)
        }
    end
)
//
| T2Mift(t21, t22, t23) => (
    let
        val T1 = tinfer0_env(t21, ctx0)
        val T2 = tinfer0_env(t22, ctx0)
        val T3 = tinfer0_env(t23, ctx0)
        val-00 = t1ype_unify(T1, T1Pbtf)
    in
        T2 where { val-00 = t1ype_unify(T2, T3) }
    end
)
//
| T2Mfix(tv1, tv2, opty1, opty2, t2e) => (
    let
        val T01 = (
        case+ opty1 of
        | myoptn_nil() => t1ype_new_ext()
        | myoptn_cons(T01) => T01
        )
        val T02 = (
        case+ opty2 of
        | myoptn_nil() => t1ype_new_ext()
        | myoptn_cons(T01) => T01
        )
        val ctx1 = CTXcons(tv1, T01, ctx0)
        //val ctx2 = CTXcons(tv2, T02, ctx1)
        val T1 = tinfer0_env(t2e, ctx1)
        val T012 = t1ype_eval(T01)
        val- T1Pfun(z, res) = T012
        val- 00 = t1ype_unify(res, T02)
    in 
        T012 where { val- 00 = t1ype_unify(T012, T1) }
    end (**)
)
//
| T2Mtup(t1, t2) => T1Ptup(x, y) where {
    val x = tinfer0_env(t1, ctx0)
    val y = tinfer0_env(t2, ctx0)
}
//
| T2Mfst(t1) => (
    let 
        val temp = tinfer0_env(t1, ctx0)
        //val- T1Ptup(x, y) = tinfer0_env(t1, ctx0)

    in
      case- temp of
      | T1Ptup(x, y) => x 
      | T1Pext(x) => (
        let
          val ntup = T1Ptup(t1ype_new_ext(), t1ype_new_ext())
          val- 00 = t1ype_unify(temp, ntup)
          val- T1Ptup(a, b) = temp
        in 
          a
        end
      )

        //x 
    end
)
//
| T2Msnd(t1) => (
    let 
        val temp = tinfer0_env(t1, ctx0)
    in
        case- temp of
        | T1Ptup(x, y) => x 
        | T1Pext(x) => (
          let
            val ntup = T1Ptup(t1ype_new_ext(), t1ype_new_ext())
            val- 00 = t1ype_unify(temp, ntup)
            val- T1Ptup(a, b) = temp
          in 
            b 
          end
        )
        
    end
)
//
| T2Mann(t2e, t1y) => (
    let
        val t2 = tinfer0_env(t2e, ctx0)
        val-00 = t1ype_unify(t2, t1y)
    in
        t1y
    end
)
//
| T2Mnil() => T1Plst(t1ype_new_ext())
//
| T2Mcons(t2e1, t2e2) => ( //assuming that the entire list must have the same type (or a nil at the end)
    T2 where {
      val T1 = tinfer0_env(t2e1, ctx0)
      val T2 = tinfer0_env(t2e2, ctx0)
      val- 00 = t1ype_unify(T1Plst(T1), T2)
    }
    (*
    let
      val- T1Plst(y) = tinfer0_env(t2e2, ctx0)
      val x = tinfer0_env(t2e1, ctx0)
      val- 00 = t1ype_unify(x, y)
        (*
        fun loop(ls: t2erm): t1ype =
        case+ ls of
        | T2Mcons(x1, x2) => (
            let
                val head = tinfer0_env(x1, ctx0)
                val- 00 = t1ype_unify(head, loop(x2))
            in
                head
            end
        )

        | T2Mnil() => t1ype_new_ext()
        | _ => (
          let
            val- T1Plst(z) = tinfer0_env(ls, ctx0) //fixed based on email. If trm0 is not a cons, it needs to evaluate to a T1Plst(something)
          in
            z
          end
        )
        
         exit(1) where {
            val () = println!("tinfer0_env: T2Mcons: second term not cons or nil ")
        } *)
    in 
        T1Plst(x)
    end
    *)
)
//
| T2Misnil(t2e) => (
    let
        val- T1Plst(_) = tinfer0_env(t2e, ctx0)

    in
        T1Pbtf
    end
)
//
| T2Mhead(t2e) => (
    let 
        val temp = tinfer0_env(t2e, ctx0)

    in
      case- temp of
      | T1Plst(x) => x 
      | T1Pext(_) => (
        let
          val nlst = T1Plst(t1ype_new_ext())
          val- 00 = t1ype_unify(temp, nlst)
          val- T1Plst(a) = temp
        in 
          a
        end
      )

        //x 
    end
)
//
| T2Mtail(t2e) => (

    case+ t2e of
    | T2Mcons(x,y) => tinfer0_env(y, ctx0) // this case is useful when y is just T2Mnil
    | _ => (
      let
        val temp = tinfer0_env(t2e, ctx0) //fixed based on email. Since the assumption is the entire list 
        //have the same type, the tail of a list with T1Plst(x) must also have type T1Plst(x)
      in
        case- temp of
        | T1Plst(x) => x 
        | T1Pext(_) => (
          let
            val nlst = T1Plst(t1ype_new_ext())
            val- 00 = t1ype_unify(temp, nlst)
          in
            temp
          end
        )

      end
    )

    (* exit(1) where {
            val () = println!("tinfer0_env: T2Mtail: not cons ")
        } *)
        
)
//
| T2Mref_new(t2e) => (
    T1Pref(x) where {
        val x = tinfer0_env(t2e, ctx0)
    }
)
//
| T2Mref_get(t2e) => (
    let
        val- T1Pref(x) = tinfer0_env(t2e, ctx0)
    in
        x
    end
)
//
| T2Mref_set(t2e1, t2e2) => (
    let
        val- T1Pref(x) = tinfer0_env(t2e1, ctx0)
        val y = tinfer0_env(t2e2, ctx0)
        val- 00 = t1ype_unify(x, y) //fixed based on email
    in
        T1Pbas("emp") // fixed based on email
    end
)
//
)
//
*)
(* ****** ****** *)
(* ****** ****** *)

(**************************************** End of tinfer************************************************)