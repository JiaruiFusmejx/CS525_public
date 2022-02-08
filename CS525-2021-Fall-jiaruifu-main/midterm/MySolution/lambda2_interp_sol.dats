(* ****** ****** *)
#dynload
"./../lambda1.dats"

(* ****** ****** *)
//
#include
"./../lambda2_interp.dats"

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

implement
t2var_equal
(X1, X2) = (X1.stamp() = X2.stamp())


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
    (!x := update; T2Vref(x))

  end
)
)
//
(****************************************************************************************)



(* ****** ****** *)

implement
print_t2erm(t0) = 
fprint_t2erm(stdout_ref, t0)
implement
prerr_t2erm(t0) = 
fprint_t2erm(stderr_ref, t0)

local

implement
fprint_val<t2erm> = fprint_t2erm

in (* in-of-local *)

implement
fprint_t2erm
  (out, t0) =
(
case+ t0 of
//
| T2Memp() =>
  fprint!(out, "T2Memp(", ")")
//
| T2Mint(x) =>
  fprint!(out, "T2Mint(", x, ")")
| T2Mbtf(x) =>
  fprint!(out, "T2Mbtf(", x, ")")
//
| T2Mnil() =>
  fprint!(out, "T2Mnil(", ")")
//
| T2Mstr(x) =>
  fprint!(out, "T2Mstr(", x, ")")
//
| T2Mvar(x) =>
  fprint!(out, "T2Mvar(", x, ")")
//
| T2Mlam(x1, T1, t2) =>
  fprint!(out, "T2Mlam(", x1, "; ", t2, ")")
//
| T2Mapp(t1, t2) =>
  fprint!(out, "T2Mapp(", t1, "; ", t2, ")")
//
| T2Mopr(opr, ts) =>
  fprint!(out, "T2Mopr(", opr, "; ", ts)
//
| T2Mlet(x, t1, t2) =>
  fprint!(out, "T2Mlet(", x, "; ", t1, "; ", t2, ")")
//
| T2Mift(t1, t2, t3) =>
  fprint!(out, "T2Mift(", t1, "; ", t2, "; ", t3, ")")
//
| T2Mfix(f1, x2, T1, T2, t3) =>
  fprint!(out, "T2Mfix(", f1, "; ", x2, "; ", t3, ")")
//
| T2Mtup(t1, t2) =>
  fprint!(out, "T2Mtup(", t1, "; ", t2, ")")
//
| T2Mfst(t1) =>
  fprint!(out, "T2Mfst(", t1, ")")
| T2Msnd(t1) =>
  fprint!(out, "T2Msnd(", t1, ")")
//
| T2Mann(t1, T2) =>
  fprint!(out, "T2Mann(", t1, "; ", T2, ")")
//
| T2Mcons(t1, t2) =>
  fprint!(out, "T2Mcons(", t1, "; ", t2, ")")
| T2Mhead(t1) =>
  fprint!(out, "T2Mhead(", t1, ")")
| T2Mtail(t1) =>
  fprint!(out, "T2Mtail(", t1, ")")
| T2Misnil(t1) =>
  fprint!(out, "T2Misnil(", t1, ")")
//
| T2Mref_new(t1) =>
  fprint!(out, "TMref_new(", t1, ")")
| T2Mref_get(t1) =>
  fprint!(out, "TMref_get(", t1, ")")
| T2Mref_set(t1, t2) =>
  fprint!(out, "TMref_set(", t1, ", ", t2, ")")
//
(*
| T2Marr_new(t1, t2) =>
  fprint!(out, "TMarr_new(", t1, ", ", t2, ")")
| T2Marr_size(t1) =>
  fprint!(out, "TMarr_size(", t1, ")")
| T2Marr_get_at(t1, t2) =>
  fprint!(out, "TMarr_get_at(", t1, ", ", t2, ")")
| T2Marr_set_at(t1, t2, t3) =>
  fprint!(out, "TMarr_set_at(", t1, ", ", t2, ", ", t3, ")")
*)
//
) (* end of [fprint_t2erm] *)

end // end of [local]

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
(* ****** ****** *)
val tadd23 = T2Mopr("+", mylist_cons(T2Mint(2), mylist_cons(T2Mint(3), mylist_nil())))
val ref_add23 = T2Mref_new(tadd23)
val get_ref = T2Mref_get(ref_add23)

val eval_t23 = interp0(tadd23)
val eval_ref_t23 = interp0(ref_add23)
val eval_gr = interp0(get_ref)

val () = println!("tadd23: ", tadd23)

val () = println!("tadd23: ", tadd23, " tadd23 after interp0: ", eval_t23)

val () = println!("ref_add23: ", ref_add23, " ref_add23 after interp0: ", eval_ref_t23)
val () = println!("get_ref: ", get_ref, " get_ref after interp0: ", eval_gr)


(* end of [lambda2_interp_sol.dats] *)
