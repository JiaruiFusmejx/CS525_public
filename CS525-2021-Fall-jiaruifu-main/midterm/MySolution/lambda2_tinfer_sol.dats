(* ****** ****** *)
#dynload
"./../lambda1.dats"
(* ****** ****** *)
//
#include
"./../lambda2_tinfer.dats"
//
(* ****** ****** *)

(*
datatype t1ype =
  | T1Pext of t1xyz
  | T1Pbas of string
//
  | T1Plst of (t1ype)
//
  | T1Pref of (t1ype)
//
  | T1Pfun of (t1ype, t1ype)
  | T1Ptup of (t1ype, t1ype)
//
*)

implement main0() = ((*dummy*))
(* ****** ****** *)

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

(* ****** ************ ************ end of code supporting t2var_equal ************ ************ ****** *)

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
  if (x0 = x1)
  then myoptn_cons(T1)
  else t2var_infer1(x0, ctx1)
)

(* ****** ************ ************ ************ ************ ****** *)

val T1Pvoid = T1Pbas("void")
val T1Pint = T1Pbas("int")
val T1Pbtf = T1Pbas("btf")
val T1Pstr = T1Pbas("str")


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
        val- T1Ptup(x, y) = tinfer0_env(t1, ctx0)
    in
        x 
    end
)
//
| T2Msnd(t1) => (
    let 
        val- T1Ptup(x, y) = tinfer0_env(t1, ctx0)
    in
        y 
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
| T2Mnil() => T1Plst(T1Pbas("nil"))
//
| T2Mcons(t2e1, t2e2) => (
    let
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
        | _ => exit(1) where {
            val () = println!("tinfer0_env: T2Mcons: second term not cons or nil ")
        }
    in 
        T1Plst(loop(trm0))
    end
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
        val- T1Plst(x) = tinfer0_env(t2e, ctx0)
    in
        x 
    end
)
//
| T2Mtail(t2e) => (

    case+ t2e of
    | T2Mcons(x,y) => tinfer0_env(y, ctx0)
    | _ => exit(1) where {
            val () = println!("tinfer0_env: T2Mtail: not cons ")
        }
        
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
    in
        T1Pref(y)
    end
)
//
)
//
(* ****** ****** *)
(* ****** ****** *)
(****************************************************************************************)


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
T0Migt(T1: term0, T2: term0): term0
implement
T0Migt(T1, T2) = T0Mopr(">", T1:: T2 :: nil() )



val tadd23 = T2Mopr("+", mylist_cons(T2Mint(2), mylist_cons(T2Mint(3), mylist_nil())))
val ref_add23 = T2Mref_new(tadd23)
val get_ref = T2Mref_get(ref_add23)

val ty_tadd23 = tinfer0(tadd23)
val ty_rad23 = tinfer0(ref_add23)
val ty_gr = tinfer0(get_ref)
val ty_igt_2 = tinfer0(igt_2)

val () = println!("tadd23: ", tadd23, " tadd23 after tinfer0: ", ty_tadd23)

val () = println!("ref_add23: ", ref_add23, " ref_add23 after tinfer0: ", ty_rad23)
val () = println!("get_ref: ", get_ref, " get_ref after tinfer0: ", ty_gr)


(* end of [lambda2_tinfer_sol.dats] *)

