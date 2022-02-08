
#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"

extern fun int_test(): int
implement
int_test() = (
  let fun loop(i: int, x: int) : int =
  (
    if 
    (x != 0)
    then loop(i+1, x*2)
    else i
  )
  in loop(0,1)
  end
)


fun ghaap(n: int): int =
(
  if
  (n >= 2)
  then n * ghaap(n-1) * ghaap(n-2)
  else (n+1)
  // end of [if]
)

fun gheeper(i: int, n_i: int, n_ii: int, n): int =
(
  if (i <= n) 
  then gheeper(i+1, ((i)*n_i*n_ii), n_i, n) 
  else n_i

)

extern fun gheep(n: int): int
implement
gheep(n) = (
  if (n < 2)
  then (n+1)
  else gheeper(2, 2, 1, n)
)




datatype
intlist =
| intlist_nil of ()
| intlist_cons of (int, intlist)
//
#define nil intlist_nil
#define :: intlist_cons
#define cons intlist_cons

fun reverse_list(x: intlist, y: intlist): intlist =
  case+ x of
  |intlist_nil() => y
  |intlist_cons(t, xs) =>  reverse_list(xs, intlist_cons(t,y))

fun reverse_wrp(x: intlist): intlist =
  reverse_list(x, intlist_nil())

fun intlist_appender(x: intlist, y: intlist): intlist =
  case+ x of
  |intlist_nil() => y
  |intlist_cons(t, xs) => intlist_appender(xs, intlist_cons(t, y))

extern
fun
intlist_append : (intlist, intlist) -> intlist
implement
intlist_append(x, y) =
  intlist_appender( reverse_wrp(x),y)

fun prnt_list(x : intlist): void =
  case+ x of
  |intlist_nil() => println!("end")
  |intlist_cons(t, xs) =>  (println!(t); prnt_list(xs))
                         
//
(* ****** ****** *)
implement main0() = ()
//println!(int_test())
//println!("factorial(10) = ", 11)
//prnt_list(intlist_append( intlist_cons(1, intlist_cons(2, intlist_nil())), intlist_cons(3, intlist_nil())))
//println!("Ghaap = ", ghaap(5), " Gheep = ", gheep(5))
(* end of [assign00.dats] *)