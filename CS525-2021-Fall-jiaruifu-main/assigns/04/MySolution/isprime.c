/* ****** ****** */

#include "runtime.h"

/* ****** ****** */

extern
lamval
LAMVAL_print(lamval x)
{
  int tag;
  tag = x->tag;
  switch( tag )
  {
    case TAGcfn:
      printf("<lamval_cfn>"); break;
    case TAGint:
      printf("%i", ((lamval_int)x)->data); break;
    case TAGstr:
      printf("%s", ((lamval_str)x)->data); break;
    default: printf("Unrecognized tag = %i", tag);
  }
}

/* ****** ****** */

/*
(*
//
// HX: 20 points
// Please implement 'isprime' in C using
// the boxed data representation covered
// in the lectures on 10/27 and 10/29.
//
*)
(* ****** ****** *)

(*
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
*/
lamval 
isprime(lamval n)
{
  lamval t0;
  lamval r0, r1, r2, r3, r4, r5;

  /*
  printf("isprime(");
  LAMVAL_print(n);
  printf(") = ...\n");
  */

  r1 = n;
  r2 = LAMVAL_int(2);
  
  t0 = ((lamval)LAMOPR_ige(r1, LAMVAL_int(2)));
  //printf("print t0, 1 for ige 2, 0 otherwise");
  //LAMVAL_print(t0);printf("\n");

  if (((lamval_int)t0)->data){
    r3 = ((lamval)LAMOPR_ilt(r2, r1));

    //printf("print r3, 1 for i ile x, 0 otherwise");
    //LAMVAL_print(r3);printf("\n");

    while(((lamval_int)r3)->data){
      r4 = ((lamval)LAMOPR_mod(r1, r2));

      //printf("print r4, x mod i: ");
      //LAMVAL_print(r4);printf("\n");

      r5 = ((lamval)LAMOPR_ieq(r4, LAMVAL_int(0)));

      //printf("print r5, is mod == 0: ");
      //LAMVAL_print(r5);printf("\n");

      if (((lamval_int)r5)->data){
        r0 = LAMVAL_int(0);
        //printf("found factor: ");
        return r0;
        //break;
      }else{
        r2 = LAMOPR_add(r2, LAMVAL_int(1));
        r3 = ((lamval)LAMOPR_ilt(r2, r1));
      }
    }
    r0 = LAMVAL_int(1);
  }else {
    r0 = LAMVAL_int(1);
  }
  return r0;
}


int main() {
  printf("1 for true, 0 for false\n");
  printf("Is 2 a prime: ");
  LAMVAL_print(isprime(LAMVAL_int(2))); printf("\n"); 
  printf("Is 3 a prime: ");
  LAMVAL_print(isprime(LAMVAL_int(3))); printf("\n"); 
  printf("Is 10 a prime: ");
  LAMVAL_print(isprime(LAMVAL_int(10))); printf("\n"); 
  printf("Is 21 a prime: ");
  LAMVAL_print(isprime(LAMVAL_int(21))); printf("\n"); 
  printf("Is 19 a prime: ");
  LAMVAL_print(isprime(LAMVAL_int(19))); printf("\n"); 
  return 0;
}
