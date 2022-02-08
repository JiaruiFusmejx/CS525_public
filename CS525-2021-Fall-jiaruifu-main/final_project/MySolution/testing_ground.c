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
    case TAGbtf:
      printf("%s", ((lamval_btf)x)->data ? "true" : "false");  break;
      //printf("%s", ((lamval_btf)x)->data); break;
    case TAGemp:
      printf("empty"); break;
    case TAGtup:
      //printf("Tuple: ( ", LAMVAL_print(((lamval_tup)x)->data2), "; ", LAMVAL_print(((lamval_tup)x)->data3) , " )");  
      printf("Tuple: ( ");  
      LAMVAL_print(((lamval_tup)x)->data2);
      printf("; ");
      LAMVAL_print(((lamval_tup)x)->data3);
      printf(" )");
      break;
    case TAGcon:
      printf("Cons: ( ");  
      LAMVAL_print(((lamval_con)x)->data1);
      printf("; ");
      LAMVAL_print(((lamval_con)x)->data2);
      printf(" )");

      break;

    /*  
    case TAGref:
      printf("Ref: %p", ((lamval_ref)x)->data);
      printf("\n");
      //LAMVAL_print(((lamval_ref)x)->data);
      break;
     */ 
    default: printf("Unrecognized tag = %i", tag);
  }
}

lamval fun(lamval test2){  return LAMVAL_str("returned something"); }


int main() {
  printf("Test:");
  LAMVAL_print(LAMVAL_str("true")) ; printf("\n");
  printf("Test2:");
  LAMVAL_print(LAMVAL_btf(true)) ; printf("\n");
  printf("Test3:");
  LAMVAL_print(LAMVAL_emp()) ; printf("\n");
  printf("Test4:");
  LAMVAL_print(LAMVAL_tup(LAMVAL_str("yada"), LAMVAL_btf(true))) ; printf("\n");
  printf("Test5:");
  //lamval i = LAMVAL_int(5);
  //((lamval)LAMVAL_int(5))
  //lamval j = (((lamval_ref)LAMVAL_ref(&i))->data);
  //LAMVAL_print(*(((lamval_ref)LAMVAL_ref(&i))->data)) ; printf("\n");
  
  printf("Testing compiled code from compiler 1:");printf("\n");
  LAMVAL_print(LAMOPR_add(LAMVAL_int(2), LAMVAL_int(3))) ; printf("\n");

  printf("Testing compiled code from compiler 2:");printf("\n");
  LAMVAL_print(LAMOPR_sub(LAMVAL_int(25), LAMVAL_int(4))) ; printf("\n");

  printf("Testing compiled code from compiler 3:");printf("\n");
  LAMVAL_print(fun(LAMVAL_int(25))) ; printf("\n");

  printf("Testing compiled code from compiler 4:");printf("\n");
  LAMVAL_print(LAMVAL_con(LAMVAL_emp(), LAMVAL_emp() )) ; printf("\n");

  printf("Testing compiled code from compiler 5:");printf("\n");
  LAMVAL_print(LAMVAL_tup(LAMVAL_int(4), LAMVAL_emp() )) ; printf("\n");

  printf("Testing compiled code from compiler 6:");printf("\n");
  LAMVAL_print(LAMOPR_fst(LAMVAL_tup(LAMVAL_int(4), LAMVAL_emp() ))) ; printf("\n");  

  printf("Testing compiled code from compiler 7:");printf("\n");
  //LAMVAL_print(if((lamval_btf)LAMOPR_igt(LAMVAL_int(2), LAMVAL_int(3)))->data){LAMVAL_str(first is greater); }else{ LAMVAL_str(second is greater); }) ; printf("\n");  
  return 0;
}
