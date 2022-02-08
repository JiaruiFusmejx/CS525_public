/*
// A basic runtime for lambda
*/

/* ****** ****** */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

/* ****** ****** */

extern
void*
mymalloc(size_t);

/* ****** ****** */

#define TAGint 1
#define TAGstr 2
#define TAGdbl 3
#define TAGcfn 4 // closure function
#define TAGbtf 5
#define TAGemp 6
#define TAGtup 7
#define TAGref 8
#define TAGnil 9
#define TAGcon 10

/* ****** ****** */

typedef
struct{ int tag; } lamval_;
/*
typedef
lamval_ = struct{ int tag; }
*/

typedef lamval_ *lamval;
/*
typedef *lamval = lamval_
*/

/* ****** ****** */

int
LAMVAL_tag(lamval x){ return x->tag; }

/* ****** ****** */

typedef
struct{
  int tag; int data;
} lamval_int_;
typedef
struct{
  int tag; char *data;
} lamval_str_;
typedef
struct{
  int tag; double data;
} lamval_dbl_;
typedef
struct{
  int tag; bool data;
} lamval_btf_;

typedef
struct{
  int tag;
} lamval_emp_;

typedef
struct{
  int tag;
  int tag2;
  int tag3;
  lamval data2;
  lamval data3;
} lamval_tup_;

typedef
struct{
  int tag;
  lamval data1;
  lamval data2;
} lamval_con_;

typedef
struct{
  int tag;
} lamval_nil_;


typedef
struct{
  int tag; 
  lamval *data;
} lamval_ref_;


typedef lamval_int_ *lamval_int;
typedef lamval_str_ *lamval_str;
typedef lamval_dbl_ *lamval_dbl;
typedef lamval_btf_ *lamval_btf;
typedef lamval_emp_ *lamval_emp;
typedef lamval_tup_ *lamval_tup;
typedef lamval_ref_ *lamval_ref;
typedef lamval_con_ *lamval_con;
typedef lamval_nil_ *lamval_nil;

/* ****** ****** */

extern
void*
mymalloc(size_t n) {
  void* p0;
  p0 = malloc(n);
  if (p0 != 0) return p0;
  fprintf(stderr, "myalloc failed!!!\n");
  exit(1);
}

/* ****** ****** */

extern
lamval
LAMVAL_int(int i)
{
  lamval_int p0;
  p0 = mymalloc(sizeof(lamval_int_));
  p0->tag = TAGint; p0->data = i; return (lamval)p0;
}

extern
lamval
LAMVAL_btf(bool b)
{
  lamval_btf p0;
  p0 = mymalloc(sizeof(lamval_btf_));
  p0->tag = TAGbtf; p0->data = b; return (lamval)p0;
}

extern
lamval
LAMVAL_str(char *s)
{
  lamval_str p0;
  p0 = mymalloc(sizeof(lamval_str_));
  p0->tag = TAGstr; p0->data = s; return (lamval)p0;
}

extern
lamval
LAMVAL_emp()
{
  lamval_emp p0;
  p0 = mymalloc(sizeof(lamval_emp_));
  p0->tag = TAGemp; return (lamval)p0;
}

extern
lamval
LAMVAL_tup(lamval fst, lamval snd)
{
  lamval_tup p0;
  p0 = mymalloc(sizeof(lamval_tup_));
  p0->tag = TAGtup; 
  p0->tag2 = (fst->tag);
  p0->tag3 = (snd->tag);
  p0->data2 = fst;
  p0->data3 = snd;
  return (lamval)p0;
}

extern
lamval
LAMVAL_con(lamval head, lamval tail)
{
  lamval_con p0;
  p0 = mymalloc(sizeof(lamval_con_));
  p0->tag = TAGcon; 
  p0->data1 = head;
  p0->data2 = tail;
  return (lamval)p0;
}

extern
lamval
LAMVAL_nil()
{
  lamval_nil p0;
  p0 = mymalloc(sizeof(lamval_nil_));
  p0->tag = TAGnil; return (lamval)p0;
}

extern
lamval
LAMVAL_ref(lamval *r)
{
  lamval_ref p0;
  p0 = mymalloc(sizeof(lamval_ref_));
  p0->tag = TAGref; p0->data = r; return (lamval)p0;
}

/* ****** ****** */

extern
lamval
LAMOPR_isn(lamval x)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  if(x->tag == TAGnil){
    return LAMVAL_btf(true);
  }else{
    return LAMVAL_btf(false);
  }
  
}

extern
lamval
LAMOPR_head(lamval x)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  ((lamval_con)x)->data1;
}

extern
lamval
LAMOPR_tail(lamval x)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  ((lamval_con)x)->data2;
}

extern
lamval
LAMOPR_fst(lamval x)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  ((lamval_tup)x)->data2;
}

extern
lamval
LAMOPR_snd(lamval x)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  ((lamval_tup)x)->data3;
}

extern
lamval
LAMOPR_add(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  LAMVAL_int(((lamval_int)x)->data + ((lamval_int)y)->data);
}

extern
lamval
LAMOPR_sub(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);ppp
  */
  return
  LAMVAL_int(((lamval_int)x)->data - ((lamval_int)y)->data);
}

/* ****** ****** */

extern
lamval
LAMOPR_mul(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  LAMVAL_int(((lamval_int)x)->data * ((lamval_int)y)->data);
}

/* ****** ****** */

extern
lamval
LAMOPR_div(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  LAMVAL_int(((lamval_int)x)->data / ((lamval_int)y)->data);
}

extern
lamval
LAMOPR_mod(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  LAMVAL_int(((lamval_int)x)->data % ((lamval_int)y)->data);
}

/* ****** ****** */

extern
lamval
LAMOPR_ilt(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);
  */
  return
  LAMVAL_btf(((lamval_int)x)->data < ((lamval_int)y)->data ? true : false);
}

extern
lamval
LAMOPR_ile(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);ppp
  */
  return
  LAMVAL_btf(((lamval_int)x)->data <= ((lamval_int)y)->data ? true : false);
}

/* ****** ****** */

extern
lamval
LAMOPR_igt(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);ppp
  */
  return
  LAMVAL_btf(((lamval_int)x)->data > ((lamval_int)y)->data ? true : false);
}

extern
lamval
LAMOPR_ige(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);ppp
  */
  return
  LAMVAL_btf(((lamval_int)x)->data >= ((lamval_int)y)->data ? true : false);
}

/* ****** ****** */

extern
lamval
LAMOPR_ieq(lamval x, lamval y)
{
  /*
  assert(x->tag == TAGint);
  assert(y->tag == TAGint);ppp
  */
  return
  LAMVAL_btf(((lamval_int)x)->data == ((lamval_int)y)->data ? true : false);
}
