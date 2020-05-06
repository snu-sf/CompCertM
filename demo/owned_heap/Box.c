#include <stdio.h>   
#include <stdlib.h>

typedef int T;

void* new(T v) {
  /* T *key = malloc(sizeof(T)); */
  /* *key = 0; */
  T *key = malloc(sizeof(T));
  *key = v;
  return key;
}

T get(void *key) {
  return *(T *)key;
}

void set(void *key, T val) {
  *(T *)key = val;
}


/*** NOTE: Supporting below functions would require "abstraction relation" ***/
/* new_uninit */
/* new_zeroed */
/* assume_init */ // <- TODO: this can be somewhat interesting? not sure

/* pub unsafe fn from_raw(raw: *mut T) -> Box<T> */     //this is equivalent to "init"
/* pub fn into_raw(b: Box<T>) -> *mut T */     //this is equivalent to "fini"
//NOTE: it seems into_raw != fini. See https://doc.rust-lang.org/std/rc/struct.Rc.html#method.into_raw
//In kaist-cp/cs420, into_raw is used for int2ptr cast.
/* pub fn leak<'a>(b: Box<T>) -> &'a mut T */     // <- TODO: this can be somewhat interesting?





void delete(void *key) {
  free(key);
}

// duplicate of "into_raw"?
/* void publicize(int *key) { */
/* } */

// duplicate of "from_raw"?
/* void privatize(int *key) { */
/* } */


// A degenerated version of "into_raw"
void init(void *key) {
}

// A degenerated version of "from_raw"
void fini(void *key) {
}

/* typedef int (*int_func_int) (int); */

/* void map(int *key, int_func_int f) { */
/*   *key = f(*key); */
/* } */
