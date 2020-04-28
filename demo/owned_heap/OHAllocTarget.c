#include <stdio.h>   
#include <stdlib.h>

int* new() {
  int *key = malloc(sizeof(int));
  *key = 0;
  return key;
}

int get(int *key) {
  return *key;
}

void set(int *key, int val) {
  *key = val;
}





void delete(int *key) {
  free(key);
}

typedef int (*int_func_int) (int);

void map(int *key, int_func_int f) {
  *key = f(*key);
}

void publicize(int *key) {
}

void privatize(int *key) {
}

void init(int *key) {
  *key = 0;
}

void fini(int *key) {
}

