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

//TODO: void init(int* ptr);
//map(void *f) { apply f } .. ?
