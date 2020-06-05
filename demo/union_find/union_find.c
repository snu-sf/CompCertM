#include "stdio.h"
#include "stdlib.h"

struct Node {
  unsigned int rank;
  struct Node * parent;
};

struct Node* makeSet() {
  struct Node * x;
  x = (struct Node *) malloc (sizeof (struct Node));
  x -> parent = x;
  x -> rank = 0;
  return x;
}

struct Node* find(struct Node* x) {
  struct Node *p, *p0;
  p = x -> parent;
  if (p != x) {
    p0 = find(p);
    p = p0;
    x -> parent = p;
  }
  return p;
};

void unionS(struct Node* x, struct Node* y) {
  struct Node *xRoot, *yRoot;
  unsigned int xRank, yRank;
  xRoot = find(x);
  yRoot = find(y);
  if (xRoot == yRoot) {
    return;
  }
  xRank = xRoot -> rank;
  yRank = yRoot -> rank;
  if (xRank < yRank) {
    xRoot -> parent = yRoot;
  } else if (xRank > yRank) {
    yRoot -> parent = xRoot;
  } else {
    yRoot -> parent = xRoot;
    xRoot -> rank = xRank + 1;
  }
};

/////////////////////////////////////////////////

int same_set(struct Node* x, struct Node *y) {
  return (find(x) == find(y));
}

