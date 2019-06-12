extern int g(int x);

int f(int x) {
  if(x == 0) return 0;
  return g(x-1) + x;
}
