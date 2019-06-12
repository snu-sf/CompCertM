extern int f(int x);

int g(int x) {
  if(x == 0) return 0;
  return f(x-1) + x;
}
