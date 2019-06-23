extern int g(int x);

static int memoized[1000] = { 0 };

int f(int x) {
  int t;
  if(x == 0) return 0;
  t = memoized[x];
  if(t < 0) {
    t = g(x-1) + x;
    memoized[x] = t;
  }
  return t;
}
