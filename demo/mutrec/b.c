extern int f(int x);

static int memoized[2] = { 0, 0 };

int g(int x) {
  int t_i, t_v;
  if(x == 0) return 0;
  t_i = memoized[0];
  if(x == t_i) {
    t_v = memoized[1];
  }
  else {
    t_v = f(x-1) + x;
    memoized[0] = x;
    memoized[1] = t_v;
  }
  return t_v;
}
