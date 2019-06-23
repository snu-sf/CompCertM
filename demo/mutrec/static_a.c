extern int g(int x);

static int memoized[10] = {-1, -1, -1, -1, -1, -1, -1, -1, -1, -1};

int f(int x) {
  if(x == 0) return 0;
  if(memoized[x] < 0) {
    memoized[x] = g(x-1) + x;
  }
  return memoized[x];
}
