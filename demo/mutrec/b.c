static int in = 0;
static int out = 0;

extern int g(int x);

int f(int x) {
  if(x != in) {
    in = x;
    out = x * x;
  }
  return g(out);
}
