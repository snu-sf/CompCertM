int iter(int (*fptr)(int), int n, int x) {
  if(n == 0) return x;
  return iter(fptr, n-1, fptr(x));
}
