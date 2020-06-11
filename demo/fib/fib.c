int fib(int n) {
  if(n == 0)
    return 0;
  if(n == 1)
    return 1;
  int y1 = fib(n-2);
  int y2 = fib(n-1);
  return y1 + y2;
}
