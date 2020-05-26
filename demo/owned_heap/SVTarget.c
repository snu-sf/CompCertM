static int x = 0;

int get() {
  if(x >= 0) return x;
  else return -1;
}

void incr() {
  x = (x+1)%10;
}
