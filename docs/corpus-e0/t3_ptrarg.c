void set(int *p) { *p = 4; }
int main(void) { int x = 0; set(&x); return x; }
