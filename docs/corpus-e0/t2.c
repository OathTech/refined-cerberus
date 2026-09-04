int add(int a, int b) { return a + b; }
int main(void) { int s = 0; for (int i = 0; i < 3; i++) { s = add(s, i); } return s; }
