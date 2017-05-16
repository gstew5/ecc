#include <stdio.h>
#include <stdbool.h>
#include <assert.h>

#define N 3

typedef bool CODE[N];

CODE code0;
CODE code1;

CODE* encode(bool b) {
  if (b == 0) return &code0;
  else if (b == 1) return &code1;
  else assert(0);
}

//Hamming distance between c and d
int hamming(CODE c, CODE d) {
  int sum = 0;
  for (int i=0; i < N; i++) {
    sum += c[i]^d[i];
  }
  return sum;
}

bool decode(CODE c) {
  int d0 = hamming(code0, c);
  int d1 = hamming(code1, c);

  if (d0 < d1) { return 0; }
  else if (d0 > d1) { return 1; }
  else assert(0); //decoding failed
}

bool nondet_bit(void); //nondeterministically generate a bit
int nondet_int(void); //nondeterministically generate an integer

//channel model
CODE channel;
CODE* syndrome(CODE c) {
  //copy code c into channel
  for (int i = 0; i < N; i++) {
    channel[i] = c[i];
  }
  //apply syndrome
  for (int n = 1; n <= N/2; n++) {
    int i = nondet_int();
    __CPROVER_assume(0 <= i && i < N);    
    channel[i] = nondet_bit();
  }
  return &channel;
}

int main(void) {
  //initialize codes 0 and 1
  for (int i = 0; i < N; i++) {
    code0[i] = 0;
    code1[i] = 1;
  }

  //encode
  bool b1 = nondet_bit();
  int i1 = nondet_int();
  __CPROVER_assume(0 <= i1 && i1 < N);
  assert((*encode(b1))[i1] == b1);

  //syndrome
  CODE c1;
  for (int i = 0; i < N; i++) c1[i] = nondet_bit();
  assert(hamming(c1, *syndrome(c1)) <= N/2);
  
  //decode
  CODE c2;
  for (int i = 0; i < N; i++) c2[i] = nondet_bit();
  if (hamming(c2, code0) < hamming(c2, code1))
    assert(decode(c2) == 0);
  if (hamming(c2, code1) < hamming(c2, code0))
    assert(decode(c2) == 1);
  
  //\forall b, decode(*syndrome(*encode(b))) == b
  /*bool b1 = nondet_bit();
  bool b2 = decode(*syndrome(*encode(b1)));
  assert (b1 == b2);*/
}


