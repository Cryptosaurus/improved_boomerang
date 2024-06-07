// Boomerang attack on 6-round mini-AES

// Implementation of Algorithm 3 from paper 'Improved Boomerang Attacks on 6-round AES'
// Based on the code from https://github.com/AugustinBariant/Truncated_boomerangs

// Written by Gaetan Leurent gaetan.leurent@inria.fr (2024)
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to the
// public domain worldwide. This software is distributed without any
// warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software. If not, see
// <http://creativecommons.org/publicdomain/zero/1.0/>.

#define _XOPEN_SOURCE 500
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>

// #define VERBOSE

#define tabsize(t) (sizeof(t)/sizeof((t)[0]))

/***********************************/
/* T-tables based AES              */
/***********************************/

#define N 4
#define R 6

typedef uint16_t word;
#define MASK 0xf
#define M0 0xf000
#define M1 0xf00
#define M2 0xf0
#define M3 0xf
#include "tables4.h"

typedef word state[4];

void AddKey(state x, state k) {
  x[0] ^= k[0];
  x[1] ^= k[1];
  x[2] ^= k[2];
  x[3] ^= k[3];
}

void  __attribute__((always_inline)) Round(state x, state y) {
    y[0] = Te0[(x[0] >> (3*N)) & MASK] ^
           Te1[(x[1] >> (2*N)) & MASK] ^
           Te2[(x[2] >> (1*N)) & MASK] ^
           Te3[(x[3] >> (0*N)) & MASK];
    y[1] = Te0[(x[1] >> (3*N)) & MASK] ^
           Te1[(x[2] >> (2*N)) & MASK] ^
           Te2[(x[3] >> (1*N)) & MASK] ^
           Te3[(x[0] >> (0*N)) & MASK];
    y[2] = Te0[(x[2] >> (3*N)) & MASK] ^
           Te1[(x[3] >> (2*N)) & MASK] ^
           Te2[(x[0] >> (1*N)) & MASK] ^
           Te3[(x[1] >> (0*N)) & MASK];
    y[3] = Te0[(x[3] >> (3*N)) & MASK] ^
           Te1[(x[0] >> (2*N)) & MASK] ^
           Te2[(x[1] >> (1*N)) & MASK] ^
           Te3[(x[2] >> (0*N)) & MASK];
}

void  __attribute__((always_inline)) RoundInv(state x, state y) {
  y[0] = Td0[(x[0] >> (3*N)) & MASK] ^
         Td1[(x[3] >> (2*N)) & MASK] ^
         Td2[(x[2] >> (1*N)) & MASK] ^
         Td3[(x[1] >> (0*N)) & MASK];
  y[1] = Td0[(x[1] >> (3*N)) & MASK] ^
         Td1[(x[0] >> (2*N)) & MASK] ^
         Td2[(x[3] >> (1*N)) & MASK] ^
         Td3[(x[2] >> (0*N)) & MASK];
  y[2] = Td0[(x[2] >> (3*N)) & MASK] ^
         Td1[(x[1] >> (2*N)) & MASK] ^
         Td2[(x[0] >> (1*N)) & MASK] ^
         Td3[(x[3] >> (0*N)) & MASK];
  y[3] = Td0[(x[3] >> (3*N)) & MASK] ^
         Td1[(x[2] >> (2*N)) & MASK] ^
         Td2[(x[1] >> (1*N)) & MASK] ^
         Td3[(x[0] >> (0*N)) & MASK];
}

void SRSB(state x) {
  state y;
  y[0] = (Te4[(x[0] >> (3*N)) & MASK] & M0) ^
         (Te4[(x[1] >> (2*N)) & MASK] & M1) ^
         (Te4[(x[2] >> (1*N)) & MASK] & M2) ^
         (Te4[(x[3] >> (0*N)) & MASK] & M3);
  y[1] = (Te4[(x[1] >> (3*N)) & MASK] & M0) ^
         (Te4[(x[2] >> (2*N)) & MASK] & M1) ^
         (Te4[(x[3] >> (1*N)) & MASK] & M2) ^
         (Te4[(x[0] >> (0*N)) & MASK] & M3);
  y[2] = (Te4[(x[2] >> (3*N)) & MASK] & M0) ^
         (Te4[(x[3] >> (2*N)) & MASK] & M1) ^
         (Te4[(x[0] >> (1*N)) & MASK] & M2) ^
         (Te4[(x[1] >> (0*N)) & MASK] & M3);
  y[3] = (Te4[(x[3] >> (3*N)) & MASK] & M0) ^
         (Te4[(x[0] >> (2*N)) & MASK] & M1) ^
         (Te4[(x[1] >> (1*N)) & MASK] & M2) ^
         (Te4[(x[2] >> (0*N)) & MASK] & M3);
  
  memcpy(x, y, sizeof(state));
}

void SRSBInv(state x) {
  state y;
  y[0] = (Td4[(x[0] >> (3*N)) & MASK] & M0) ^
         (Td4[(x[3] >> (2*N)) & MASK] & M1) ^
         (Td4[(x[2] >> (1*N)) & MASK] & M2) ^
         (Td4[(x[1] >> (0*N)) & MASK] & M3);
  y[1] = (Td4[(x[1] >> (3*N)) & MASK] & M0) ^
         (Td4[(x[0] >> (2*N)) & MASK] & M1) ^
         (Td4[(x[3] >> (1*N)) & MASK] & M2) ^
         (Td4[(x[2] >> (0*N)) & MASK] & M3);
  y[2] = (Td4[(x[2] >> (3*N)) & MASK] & M0) ^
         (Td4[(x[1] >> (2*N)) & MASK] & M1) ^
         (Td4[(x[0] >> (1*N)) & MASK] & M2) ^
         (Td4[(x[3] >> (0*N)) & MASK] & M3);
  y[3] = (Td4[(x[3] >> (3*N)) & MASK] & M0) ^
         (Td4[(x[2] >> (2*N)) & MASK] & M1) ^
         (Td4[(x[1] >> (1*N)) & MASK] & M2) ^
         (Td4[(x[0] >> (0*N)) & MASK] & M3);
  
  memcpy(x, y, sizeof(state));
}

void SB(state x) {
  state y;
  y[0] = (Te4[(x[0] >> (3*N)) & MASK] & M0) ^
         (Te4[(x[0] >> (2*N)) & MASK] & M1) ^
         (Te4[(x[0] >> (1*N)) & MASK] & M2) ^
         (Te4[(x[0] >> (0*N)) & MASK] & M3);
  y[1] = (Te4[(x[1] >> (3*N)) & MASK] & M0) ^
         (Te4[(x[1] >> (2*N)) & MASK] & M1) ^
         (Te4[(x[1] >> (1*N)) & MASK] & M2) ^
         (Te4[(x[1] >> (0*N)) & MASK] & M3);
  y[2] = (Te4[(x[2] >> (3*N)) & MASK] & M0) ^
         (Te4[(x[2] >> (2*N)) & MASK] & M1) ^
         (Te4[(x[2] >> (1*N)) & MASK] & M2) ^
         (Te4[(x[2] >> (0*N)) & MASK] & M3);
  y[3] = (Te4[(x[3] >> (3*N)) & MASK] & M0) ^
         (Te4[(x[3] >> (2*N)) & MASK] & M1) ^
         (Te4[(x[3] >> (1*N)) & MASK] & M2) ^
         (Te4[(x[3] >> (0*N)) & MASK] & M3);
  
  memcpy(x, y, sizeof(state));
}

void SBInv(state x) {
  state y;
  y[0] = (Td4[(x[0] >> (3*N)) & MASK] & M0) ^
         (Td4[(x[0] >> (2*N)) & MASK] & M1) ^
         (Td4[(x[0] >> (1*N)) & MASK] & M2) ^
         (Td4[(x[0] >> (0*N)) & MASK] & M3);
  y[1] = (Td4[(x[1] >> (3*N)) & MASK] & M0) ^
         (Td4[(x[1] >> (2*N)) & MASK] & M1) ^
         (Td4[(x[1] >> (1*N)) & MASK] & M2) ^
         (Td4[(x[1] >> (0*N)) & MASK] & M3);
  y[2] = (Td4[(x[2] >> (3*N)) & MASK] & M0) ^
         (Td4[(x[2] >> (2*N)) & MASK] & M1) ^
         (Td4[(x[2] >> (1*N)) & MASK] & M2) ^
         (Td4[(x[2] >> (0*N)) & MASK] & M3);
  y[3] = (Td4[(x[3] >> (3*N)) & MASK] & M0) ^
         (Td4[(x[3] >> (2*N)) & MASK] & M1) ^
         (Td4[(x[3] >> (1*N)) & MASK] & M2) ^
         (Td4[(x[3] >> (0*N)) & MASK] & M3);
  
  memcpy(x, y, sizeof(state));
}

void MC(state x) {
  state y;
  SRSBInv(x);
  Round(x, y);
  memcpy(x, y, sizeof(state));
}

void MCInv(state x) {
  state y;
  SRSB(x);
  RoundInv(x, y);  
  memcpy(x, y, sizeof(state));
}


void encrypt_N(state x, state *k, int rnd) {
  for (int i=0; i<rnd; i++) {
    state t;
    AddKey(x,k[i]);
    Round(x, t);
    memcpy(x, t, sizeof(state));
  }

  AddKey(x,k[rnd]);
}

void encrypt(state x, state k[R+1]) {
  encrypt_N(x, k, R);
}

void decrypt(state x, state k[R+1]) {
  SRSB(x);
  for (int i=R; i>0; i--) {
    state t;
    RoundInv(x, t);
    AddKey(t,k[i]);
    memcpy(x, t, sizeof(state));
  }
  SRSBInv(x);
  AddKey(x,k[0]);
}


void print_state(state x) {
  for (int i=0; i<4; i++)
    printf (N==8? "%08x\n":  "%04x\n", x[i]);
  printf ("\n");
}

void print_quartet(state p1, state p2, state p3, state p4, state k[]) {
  printf ("Candidate Quartet:\n");
  
  state x1, x2, x3, x4;
  memcpy(x1, p1, sizeof(x1));
  memcpy(x2, p2, sizeof(x2));
  memcpy(x3, p3, sizeof(x3));
  memcpy(x4, p4, sizeof(x4));
  for (int i=0; i<=R; i++) {
    for (int j=0; j<4; j++)
      printf (N==8? "%08x | %08x [%08x] || %08x | %08x [%08x] || [%08x] [%08x]\n":
	      "%04x | %04x [%04x] || %04x | %04x [%04x] || [%04x] [%04x]\n",
	      x1[j], x2[j], x1[j]^x2[j], x3[j], x4[j], x3[j]^x4[j], x1[j]^x3[j], x2[j]^x4[j]);
    printf ("\n");

    state t;
    AddKey(x1,k[i]);
    Round(x1, t);
    memcpy(x1, t, sizeof(state));
    AddKey(x2,k[i]);
    Round(x2, t);
    memcpy(x2, t, sizeof(state));
    AddKey(x3,k[i]);
    Round(x3, t);
    memcpy(x3, t, sizeof(state));
    AddKey(x4,k[i]);
    Round(x4, t);
    memcpy(x4, t, sizeof(state));
  }
  printf ("\n");
}

void print_pair(state p1, state p2, state k[]) {
  printf ("Candidate Pair:\n");
  
  state x1, x2;
  memcpy(x1, p1, sizeof(x1));
  memcpy(x2, p2, sizeof(x2));
  for (int i=0; i<=R; i++) {
    for (int j=0; j<4; j++)
      printf ("%04x | %04x [%04x]\n",
	      x1[j], x2[j], x1[j]^x2[j]);
    printf ("\n");

    state t;
    AddKey(x1,k[i]);
    Round(x1, t);
    memcpy(x1, t, sizeof(state));
    AddKey(x2,k[i]);
    Round(x2, t);
    memcpy(x2, t, sizeof(state));
  }
  printf ("\n");
}

int weight(word x) {
  return
    !!(x & 0xf000) +
    !!(x & 0x0f00) +
    !!(x & 0x00f0) +
    !!(x & 0x000f);
}

word extract_diag0(state x) {
  return
    (x[0] & 0xf000) |
    (x[1] & 0x0f00) |
    (x[2] & 0x00f0) |
    (x[3] & 0x000f);
}

word extract_diag1(state x) {
  return
    (x[0] & 0x0f00) |
    (x[1] & 0x00f0) |
    (x[2] & 0x000f) |
    (x[3] & 0xf000);
}

word extract_diag2(state x) {
  return
    (x[0] & 0x00f0) |
    (x[1] & 0x000f) |
    (x[2] & 0xf000) |
    (x[3] & 0x0f00);
}

word extract_diag3(state x) {
  return
    (x[0] & 0x000f) |
    (x[1] & 0xf000) |
    (x[2] & 0x0f00) |
    (x[3] & 0x00f0);
}

word extract_antidiag0(const state x) {
  return
    (x[0] & 0xf000) |
    (x[1] & 0x000f) |
    (x[2] & 0x00f0) |
    (x[3] & 0x0f00);
}

word extract_antidiag1(const state x) {
  return
    (x[0] & 0x0f00) |
    (x[1] & 0xf000) |
    (x[2] & 0x000f) |
    (x[3] & 0x00f0);
}

word extract_antidiag2(const state x) {
  return
    (x[0] & 0x00f0) |
    (x[1] & 0x0f00) |
    (x[2] & 0xf000) |
    (x[3] & 0x000f);
}

word extract_antidiag3(const state x) {
  return
    (x[0] & 0x000f) |
    (x[1] & 0x00f0) |
    (x[2] & 0x0f00) |
    (x[3] & 0xf000);
}

typedef struct {
  word x[32<<N];
  unsigned n;
} candidates;

word* superbox_inv;  // Not full superbox

// Pre-compute DDT of a column
// Easier than S-Box by S-Box, but requires more memory
// p[m][delta] contains a list of candidates
candidates (*precompute_candidates())[4] {
  superbox_inv = malloc(sizeof(superbox_inv[0])<<(4*N));
  assert(superbox_inv);
  for (uint64_t i=0; i < 1ULL<<(4*N); i++) {
    state x = {
      i & 0xf000,
      i & 0x000f,
      i & 0x00f0,
      i & 0x0f00
    };
    state y;
    RoundInv(x, y);
    superbox_inv[i] = y[0];
  }
  
  candidates (*p)[4] = calloc(1ULL<<(4*N), sizeof(p[0]));
  assert(p);
  // Stupid precomputation with complexity 1<<8*N
#pragma omp parallel for
  for (uint64_t delta=1; delta < 1ULL<<(4*N); delta++) {
    // Output difference
    word x = 0;
    // Output value
    do {
      word a = superbox_inv[x];
      word b = superbox_inv[x^delta];
      if (((a^b) & 0x0fff) == 0)
	p[0][delta].x[p[0][delta].n++] = x;
      if (((a^b) & 0xf0ff) == 0)
	p[1][delta].x[p[1][delta].n++] = x;
      if (((a^b) & 0xff0f) == 0)
	p[2][delta].x[p[2][delta].n++] = x;
      if (((a^b) & 0xfff0) == 0)
	p[3][delta].x[p[3][delta].n++] = x;

      assert(p[0][delta].n < tabsize(p[0][delta].x));
      assert(p[1][delta].n < tabsize(p[1][delta].x));
      assert(p[2][delta].n < tabsize(p[2][delta].x));
      assert(p[3][delta].n < tabsize(p[3][delta].x));
    } while (++x);
  }

  return p;
}

typedef struct {
  state c;    // Ciphertext
  uint16_t i; // Plaintext index
} data_p;

int cmp_diag(const void *a, const void *b) {
  const data_p *A = a;
  const data_p *B = b;

  uint64_t aa =
    ((uint64_t)extract_antidiag0(A->c)<<48) |
    ((uint64_t)extract_antidiag1(A->c)<<32) |
    ((uint64_t)extract_antidiag2(A->c)<<16) |
    ((uint64_t)extract_antidiag3(A->c));

  uint64_t bb =
    ((uint64_t)extract_antidiag0(B->c)<<48) |
    ((uint64_t)extract_antidiag1(B->c)<<32) |
    ((uint64_t)extract_antidiag2(B->c)<<16) |
    ((uint64_t)extract_antidiag3(B->c));

  if (aa>bb)
    return 1;
  if (aa<bb)
    return -1;
  return 0;
}

int main() {
  srandom(time(NULL));
  state k[R+1];
  state kInv[R+1];
  for (int i=0; i<R+1; i++) {
    for (int j=0; j<4; j++) {
      k[i][j] = random();
      kInv[i][j] = k[i][j];
    }
    if (i)
      MCInv(kInv[i]);
  }

  printf ("Secret key: k0 = %04x, k6 = %04x\n\n",
	  extract_diag0(k[0]), extract_antidiag0(kInv[6]));

  /***********************************/
  /* Verify AES implementation       */
  /***********************************/
  
  /* state x = {0,0,0,0}; */
  /* print_state(x); */
  /* encrypt(x, k); */
  /* print_state(x); */
  /* decrypt(x, kInv); */
  /* print_state(x); */

  /* state y = {0xdeadbeef,0,0,1}; */
  /* print_state(y); */
  /* encrypt(y, k); */
  /* print_state(y); */
  /* decrypt(y, kInv); */
  /* print_state(y); */


  /***********************************/
  /* 6-round boomerang               */
  /***********************************/

  candidates (*cand)[4] = precompute_candidates();

  int cnt = 0, cnd = 0;

#pragma omp parallel
  {
    data_p *struc = malloc(sizeof(struc[0])<<16);
    assert(struc);
  
    struct { int n; uint16_t k[1<<12]; } *S_cand = malloc(sizeof(S_cand[0])*4);
    assert(S_cand);
  
    struct { int n; uint16_t k[1<<12]; } *S_cand2 = malloc(sizeof(S_cand2[0])*4);
    assert(S_cand2);
   
#pragma omp for
    for (int tmp=0; tmp<65536; tmp++) {
      int my_cnt = __atomic_fetch_add(&cnt,1,__ATOMIC_RELAXED);
      
      // Build strucutre, and encrypt it
      state x = {
	random() & 0x0fff,
	random() & 0xf0ff,
	random() & 0xff0f,
	random() & 0xfff0};
    
      for (int i=0; i<1<<16; i++) {
	// Structure active on a diagonal
	struc[i].i = i;
	struc[i].c[0] = x[0] ^ (i & 0xf000);
	struc[i].c[1] = x[1] ^ (i & 0x0f00);
	struc[i].c[2] = x[2] ^ (i & 0x00f0);
	struc[i].c[3] = x[3] ^ (i & 0x000f);
	encrypt(struc[i].c, k);
	MCInv(struc[i].c);
      }

      // Sort
      qsort(struc, 1<<16, sizeof(struc[0]), cmp_diag);

      // Check for usufull collisions
      // For simplicity, we consider antidiagonal 0 and 1, and position a=0
      for (int i=1; i<1<<16; i++) {
	if ( ((struc[i].c[0]^struc[i-1].c[0]) & 0xff00) == 0 &&
	     ((struc[i].c[1]^struc[i-1].c[1]) & 0xf00f) == 0 &&
	     ((struc[i].c[2]^struc[i-1].c[2]) & 0x00ff) == 0 &&
	     ((struc[i].c[3]^struc[i-1].c[3]) & 0x0ff0) == 0 &&
	     ((struc[i].i^struc[i-1].i) & 0xf000) == 0) {

	  int my_cnd = __atomic_fetch_add(&cnd,1,__ATOMIC_RELAXED);
#ifdef VERBOSE
	  printf ("Candidate pair found [pair #%i, structure #%i]\n", my_cnd, my_cnt);
#else
	  printf ("\rCandidate pair found [pair #%4i, structure #%5i]", my_cnd, my_cnt);
	  fflush(stdout);
#endif
	  
	  // Plaintext/ciphertext
	  state C0, C1, P0, P1;
	  memcpy(C0, struc[i].c, sizeof(state));
	  memcpy(C1, struc[i-1].c, sizeof(state));
	  memcpy(P0, struc[i].c, sizeof(state));
	  memcpy(P1, struc[i-1].c, sizeof(state));
	  MC(P0);
	  MC(P1);
	  decrypt(P0, kInv);
	  decrypt(P1, kInv);
          

          
#ifdef VERBOSE
	  // Detect right pairs
	  int right = 0;
	  int right_m;
	  {
	    state X0, X1, Y0, Y1, Z0, Z1, T0, T1;
	    memcpy(X0, P0, sizeof(state));
	    memcpy(X1, P1, sizeof(state));

	    AddKey(X0, k[0]);
	    AddKey(X1, k[0]);
	    Round(X0, Y0);
	    Round(X1, Y1);

	    AddKey(Y0, k[1]);
	    AddKey(Y1, k[1]);
	    Round(Y0, Z0);
	    Round(Y1, Z1);

	    AddKey(Z0, k[2]);
	    AddKey(Z1, k[2]);
	    Round(Z0, T0);
	    Round(Z1, T1);
	    AddKey(T0, T1);
	    
	    if ( ( weight(Y0[0]^Y1[0]) < 4 ) &&
	    	 ( extract_diag0(T0) == 0 ||
	    	   extract_diag1(T0) == 0 ||
	    	   extract_diag2(T0) == 0 ||
	    	   extract_diag3(T0) == 0 ) ) {

	      printf ("************************************************************\n"
		      "Right pair!! (%04x)\n", Y0[0]^Y1[0]);
	      
	      printf ("x = \n");
	      print_state(x);
	      printf ("\ni = %04x\np = \n", struc[i].i);
	      print_state(X0);
	      printf ("c = \n");
	      print_state(struc[i].c);
	      printf ("j = %04x\np = \n", struc[i-1].i);
	      print_state(X1);
	      printf ("c = \n");
	      print_state(struc[i-1].c);
	      printf("\n");

	      print_pair(P0, P1, k);
	      
	      right = 1;
	      if (extract_diag0(T0) == 0)
		right_m = 0;
	      if (extract_diag1(T0) == 0)
		right_m = 3;
	      if (extract_diag2(T0) == 0)
		right_m = 2;
	      if (extract_diag3(T0) == 0)
		right_m = 1;
	    }

	  }
#endif	  

	  // Key candidates ($S_\ell$)
	  // Do it naively because it doesn't matter
	  for (int l=0; l<4; l++) {
	    S_cand[l].n = 0;
	  }
	  for (int k=0; k < 1<<12; k++) {
	    state t, u, v;
	    t[0] = ((struc[i].i^k) & 0xf000);
	    t[1] = ((struc[i].i^k) & 0x0f00);
	    t[2] = ((struc[i].i^k) & 0x00f0);
	    t[3] = ((struc[i].i^k) & 0x000f);
	    Round(t, u);
	  
	    t[0] = ((struc[i-1].i^k) & 0xf000);
	    t[1] = ((struc[i-1].i^k) & 0x0f00);
	    t[2] = ((struc[i-1].i^k) & 0x00f0);
	    t[3] = ((struc[i-1].i^k) & 0x000f);
	    Round(t, v);

	    for (int l=0; l<4; l++) {
	      if (((u[0]^v[0]) & (0xf << (4*l))) == 0) {
		S_cand[l].k[S_cand[l].n++] = k;
	      }
	    }
	  }

	  // Candidates quartets
	  for (int qi=1; qi<1<<16; qi++) {
	    state P2, P3, C2, C3;

	    // Structure active on an anti-diagonal
	    state delta = {qi & 0xf000, qi & 0x000f, qi & 0x00f0, qi & 0x0f00};

            memcpy(C2, C0, sizeof(state));
            memcpy(C3, C1, sizeof(state));
	    AddKey(C2, delta);
	    AddKey(C3, delta);

            memcpy(P2, C2, sizeof(state));
            memcpy(P3, C3, sizeof(state));

	    MC(P2);
	    decrypt(P2, kInv);
	    MC(P3);
	    decrypt(P3, kInv);
	    
	    // Quartet is (P0, P1, P2, P3)

	    // Filter plaintext
	    if ((P2[0]&0xf000) == (P3[0]&0xf000)) {
#ifdef VERBOSE
              int right2 = 0;
	      if (right) {
		state Y, Z;
		memcpy(Y, P0, sizeof(state));
		memcpy(Z, P2, sizeof(state));
		
		encrypt_N(Y, k, 4);
		encrypt_N(Z, k, 4);

		if (((extract_diag0(Y)^extract_diag0(Z)) & ~(0xf000>>(4*right_m))) == 0) {
		  printf ("************************************************************\n"
			  "Right quartet!! (%04x) [qi:%04x]\n", P0[0]^P1[0], qi);

		  printf ("p = \n");
		  print_state(P2);
		  printf ("p = \n");
		  print_state(P3);
		  printf ("\n");

		  
		  print_quartet(P0, P1, P2, P3, k);

		  right2 = 1;
		}
	      }
#endif	      

	      
	      // Filter 2^8 candidates k0[5,10,15] to 2^4
	      for (int l=0; l<4; l++) {
		S_cand2[l].n = 0;
		for (int k=0; k < S_cand[l].n; k++) {
		  state t, u, v;
		  t[0] = ((P2[0]^S_cand[l].k[k]) & 0xf000);
		  t[1] = ((P2[1]^S_cand[l].k[k]) & 0x0f00);
		  t[2] = ((P2[2]^S_cand[l].k[k]) & 0x00f0);
		  t[3] = ((P2[3]^S_cand[l].k[k]) & 0x000f);
		  Round(t, u);
	  
		  t[0] = ((P3[0]^S_cand[l].k[k]) & 0xf000);
		  t[1] = ((P3[1]^S_cand[l].k[k]) & 0x0f00);
		  t[2] = ((P3[2]^S_cand[l].k[k]) & 0x00f0);
		  t[3] = ((P3[3]^S_cand[l].k[k]) & 0x000f);
		  Round(t, v);

		  if (((u[0]^v[0]) & (0xf << (4*l))) == 0) {
		    S_cand2[l].k[S_cand2[l].n++] = S_cand[l].k[k];
		  }
		}
	      }


	      for (int m=0; m<4; m++) {
		// Extract key candidates on ciphertext side
		word delta = qi;
		for (unsigned ki=0; ki<cand[m][delta].n; ki++) {
		  word k6 = cand[m][delta].x[ki] ^ extract_antidiag0(struc[i].c);

#ifdef VERBOSE
                  int right3 = 0;
                  if (right2) {
                    if (k6 == extract_antidiag0(kInv[6])) {
                      printf ("************************************************************\n"
                              "Right k6 guess!!  (%04x) [%i/%i]\n", k6, m, right_m);
                      right3 = 1;
                    }
                  }
#endif

                  // Build extra quartets
		  // NOTE: we use more quartets than required to
		  // remove false positives (the paper suggest
		  // recovering over key bytes instead)
		  struct { state p0; state p1; } xtraQ[12]; // plaintexts
                  for (unsigned i=0; i<tabsize(xtraQ); i++) {
                    state U, V;
                    state K6 = {k6 & 0xf000, k6 & 0x000f, k6 & 0x00f0, k6 & 0x0f00};
                    
                    memcpy (U, C0, sizeof(state));
                    AddKey (U, K6);
                    RoundInv (U, V); // SRInv, SBInv, MCInv
                    V[0] ^= (i+1)<<(12-4*m);
                    MC (V);
                    SRSB (V);
                    AddKey (V, K6);

                    memcpy(&xtraQ[i].p0, V, sizeof(state));
                    memcpy(&xtraQ[i].p1, V, sizeof(state));
                    AddKey(xtraQ[i].p1, C0);
                    AddKey(xtraQ[i].p1, C1);

                    MC(xtraQ[i].p0);
                    decrypt(xtraQ[i].p0, kInv);
                    MC(xtraQ[i].p1);
                    decrypt(xtraQ[i].p1, kInv);
                    
#ifdef VERBOSE
                    if (right3) {
                      printf ("Extra quartet:\n");
                      print_quartet(P0, P1, xtraQ[i].p0, xtraQ[i].p1, k);
                    }
#endif
                  }

		  // Check key candidates
		  for (int l=0; l<4; l++) {
		    for (int kk=0; kk < S_cand2[l].n; kk++) {
		      // NOTE: we exhaustively try all k0[0],
		      // instead of using linear algebra and the DDT
		      // to directly recover the correct value
		      for (int ki=0; ki<16; ki++) {

			word k0 = S_cand2[l].k[kk] + (ki<<12);
			int good = 1;

			for (int qq=0; qq<tabsize(xtraQ); qq++) {
			  state t, u, v;
			  t[0] = xtraQ[qq].p0[0] ^ (k0 & 0xf000);
			  t[1] = xtraQ[qq].p0[1] ^ (k0 & 0x0f00);
			  t[2] = xtraQ[qq].p0[2] ^ (k0 & 0x00f0);
			  t[3] = xtraQ[qq].p0[3] ^ (k0 & 0x000f);
			  Round(t, u);
		      
			  t[0] = xtraQ[qq].p1[0] ^ (k0 & 0xf000);
			  t[1] = xtraQ[qq].p1[1] ^ (k0 & 0x0f00);
			  t[2] = xtraQ[qq].p1[2] ^ (k0 & 0x00f0);
			  t[3] = xtraQ[qq].p1[3] ^ (k0 & 0x000f);
			  Round(t, v);
		      

			  if (((u[0]^v[0]) & (0xf << (4*l))) != 0) {
			    good = 0;
			    break;
			  }
			}

			if (good) {
			  printf ("\rKey candidate found! [candidate pair #%i, structure #%i]", my_cnd, my_cnt);
#ifdef VERBOSE
			  printf(" [right:%i] [right2:%i] [right3:%i]", right, right2, right3);
#endif
			  printf ("\nk0 = %04x, k6 = %04x\n\n", k0, k6);
			}
		      }
		    }
		  }
		}
	      }
	    }
	  }
	}
      }
    }
  }
  printf ("\n");
}
