// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef EXTENDED_EUCLIDEAN__B_EQ_0__B_EQ_A
#define EXTENDED_EUCLIDEAN__B_EQ_0__B_EQ_A  1

#ifndef NDEBUG
#  include "assert_helper_gcd.h"
#endif
#include <assert.h>
#include <limits>

#if defined(assert_invariant) || defined(assert_precondition)
#  error "assert_invariant and/or assert_precondition were already defined"
#endif
// assert aliases will help self-document the code
#define assert_invariant     assert
#define assert_precondition  assert


template <typename T>
void extended_euclidean__b_eq_0__b_eq_a(T a, T b, T* pGcd, T* pX, T* pY)
{
	    static_assert(std::numeric_limits<T>::is_integer, "");
	    static_assert(std::numeric_limits<T>::is_signed, "");
/*01*/     assert_precondition(b == a);
/*02*/     assert_precondition(b == 0);
/*03*/  T x0 = 1;
/*04*/  T y0 = 0;
/*05*/  T a0 = a;
/*06*/  T x1 = 0;
/*07*/  T y1 = 1;
/*08*/  T a1 = b;

/*09*/     assert(a == 0);                     // By [01, 02]
/*10*/     assert(gcd(a,b) == 0);
           // Proof: By [02, 09] b == 0 and a == 0, thus gcd(a,b) == gcd(0,0).
           // Since we will use the definition of the gcd under which
           // gcd(0,0) == 0,  gcd(a,b) == gcd(0,0) == 0.
           // Note on the gcd definition:  One way d = gcd(a,b) can be defined
           // is that d is the integer that divides both a and b, such that for
           // every integer c that divides both a and b, d >= c.  Under this
           // definition, gcd(0,0) is undefined.  Another way d = gcd(a,b) can be
           // defined is that d is the non-negative integer that divides both a
           // and b, such that for every integer c that divides both a and b,
           // c divides d.  Under this definition, gcd(0,0) == 0.
           // See https://math.stackexchange.com/a/495457
           // If a caller is using the first definition, calling with a == 0 and
           // b == 0 would be an implicit precondition violation since it would
           // be a request for the undefined gcd(0,0).  We will assume that the
           // caller will not violate any implicit preconditions, and therefore
           // that the caller expects the second definition if calling with
           // a == 0 and b == 0.
/*11*/     assert(a1 == 0);                    // By [08, 02]

/*12*/  // By [11], this loop will never be taken
        while (a1 != 0) {
           assert(false);  // we will never reach this assert, by [12]
           T q = a0/a1;
           T a2 = a0 - q*a1;
           T x2 = x0 - q*x1;
           T y2 = y0 - q*y1;
 
           x0 = x1;
           y0 = y1;
           a0 = a1;
           x1 = x2;
           y1 = y2;
           a1 = a2;
        }

           // Note: Because by [10] gcd(a,b) == 0,  we do NOT have
           // (abs(x1) == b/gcd(a,b))  or  (abs(y1) == a/gcd(a,b))  or
           // (abs(x0) <= (b/gcd(a,b))/2)  or  (abs(y0) <= (a/gcd(a,b))/2).
/*13*/     assert(x1 == 0);                    // By [12, 06]
/*14*/     assert(y1 == 1);                    // By [12, 07]
/*15*/     assert(x0 == 1);                    // By [12, 03]
/*16*/     assert(y0 == 0);                    // By [12, 04]
/*17*/     assert(a0 == gcd(a,b));
           // Proof: By [12, 05, 09] a0 == a == 0.  By [10] gcd(a,b) == 0.
           // Thus a0 == 0 == gcd(a,b).
/*18*/     assert(a*x0 + b*y0 == gcd(a,b));
           // Proof: By [15, 16, 09] x0 == 1 and y0 == 0 and a == 0.
           // By [10] gcd(a,b) == 0.
           // Thus, a*x0 + b*y0 == a*1 + b*0 == a == 0 == gcd(a,b).
           // Note: Since a*x0 + b*y0 == gcd(a,b), we know x0 and y0 are the
           // Bezout coefficients.
        *pX = x0;
        *pY = y0;
        *pGcd = a0;
}

#undef assert_invariant
#undef assert_precondition

#endif
