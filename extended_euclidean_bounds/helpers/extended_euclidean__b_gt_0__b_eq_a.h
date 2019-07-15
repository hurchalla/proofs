// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef EXTENDED_EUCLIDEAN__B_GT_0__B_EQ_A
#define EXTENDED_EUCLIDEAN__B_GT_0__B_EQ_A  1

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
void extended_euclidean__b_gt_0__b_eq_a(T a, T b, T* pGcd, T* pX, T* pY)
{
        static_assert(std::numeric_limits<T>::is_integer, "");
        static_assert(std::numeric_limits<T>::is_signed, "");
/*01*/     assert_precondition(b == a);
/*02*/     assert_precondition(b > 0);
/*03*/  T x0 = 1;
/*04*/  T y0 = 0;
/*05*/  T a0 = a;
/*06*/  T x1 = 0;
/*07*/  T y1 = 1;
/*08*/  T a1 = b;

/*09*/     assert(a > 0);                      // By [01, 02]
/*10*/     assert(gcd(a,b) == a);
           // Proof: By [09, 01] a > 0 and b == a, so gcd(a,b) != gcd(0,0), and
           // gcd(a,b) == gcd(a,a) == a.
/*H0*/     assert(gcd(a,b) >= 1);              // By [10, 09] gcd(a,b) == a >= 1
/*11*/     assert(a1 == a);                    // By [08, 01]


        // This loop would be taken at least once, since by [08,02] a1 > 0.
        // So we will peel out the first iteration from the loop, and place it
        // prior to the start of the loop.
//      while (a1 != 0) {
//         T q = a0/a1;
//         T a2 = a0 - q*a1;
//         T x2 = x0 - q*x1;
//         T y2 = y0 - q*y1;
//
//         x0 = x1;
//         y0 = y1;
//         a0 = a1;
//         x1 = x2;
//         y1 = y2;
//         a1 = a2;
//      }

        // The peeled-out first iteration:
        {
/*12*/     T q = a0/a1;
/*13*/        assert(q == 1);
              // Proof: By [05, 08, 01, 02] a0 == a and a1 == b and  a == b > 0.
              // By [12] q == a0/a1 == a/b == b/b.  Since b > 0, q == b/b == 1.
/*14*/        assert(1 <= q && q <= a0);
              // Proof: By [13] q == 1, so 1 <= q.  By [05, 09] a0 == a > 0,
              // so a0 >= 1.  Since q == 1  and  1 <= a0,  q <= a0.
/*15*/     T a2 = a0 - q*a1;
/*16*/        assert(q*a1 == a);               // By [13, 11]
/*17*/        assert(0 < (q*a1) && (q*a1) <= a0);
              // Proof: By [16, 09] (q*a1) == a > 0, so 0 < (q*a1).  By [05],
              // a0 == a, so  (q*a1) == a == a0, and thus (q*a1) <= a0.
/*18*/        assert(a2 == 0);
              // Proof: By [05] a0 == a, and by [16] q*a1 == a.  By [15]
              // a2 == a0 - q*a1,  so  a2 == a - a == 0.
/*19*/        assert(0 <= a2 && a2 < a1);
              // Proof: By [18] a2 == 0, so 0 <= a2.  By [08, 02] a1 == b > 0,
              // so 0 < a1, and thus since a2 == 0,  a2 == 0 < a1.
/*H1*/        if (a2 != 0) assert(q <= a0/2);
              // Proof: By [18] a2 == 0, so this assert is skipped.
/*20*/     T x2 = x0 - q*x1;
/*21*/        assert(x2 == 1);
              // Proof: By [03, 13, 06]  x0 == 1  and  q == 1  and  x1 == 0.
              // Thus by [20] x2 == x0 - q*x1 == 1 - 1*0 == 1.
/*22*/        assert(abs(q*x1) <= abs(x2));    // By [06, 21]
/*23*/        assert(abs(x1) <= abs(x2));      // By [06, 21]
/*24*/     T y2 = y0 - q*y1;
/*25*/        assert(y2 == -1);
              // Proof: By [04, 13, 07]  y0 == 0 and  q == 1  and  y1 == 1.
              // Thus by [24] y2 == y0 - q*y1 == 0 - 1*1 == -1.
/*26*/        assert(abs(q*y1) <= abs(y2));    // By [13, 07, 25]
/*27*/        assert(abs(y1) <= abs(y2));      // By [07, 25]

/*28*/     x0 = x1;
/*29*/     y0 = y1;
/*30*/     a0 = a1;
/*31*/        assert(x0 == 0);                 // By [28, 06] x0 == x1 == 0.
/*32*/        assert(y0 == 1);                 // By [29, 07] y0 == y1 == 1.
/*33*/        assert(a0 == a);                 // By [30, 11] a0 == a1 == a.
/*34*/     x1 = x2;
/*35*/     y1 = y2;
/*36*/     a1 = a2;
/*37*/        assert(x1 == 1);                 // By [34, 21] x1 == x2 == 1.
/*38*/        assert(y1 == -1);                // By [35, 25] y1 == y2 == -1.
/*39*/        assert(a1 == 0);                 // By [36, 18] a1 == a2 == 0.
        }
/*40*/  // By [39], no further iterations of the loop will be taken
        while (a1 != 0) {
           assert(false);  // we will never reach this assert, by [40]
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

/*41*/     assert(abs(x1) == b/gcd(a,b));
           // Proof: By [10] gcd(a,b) == a, and by [01, 09] b == a > 0.  By
           // [40,37] x1 == 1.  Thus b/gcd(a,b) == a/a == 1 == abs(1) == abs(x1)
/*42*/     assert(abs(y1) == a/gcd(a,b));
           // Proof: By [10] gcd(a,b) == a, and by [09] a > 0.  By [40, 38]
           //  y1 == -1.  Thus a/gcd(a,b) == a/a == 1 == abs(-1) == abs(y1).
/*43*/     assert(abs(x0) <= (b/gcd(a,b))/2);
           // Proof: By [10] gcd(a,b) == a, and by [01, 09] b == a > 0, and
           // by [40, 31] x0 == 0.  Thus,
           // (b/gcd(a,b))/2 == (a/a)/2 == 1/2 == 0 == abs(0) == abs(x0),
           // which satisfies  abs(x0) <= (b/gcd(a,b))/2.
/*44*/     assert(y0 == 1);
           // Proof: By [40, 32] y0 == 1.
           // Note: we do NOT have (abs(y0) <= (a/gcd(a,b))/2), since this would
           // simplify to 1 <= 0, which is obviously false.
/*45*/     assert(a0 == gcd(a,b));
           // Proof: By [10, 40, 33] gcd(a,b) == a == a0.
/*46*/     assert(a*x0 + b*y0 == gcd(a,b));
           // Proof: By [40, 31, 32] x0 == 0 and y0 == 1.
           // By [01, 10], b == a == gcd(a,b).
           // Thus, a*x0 + b*y0 == a*0 + b*1 == b == a == gcd(a,b).
           // Note: Since a*x0 + b*y0 == gcd(a,b), we know x0 and y0 are the
           // Bezout coefficients.
        *pX = x0;
        *pY = y0;
        *pGcd = a0;
}

#undef assert_invariant
#undef assert_precondition

#endif
