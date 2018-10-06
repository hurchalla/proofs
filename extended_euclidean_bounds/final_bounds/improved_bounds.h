// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

// This file uses as its starting point the assertions established by
// essential_asserts_combined.h.  Some of the bounds will be improved by stating
// them in terms of inputs a and b.

#ifndef IMPROVED_BOUNDS
#define IMPROVED_BOUNDS  1

#ifndef NDEBUG
#  include "helpers/assert_helper_gcd.h"
#endif
#include <assert.h>
#include <limits>
#include <algorithm>

#if defined(assert_precondition) || defined(assert_established)
#  error "assert_precondition and/or assert_established was already defined"
#endif
// assert aliases will help self-document the code
#define assert_precondition  assert
#define assert_established  assert


template <typename T>
void improved_bounds(T a, T b, T* pGcd, T* pX, T* pY)
{
	   const auto max = static_cast<const T&(*)(const T&, const T&)>(std::max);
       static_assert(std::numeric_limits<T>::is_integer, "");
       static_assert(std::numeric_limits<T>::is_signed, "");
/*01*/ assert_precondition(a >= 0 && b >= 0);
       T x0 = 1, y0 = 0;
/*02*/ T a0 = a;
       T x1 = 0, y1 = 1;
/*03*/ T a1 = b;

/*04*/ assert(a0 <= max(a,b));                      // By [02]
/*05*/ assert(a1 <= max(a,b));                      // By [03]

       while (a1 != 0) {
/*06*/    assert(a0 <= max(a,b));                   // By [04, 15]
/*07*/    assert(a1 <= max(a,b));                   // By [05, 17]
          T q = a0/a1;
/*08*/       assert_established(0 <= q && q <= a0);
             assert(0 <= q && q <= max(a,b));
             // Proof: By [08] 0 <= q <= a0.  By [06] a0 <= max(a,b).
             // Therefore 0 <= q <= a0 <= max(a,b).
          T a2 = a0 - q*a1;
/*09*/       assert_established(0 <= (q*a1) && (q*a1) <= a0);
             assert(0 <= (q*a1) && (q*a1) <= max(a,b));
             // Proof: By [09] 0 <= (q*a1) <= a0.  By [06] a0 <= max(a,b).
             // Therefore 0 <= (q*a1) <= a0 <= max(a,b).
/*10*/       assert_established(0 <= a2 && a2 < a1);
/*11*/       assert(0 <= a2 && a2 < max(a,b));
             // Proof: By [10] 0 <= a2 < a1.  By [07] a1 <= max(a,b).
             // Therefore 0 <= a2 < a1 <= max(a,b).
/*12*/       if (a2 != 0) assert_established(q <= a0/2);
             if (a2 != 0) assert(q <= max(a,b)/2);
             // Proof: By [12] if (a2!=0) then q <= a0/2.
             // By [06] a0 <= max(a,b).
             // Therefore, if (a2!=0) then q <= a0/2 <= max(a,b)/2.
          T x2 = x0 - q*x1;
             assert_established(abs(q*x1) <= abs(x2));
             assert_established(abs(x1) <= abs(x2));
          T y2 = y0 - q*y1;
             assert_established(abs(q*y1) <= abs(y2));
/*13*/       assert_established(y1 == 1 || abs(y1) <= abs(y2));
             assert(abs(y1) <= max(1,abs(y2)));
             // Proof: By [13], y1 == 1 || abs(y1) <= abs(y2).
             // Assume y1 == 1.  Then abs(y1) == abs(1) == 1.  Since
             //   1 <= max(1,abs(y2)) for any value of abs(y2), we would have
             //   abs(y1) == 1 <= max(1,abs(y2)).
             // Assume instead abs(y1) <= abs(y2).
             //   Since abs(y2) <= max(1,abs(y2)), we would have
             //   abs(y1) <= abs(y2) <= max(1,abs(y2)).
             // For both cases,  abs(y1) <= max(1,abs(y2)).

          x0=x1; y0=y1;
/*14*/    a0=a1;
/*15*/    assert(a0 <= max(a,b));
          // Proof: By [14, 07] a0 == a1 <= max(a,b)
          x1=x2; y1=y2;
/*16*/    a1=a2;
/*17*/    assert(a1 < max(a,b));
          // Proof: By [16, 11] a1 == a2 < max(a,b)
       }

          if (a == 0 && b == 0) {
/*18*/       assert_established(x1 == 0);
/*19*/       assert(abs(x1) <= b);
             // Proof: By [18] x1 == 0, so abs(x1) == 0.  By [01] 0 <= b,
             // so abs(x1) == 0 <= b.
/*20*/       assert_established(y1 == 1);
/*21*/       assert(abs(y1) <= max(1,a));
             // Proof: By [20] y1 == 1, so abs(y1) == 1.  Since 1 <= max(1,a)
             // for any value of a, we have  abs(y1) == 1 <= max(1,a).
/*22*/       assert_established(x0 == 1);
/*23*/       assert(abs(x0) <= max(1,b/2));
             // Proof: By [22] x0 == 1, so abs(x0) == 1.  Since 1 <= max(1,b/2)
             // for any value of b/2, we have  abs(x0) == 1 <= max(1,b/2).
/*24*/       assert_established(y0 == 0);
/*25*/       assert(abs(y0) <= max(1,a/2));
             // Proof: By [24] y0 == 0, so abs(y0) == 0.  Since 1 <= max(1,a/2)
             // for any value of a/2,  abs(y0) == 0 <= 1 <= max(1,a/2).
          } else {
/*26*/       assert_established(gcd(a,b) >= 1);
/*27*/       assert_established(abs(x1) == b/gcd(a,b));
/*28*/       assert(abs(x1) <= b);
             // Proof: By [26, 01] gcd(a,b) >= 1 and b >= 0. So b/gcd(a,b) <= b.
             // By [27] abs(x1) == b/gcd(a,b) <= b.
/*29*/       assert_established(abs(y1) == a/gcd(a,b));
/*30*/       assert(abs(y1) <= max(1,a));
             // Proof: By [26, 01] gcd(a,b) >= 1 and a >= 0. So a/gcd(a,b) <= a.
             // By [29] abs(y1) == a/gcd(a,b) <= a.  Since a <= max(1,a),
             // abs(y1) <= a <= max(1,a).
/*31*/       assert_established(x0 == 1 || abs(x0) <= (b/gcd(a,b))/2);
/*32*/       assert(abs(x0) <= max(1,b/2));
             // Proof: By [31], x0 == 1 || abs(x0) <= (b/gcd(a,b))/2.
             // Assume x0 == 1.  Then abs(x0) == abs(1) == 1.  Since 
             //   1 <= max(1,b/2) for any value of b/2, we know
             //   abs(x0) == 1 <= max(1,b/2).
             // Assume instead abs(x0) <= (b/gcd(a,b))/2.
             //   By [26,01] gcd(a,b) >= 1 and b >= 0,  so b/gcd(a,b) <= b, and
             //   thus (b/gcd(a,b))/2 <= b/2.  And since b/2 <= max(1,b/2), we
             //   would have  abs(x0) <= (b/gcd(a,b))/2 <= b/2 <= max(1,b/2).
             // For both cases,  abs(x0) <= max(1,b/2).
/*33*/       assert_established(y0 == 1 || abs(y0) <= (a/gcd(a,b))/2);
/*34*/       assert(abs(y0) <= max(1,a/2));
             // Proof: By [33], y0 == 1 || abs(y0) <= (a/gcd(a,b))/2.
             // Assume y0 == 1.  Then abs(y0) == abs(1) == 1.  Since
             //   1 <= max(1,a/2) for any value of a/2, we know
             //   abs(y0) == 1 <= max(1,a/2).
             // Assume instead abs(y0) <= (a/gcd(a,b))/2.
             //   By [26,01] gcd(a,b) >= 1 and a >= 0,  so a/gcd(a,b) <= a, and
             //   thus (a/gcd(a,b))/2 <= a/2.  And since a/2 <= max(1,a/2), we
             //   would have  abs(y0) <= (a/gcd(a,b))/2 <= a/2 <= max(1,a/2).
             // For both cases,  abs(y0) <= max(1,a/2).
          }
          assert(abs(x1) <= b);                     // By [19, 28]
          assert(abs(y1) <= max(1,a));              // By [21, 30]
          assert(abs(x0) <= max(1,b/2));            // By [23, 32]
          assert(abs(y0) <= max(1,a/2));            // By [25, 34]

          assert_established(a0 == gcd(a,b));
          assert_established(a*x0 + b*y0 == gcd(a,b));
       *pX = x0;
       *pY = y0;
       *pGcd = a0;
}

#undef assert_precondition
#undef assert_established

#endif
