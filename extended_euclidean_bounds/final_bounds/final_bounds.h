// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

// This file uses as its starting point the assertions established by
// essential_asserts_improved.h, and proves the final simplifed bounds.
// This proof differs from all the preceding proofs, in that it begins with the
// established assertions at the end of the algorithm and then works backward
// from the end to prove new assertions.  This means it works backward from the
// last loop iteration, upward through the loop's code.  Once it reaches the
// start of the loop it works backward through the previous loop iteration (if
// there is a previous iteration).

#ifndef FINAL_BOUNDS
#define FINAL_BOUNDS  1

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


// This proof should be read starting at the end of the function, then moving
// upward.  Don't start at the top of the function.

template <typename T>
void final_bounds(T a, T b, T* pGcd, T* pX, T* pY)
{
   const auto max = static_cast<const T&(*)(const T&, const T&)>(std::max);
   static_assert(std::numeric_limits<T>::is_integer, "");
   static_assert(std::numeric_limits<T>::is_signed, "");
   assert_precondition(a >= 0 && b >= 0);
   T x0 = 1, y0 = 0, a0 = a;
   T x1 = 0, y1 = 1, a1 = b;

    while (a1 != 0) {
/*31*/    assert(abs(x1) <= b);
          // Proof: By [21, 17] abs(x1) <= abs(x2) <= b
/*30*/    assert(abs(y1) <= max(1,a));
          // Proof: By [16] abs(y2) <= max(1,a).
          // By [20] abs(y1) <= max(1,abs(y2)), so
          // abs(y1) <= max(1, max(1,a)) == max(1,a).
/*29*/    assert(abs(x1) <= max(1,b/2));               // By [23, 25]
/*28*/    assert(abs(y1) <= max(1,a/2));               // By [22, 24]

       T q = a0/a1;
          assert_established(0 <= q && q <= max(a,b));
       T a2 = a0 - q*a1;
          assert_established(0 <= (q*a1) && (q*a1) <= max(a,b));
          assert_established(0 <= a2 && a2 < max(a,b));
          if (a2 != 0) assert_established(q <= max(a,b)/2);
       T x2 = x0 - q*x1;
          if (a2 != 0) assert(abs(q*x1) <= max(1,b/2));
          // Proof: By [27, 15] abs(q*x1) <= abs(x2) <= max(1,b/2)
          assert(abs(q*x1) <= b);
          // Proof: By [27, 17] abs(q*x1) <= abs(x2) <= b
/*27*/    assert_established(abs(q*x1) <= abs(x2));
       T y2 = y0 - q*y1;
          if (a2 != 0) assert(abs(q*y1) <= max(1,a/2));
          // Proof: By [26, 14] abs(q*y1) <= abs(y2) <= max(1,a/2).
          assert(abs(q*y1) <= max(1,a));
          // Proof: By [26, 16] abs(q*y1) <= abs(y2) <= max(1,a).
/*26*/    assert_established(abs(q*y1) <= abs(y2));

          if (a2 == 0) {
/*25*/       assert(abs(x1) <= max(1,b/2));            // By [11, 08, 19]
/*24*/       assert(abs(y1) <= max(1,a/2));            // By [11, 07, 18]
          }
          else {  // a2 != 0
/*23*/       assert(abs(x1) <= max(1,b/2));
             // Proof: By [21, 15] abs(x1) <= abs(x2) <= max(1,b/2).
/*22*/       assert(abs(y1) <= max(1,a/2));
             // Proof: By [14], abs(y2) <= max(1,a/2).
             // By [20] abs(y1) <= max(1,abs(y2)).  Therefore,
             // abs(y1) <= max(1, max(1,a/2)) == max(1,a/2).
          }
/*21*/    assert_established(abs(x1) <= abs(x2));
/*20*/    assert_established(abs(y1) <= max(1,abs(y2)));

/*19*/ x0=x1;
/*18*/ y0=y1;
       a0=a1;
/*17*/    assert(abs(x2) <= b);                        // By [10, 13]
/*16*/    assert(abs(y2) <= max(1,a));                 // By [09, 12]
          if (a2 != 0) {  // if there is a loop iteration after this one
/*15*/       assert(abs(x2) <= max(1,b/2));            // By [11, 06, 13]
/*14*/       assert(abs(y2) <= max(1,a/2));            // By [11, 05, 12]
          }
/*13*/ x1=x2;
/*12*/ y1=y2;
/*11*/ a1=a2;
/*10*/    assert(abs(x1) <= b);                        // By [04, 31]
/*09*/    assert(abs(y1) <= max(1,a));                 // By [03, 30]
          if (a1 == 0) {  // if this is the last loop iteration
/*08*/       assert(abs(x0) <= max(1,b/2));            // By [02]
/*07*/       assert(abs(y0) <= max(1,a/2));            // By [01]
          }
          if (a1 != 0) {  // if there is a loop iteration after this one
/*06*/       assert(abs(x1) <= max(1,b/2));            // By [29]
/*05*/       assert(abs(y1) <= max(1,a/2));            // By [28]
          }
    }

/*04*/ assert_established(abs(x1) <= b);
/*03*/ assert_established(abs(y1) <= max(1,a));
/*02*/ assert_established(abs(x0) <= max(1,b/2));
/*01*/ assert_established(abs(y0) <= max(1,a/2));

       assert_established(a0 == gcd(a,b));
       assert_established(a*x0 + b*y0 == gcd(a,b));
    *pX = x0;
    *pY = y0;
    *pGcd = a0;
}

#undef assert_precondition
#undef assert_established

#endif
