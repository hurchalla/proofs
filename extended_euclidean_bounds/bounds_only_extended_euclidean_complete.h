// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef BOUNDS_ONLY_EXTENDED_EUCLIDEAN_COMPLETE
#define BOUNDS_ONLY_EXTENDED_EUCLIDEAN_COMPLETE  1

#ifndef NDEBUG
#  include "helpers/assert_helper_gcd.h"
#endif
#include <assert.h>
#include <limits>

#if defined(assert_precondition)
#  error "assert_precondition was already defined"
#endif
// assert aliases will help self-document the code
#define assert_precondition  assert


template <typename T>
void bounds_only_extended_euclidean_complete(T a, T b, T* pGcd, T* pX, T* pY)
{
   static_assert(std::numeric_limits<T>::is_integer, "");
   static_assert(std::numeric_limits<T>::is_signed, "");
   assert_precondition(b >= 0 && a >= 0);
   T x0 = 1, y0 = 0, a0 = a;
   T x1 = 0, y1 = 1, a1 = b;

   while (a1 != 0) {
      T q = a0/a1;
         assert(0 <= q && q <= a0);
      T a2 = a0 - q*a1;
         assert(0 <= (q*a1) && (q*a1) <= a0);
         assert(0 <= a2 && a2 < a1);
         if (a2 != 0) assert(q <= a0/2);
      T x2 = x0 - q*x1;
         assert(abs(q*x1) <= abs(x2));
         assert(abs(x1) <= abs(x2));
      T y2 = y0 - q*y1;
         assert(abs(q*y1) <= abs(y2));
         assert(y1 == 1 || abs(y1) <= abs(y2));
      x0=x1; y0=y1; a0=a1;
      x1=x2; y1=y2; a1=a2;
   }
      if (a == 0 && b == 0) {
         assert(x1 == 0);
         assert(y1 == 1);
         assert(x0 == 1);
         assert(y0 == 0);
      } else {
         assert(gcd(a,b) >= 1);
         assert(abs(x1) == b/gcd(a,b));
         assert(abs(y1) == a/gcd(a,b));
         assert(x0 == 1 || abs(x0) <= (b/gcd(a,b))/2);
         assert(y0 == 1 || abs(y0) <= (a/gcd(a,b))/2);
      }
   *pX = x0;
   *pY = y0;
   *pGcd = a0;
}

#undef assert_precondition

#endif
