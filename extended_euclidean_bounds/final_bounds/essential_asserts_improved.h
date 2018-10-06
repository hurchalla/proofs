// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

// This file is a trimmed copy of improved_bounds.h.
// It contains only the essential assertion results, and omits the proofs.

#ifndef ESSENTIAL_ASSERTS_IMPROVED
#define ESSENTIAL_ASSERTS_IMPROVED  1

#ifndef NDEBUG
#  include "helpers/assert_helper_gcd.h"
#endif
#include <assert.h>
#include <limits>
#include <algorithm>


template <typename T>
void essential_asserts_improved(T a, T b, T* pGcd, T* pX, T* pY)
{
   const auto max = static_cast<const T&(*)(const T&, const T&)>(std::max);
   static_assert(std::numeric_limits<T>::is_integer, "");
   static_assert(std::numeric_limits<T>::is_signed, "");
   assert(a >= 0 && b >= 0);    // precondition
   T x0 = 1, y0 = 0, a0 = a;
   T x1 = 0, y1 = 1, a1 = b;

   while (a1 != 0) {
      T q = a0/a1;
         assert(0 <= q && q <= max(a,b));
      T a2 = a0 - q*a1;
         assert(0 <= (q*a1) && (q*a1) <= max(a,b));
         assert(0 <= a2 && a2 < max(a,b));
         if (a2 != 0) assert(q <= max(a,b)/2);
      T x2 = x0 - q*x1;
         assert(abs(q*x1) <= abs(x2));
         assert(abs(x1) <= abs(x2));
      T y2 = y0 - q*y1;
         assert(abs(q*y1) <= abs(y2));
         assert(abs(y1) <= max(1,abs(y2)));

      x0=x1; y0=y1; a0=a1;
      x1=x2; y1=y2; a1=a2;
   }
      assert(abs(x1) <= b);
      assert(abs(y1) <= max(1,a));
      assert(abs(x0) <= max(1,b/2));
      assert(abs(y0) <= max(1,a/2));
      assert(a0 == gcd(a,b));
      assert(a*x0 + b*y0 == gcd(a,b));
   *pX = x0;
   *pY = y0;
   *pGcd = a0;
}

#endif
