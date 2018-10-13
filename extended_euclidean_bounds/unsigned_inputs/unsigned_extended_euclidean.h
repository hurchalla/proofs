// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef UNSIGNED_EXTENDED_EUCLIDEAN
#define UNSIGNED_EXTENDED_EUCLIDEAN 1

#include <limits>
#include <type_traits>


template <class S, class U>
void unsigned_extended_euclidean(const U a, const U b, U* pGcd, S* pX, S* pY)
{
   static_assert(std::numeric_limits<S>::is_integer, "");
   static_assert(std::numeric_limits<S>::is_signed, "");
   static_assert(std::numeric_limits<U>::is_integer, "");
   static_assert(!(std::numeric_limits<U>::is_signed), "");
   static_assert(std::is_same<std::make_signed<U>::type, S>::value, "");
   S x1=1, y1=0;
   U a1=a;
   S x0=0, y0=1;
   U a2=b, q=0;

   while (a2 != 0) {
      S x2 = x0 - static_cast<S>(q)*x1;
      S y2 = y0 - static_cast<S>(q)*y1;
      x0=x1; y0=y1;
      U a0=a1;
      x1=x2; y1=y2; a1=a2;

      q = a0/a1;
      a2 = a0 - q*a1;
   }
   *pX = x1;
   *pY = y1;
   *pGcd = a1;
}

#endif
