// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef SIGNED_EXTENDED_EUCLIDEAN
#define SIGNED_EXTENDED_EUCLIDEAN 1

#include <limits>
#include <assert.h>


template <class T>
void signed_extended_euclidean(const T a, const T b, T* pGcd, T* pX, T* pY)
{
   static_assert(std::numeric_limits<T>::is_integer, "");
   static_assert(std::numeric_limits<T>::is_signed, "");
   assert(a >= 0 && b >= 0);   // precondition
   T x0=1, y0=0, a0=a;
   T x1=0, y1=1, a1=b;

   while (a1 != 0) {
      T q = a0/a1;
      T a2 = a0 - q*a1;
      T x2 = x0 - q*x1;
      T y2 = y0 - q*y1;
      x0=x1; y0=y1; a0=a1;
      x1=x2; y1=y2; a1=a2;
   }
   *pX = x0;
   *pY = y0;
   *pGcd = a0;
}

#endif
