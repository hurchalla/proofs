// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---


// Force NDEBUG to be undefined, since testing of the proofs requires assert().
#ifdef NDEBUG
#  undef NDEBUG
#endif


#include "extended_euclidean_proof.h"
#include <iostream>
#include <cstdint>
#include <limits>


int main(int argc, char *argv[])
{
   std::cout << "***Test Extended Euclidean Bounds Proof***\n\n";

   using T = int64_t;
   
   static_assert(std::numeric_limits<T>::is_integer, "");
   static_assert(std::numeric_limits<T>::is_signed, "");
   
   T a = 5;
   T b = 7;
   T gcd, x, y;
   extended_euclidean_proof(a, b, &gcd, &x, &y);

   // test all combinations of a and b such that 0 <= a < 256 and 0 <= b < 256
   static_assert(std::numeric_limits<T>::max() >= 256, "");
   for (T a = 0; a < 256; ++a) {
	   for (T b = 0; b < 256; ++b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   std::cout << "Passed exhaustive tests for all values 0 <= a < 256 with 0 <= b < 256.\n";


   // test large combinations of a and b where a and b are very large or small
   constexpr int64_t maxTmp = 65535;
   static_assert(std::numeric_limits<T>::max() >= maxTmp, "");
   T max = maxTmp;

   for (T a = 0; a < 5; ++a) {
	   for (T b = max; b >= 0; --b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   for (T a = max; a >= max - 5; --a) {
	   for (T b = max; b >= 0; --b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   a = max / 2;
   for (T b = max; b >= 0; --b)
	   extended_euclidean_proof(a, b, &gcd, &x, &y);


   for (T a = max; a >= 0; --a) {
	   for (T b = 0; b < 5; ++b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   for (T a = max; a >= 0; --a) {
	   for (T b = max; b >= max - 5; --b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   b = max / 2;
   for (T a = max; a >= 0; --a)
	   extended_euclidean_proof(a, b, &gcd, &x, &y);

   std::cout << "Passed large combination tests.\n";


   // test combinations of a and b where a and b are extremely large or small
   max = std::numeric_limits<T>::max();
   for (T a = 0; a < 5; ++a) {
	   for (T b = max; b >= max - 5; --b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   for (T a = max; a >= max - 5; --a) {
	   for (T b = max; b >= max - 5; --b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   a = max / 2;
   for (T b = max; b >= max - 5; --b)
	   extended_euclidean_proof(a, b, &gcd, &x, &y);

   for (T a = 0; a < 5; ++a) {
	   for (T b = 0; b <= 5; ++b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   for (T a = max; a >= max - 5; --a) {
	   for (T b = 0; b <= 5; ++b)
		   extended_euclidean_proof(a, b, &gcd, &x, &y);
   }
   a = max / 2;
   for (T b = 0; b <= 5; ++b)
	   extended_euclidean_proof(a, b, &gcd, &x, &y);

   extended_euclidean_proof(a, a, &gcd, &x, &y);

   std::cout << "Passed extremely large value tests.\n";


   std::cout << "\n*** Passed all tests ***\n";
   return 0;
}
