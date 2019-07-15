// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#include "unsigned_extended_euclidean.h"
#include "signed_extended_euclidean.h"
#include <type_traits>
#include <iostream>
#include <cstdint>
#include <limits>


template <class S, class U, class T>
int test_unsigned(U a, U b)
{
   static_assert(std::numeric_limits<T>::is_integer, "");
   static_assert(std::numeric_limits<T>::is_signed, "");
   static_assert(std::numeric_limits<S>::is_integer, "");
   static_assert(std::numeric_limits<S>::is_signed, "");
   static_assert(std::numeric_limits<U>::is_integer, "");
   static_assert(!(std::numeric_limits<U>::is_signed), "");
   static_assert(std::is_same<std::make_signed<U>::type, S>::value, "");
   U gcd;
   S x, y;
   T gcd2, x2, y2;
   unsigned_extended_euclidean(a, b, &gcd, &x, &y);
   signed_extended_euclidean<T>(a, b, &gcd2, &x2, &y2);
   if (gcd != gcd2 || x != x2 || y != y2) {
       std::cout << "test failed: a == " << a << ", b == " << b << "\n";
       return 1;
   }
   return 0;
}


int exhaustive_tests()
{
   using T = int64_t;
   using S = int8_t;
   using U = std::make_unsigned<S>::type;

   U a = 5;
   U b = 7;
   U gcd;
   S x, y;
   T gcd2, x2, y2;
   unsigned_extended_euclidean(a, b, &gcd, &x, &y);
   signed_extended_euclidean<T>(a, b, &gcd2, &x2, &y2);

   // test all combinations of a and b such that 0 <= a < 256 and 0 <= b < 256
   static_assert(std::numeric_limits<U>::max() >= 255, "");
   static_assert(std::numeric_limits<T>::max() >= 255, "");
   for (U a = 0;; ++a) {
       for (U b = 0;; ++b) {
           if (0 != test_unsigned<S, U, T>(a, b))
               return 1;
           if (b == 255)
               break;
       }
       if (a == 255)
           break;
   }
   std::cout << "Passed exhaustive tests for all values 0 <= a < 256 with 0 <= b < 256.\n";
   return 0;
}


int large_combination_tests()
{
   using S = int16_t;
   using U = std::make_unsigned<S>::type;
   using T = int64_t;

   // test large combinations of a and b where a and b are very large or small
   constexpr uint64_t max = std::numeric_limits<U>::max();
   static_assert(std::numeric_limits<uint64_t>::max() > max, "");
   static_assert(std::numeric_limits<T>::max() >= max, "");

   for (uint64_t a = 0; a < 5; ++a) {
       for (uint64_t b = 0; b <= max; ++b)
           if (0 != test_unsigned<S, U, T>(static_cast<U>(a),static_cast<U>(b)))
               return 1;
   }
   for (uint64_t a = max - 5; a <= max; ++a) {
       for (uint64_t b = 0; b <= max; ++b)
           if (0 != test_unsigned<S, U, T>(static_cast<U>(a),static_cast<U>(b)))
               return 1;
   }
   uint64_t a = max / 2;
   for (uint64_t b = 0; b <= max; ++b)
       if (0 != test_unsigned<S, U, T>(static_cast<U>(a), static_cast<U>(b)))
           return 1;


   for (uint64_t a = 0; a <= max; ++a) {
       for (uint64_t b = 0; b < 5; ++b)
           if (0 != test_unsigned<S, U, T>(static_cast<U>(a),static_cast<U>(b)))
               return 1;
   }
   for (uint64_t a = 0; a <= max; ++a) {
       for (uint64_t b = max - 5; b <= max; ++b)
           if (0 != test_unsigned<S, U, T>(static_cast<U>(a),static_cast<U>(b)))
               return 1;
   }
   uint64_t b = max / 2;
   for (uint64_t a = 0; a <= max; ++a)
       if (0 != test_unsigned<S, U, T>(static_cast<U>(a), static_cast<U>(b)))
           return 1;

   std::cout << "Passed large combination tests.\n";
   return 0;
}


int extreme_values_tests()
{
   using S = int32_t;
   using U = std::make_unsigned<S>::type;
   using T = int64_t;

   // test combinations of a and b where a and b are extremely large or small
   constexpr uint64_t max = std::numeric_limits<U>::max();
   static_assert(std::numeric_limits<uint64_t>::max() > max, "");
   static_assert(std::numeric_limits<T>::max() >= max, "");

   // test combinations of a and b where a and b are extremely large or small
   for (uint64_t a = 0; a < 5; ++a)
       for (uint64_t b = max - 5; b <= max; ++b)
           if (0 != test_unsigned<S, U, T>(static_cast<U>(a),static_cast<U>(b)))
               return 1;
   for (uint64_t a = max - 5; a <= max; ++a)
       for (uint64_t b = max - 5; b <= max; ++b)
           if (0 != test_unsigned<S, U, T>(static_cast<U>(a),static_cast<U>(b)))
               return 1;
   uint64_t a = max / 2;
   for (uint64_t b = max - 5; b <= max; ++b)
       if (0 != test_unsigned<S, U, T>(static_cast<U>(a), static_cast<U>(b)))
           return 1;

   for (uint64_t a = 0; a < 5; ++a)
       for (uint64_t b = 0; b <= 5; ++b)
           if (0 != test_unsigned<S, U, T>(static_cast<U>(a),static_cast<U>(b)))
               return 1;
   for (uint64_t a = max - 5; a <= max; ++a)
       for (uint64_t b = 0; b <= 5; ++b)
           if (0 != test_unsigned<S, U, T>(static_cast<U>(a),static_cast<U>(b)))
               return 1;

   a = max / 2;
   for (uint64_t b = 0; b <= 5; ++b)
       if (0 != test_unsigned<S, U, T>(static_cast<U>(a), static_cast<U>(b)))
           return 1;

   if (0 != test_unsigned<S, U, T>(static_cast<U>(a), static_cast<U>(a)))
       return 1;

   std::cout << "Passed extremely large value tests.\n";
   return 0;
}



int main(int argc, char *argv[])
{
   std::cout << "***Test Unsigned Inputs Extended Euclidean Function***\n\n";
   
   if (exhaustive_tests() != 0)
       return 1;
   if (large_combination_tests() != 0)
       return 1;
   if (extreme_values_tests() != 0)
       return 1;

   std::cout << "\n*** Passed all tests ***\n";
   return 0;
}
