// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef EXTENDED_EUCLIDEAN_PROOF_ASSERT_HELPER_GCD
#define EXTENDED_EUCLIDEAN_PROOF_ASSERT_HELPER_GCD 1

#include <assert.h>
#include <limits>

template <typename T>
T gcd(T a, T b)
{
	static_assert(std::numeric_limits<T>::is_integer, "");
	static_assert(std::numeric_limits<T>::is_signed, "");

	while (b != 0) {
		T tmp = b;
		b = a % b;
		a = tmp;
	}
	return (a >= 0) ? a : -a;
}

#endif
