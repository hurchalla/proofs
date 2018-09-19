// --- This file is distributed under the MIT Open Source License, as detailed
// in the file "LICENSE.TXT" in the root of this repository ---

#ifndef EXTENDED_EUCLIDEAN_COLLINS
#define EXTENDED_EUCLIDEAN_COLLINS  1


#ifndef NDEBUG
#  include "helpers/assert_helper_gcd.h"
#endif
#include <assert.h>

#if defined(assert_invariant) || defined(assert_precondition)
#  error "assert_invariant and/or assert_precondition were already defined"
#endif
// assert aliases will help self-document the code
#define assert_invariant     assert
#define assert_precondition  assert


/*P1*/  // Positive Integer Division Definition:
        // If u>=0 and v>0 then the operation q = u/v produces an integer q
        // such that u == v*q + r, with 0 <= r < v.

/*P2*/  // Theorem 1: If u>=0 and v>0, and t*v <= u, then  t <= u/v.
        // Proof: Letting q = u/v, by [P1] q satisfies 
        // u == v*q + r,  with 0 <= r < v.  Since we're given t*v <= u,
        // t*v <= u == v*q + r.  Since 0 <= r < v,
        // t*v <= u == v*q + r < v*q + v == v*(q+1)
        // Hence t*v < v*(q+1)  and  t < q+1.
        // t < q+1 implies t <= q, and since q == u/v, we have  t <= u/v.

/*P3*/  // Theorem 2: If u>=0 and v>0 and q == u/v, then  q*v <= u.
        // Proof: Since q == u/v, by [P1] q satisfies
        // u == v*q + r,  with 0 <= r < v.  Since r >= 0,
        // u == v*q + r >= v*q + 0.  Hence  q*v <= u.

/*P4*/  // Generalized Euclid's Lemma:  If integers u and v are coprime,
        // and u*m == v*n,  then  u divides n, and v divides m.
        // Proof: Since u and v are coprime, by Bezout's identity there exist
        // integers j,k such that  j*u + k*v == 1.
        // Multiplying both sides by m,  j*u*m + k*v*m == m.  Since u*m == v*n,
        // j*v*n + k*v*m == m.  Since v divides both terms on the left, it must
        // divide the single term on the right.  Thus v divides m.
        // Again using  j*u + k*v == 1,  multiplying both sides by n results in
        // j*u*n + k*v*n == n.  Since u*m == v*n,  j*u*n + k*u*m == n.  Since
        // u divides both terms on the left, it must divide the single term on
        // the right.  Thus u divides n.
        
/*P5*/  // Theorem 3: If a divides b and b divides a, then a == +- b.
        // Proof: a divides b implies there exists an integer g such that
        // g*a == b.  Likewise, b divides a implies there exists an integer h
        // such that  a == h*b.  By substitution,
        //     a == h*(g*a)
        //     0 == a*(h*g - 1)
        // therefore a == 0 or (h*g-1) == 0.
        // If we assume a == 0, then since g*a == b, we would also have b == 0.
        //    Having both a == 0 and b == 0 would satisfy a == +- b.
        // Alternately, if we assume (h*g-1) == 0, we would have h*g == 1,
        // which would require either h==1 and g==1, or h == -1 and g == -1.
        // If we have h==1 and g==1, then since g*a == b, we would have a == b,
        // which satisfies a == +- b.  If we have instead h == -1 and g == -1,
        // then since g*a == b, we would have -a == b, which also
        // satisfies a == +- b.  All cases satisfy a == +- b.

/*P6*/  // Theorem 4: If integers u and v are coprime, and integers m and n
        // are coprime, and u*m == v*n,  then
        // abs(u) == abs(n) and abs(m) == abs(v).
        // Proof: By [P4], u divides n, and v divides m.  Also by [P4],
        // m divides v, and n divides u.  Since u divides n and n divides u,
        // by [P5] u == +- n, and thus abs(u) == abs(n).  Since v divides m
        // and m divides m, by [P5] v == +- m, and thus abs(v) == abs(m).


// This proof follows the presentation by George E. Collins, Mathematics of
// Computation 23 (1969), p.198, "Computing Multiplicative Inverses in GF(p)"
// http://www.ams.org/journals/mcom/1969-23-105/S0025-5718-1969-0242345-5/S0025-5718-1969-0242345-5.pdf

template <typename T>
void extended_euclidean_collins(T a, T b, T* pGcd, T* pX, T* pY)
{
/*01*/     assert_precondition(b >= 0);
/*02*/     assert_precondition(b < a);
/*03*/  T x0 = 1;
/*04*/  T y0 = 0;
/*05*/  T a0 = a;
/*06*/  T x1 = 0;
/*07*/  T y1 = 1;
/*08*/  T a1 = b;

/*09*/     assert_invariant(a > 0);            // By [01, 02]
/*10*/     assert_invariant(gcd(a,b) >= 1);
           // Proof: By [09] a > 0, so gcd(a,b) != gcd(0,0).  Since 1 is a
           // common divisor of both a and b, gcd(a,b) >= 1

/*11*/     assert_invariant(a0 > 0);           // By [05, 09]
/*12*/     assert(a1 >= 0);                    // By [08, 01]
/*13*/     assert_invariant(a1 < a0);          // By [08, 05, 02]
/*14*/     assert_invariant(a*x0 + b*y0 == a0);// Proof: By [03, 04, 05],
                                               // a*x0+b*y0 == a*1+b*0 == a== a0
/*15*/     assert_invariant(a*x1 + b*y1 == a1);// Proof: By [06, 07, 08],
                                               // a*x1+b*y1 == a*0+b*1 == b== a1
/*16*/     assert_invariant(gcd(a0,a1) == gcd(a,b));  // By [05, 08]

/*17*/     assert_invariant(abs(x0*y1 - y0*x1) == 1); // Proof: By [03,07,04,06]
                                                      // abs(x0*y1 - y0*x1) ==
                                                      // abs(1*1 - 0*0) == 1
/*18*/     T s0 = 1;    // informally, s0 represents the sign of x0.
/*19*/     T s1 = -1;   // the sign of x1 (values <= 0 treated as negative)
/*20*/     assert_invariant(s1 == -s0);        // By [18, 19]
/*21*/     assert_invariant(abs(s0) == 1);     // By [18]
/*22*/     assert_invariant(s0*abs(x0) == x0); // By [03, 18], x0 == 1, s0 == 1.
                                               // s0*abs(x0) == 1*1 == 1 == x0
/*23*/     assert_invariant(s1*abs(x1) == x1); // By [06,19], x1 == 0, s1 == -1.
                                               // s1*abs(x1) == -1*0 == 0 == x1
/*24*/     assert_invariant(-s0*abs(y0) == y0);// By [04, 18], y0 == 0, s0 == 1.
                                               // -s0*abs(y0) == -1*0 == 0 == y0
/*25*/     assert_invariant(-s1*abs(y1) == y1);// By [07,19], y1 == 1, s1 == -1.
                                               // -s1*abs(y1) == 1*1 == 1 == y1

/*26*/     assert(abs(y1) >= 2*abs(y0));       // By [07, 04], y1 == 1, y0 == 0.
                                               // abs(y1) == 1 >= 0 == 2*abs(y0)
/*27*/     assert_invariant(gcd(x1,y1) == 1);  // By [06, 07], x1 == 0, y1 == 1.
                                               // gcd(x1,y1) == gcd(0,1) == 1

/*28*/  while (a1 != 0) {
/*29*/        assert_invariant(a0 > 0);                   // By [11, 80]
/*30*/        assert(a1 > 0);
              // Proof: By [12, 81] a1 >= 0, and by [28] a1 != 0, so  a1 > 0.
/*31*/        assert_invariant(a1 < a0);                  // By [13, 82]
/*32*/        assert_invariant(a*x0 + b*y0 == a0);        // By [14, 83]
/*33*/        assert_invariant(a*x1 + b*y1 == a1);        // By [15, 84]
/*34*/        assert_invariant(gcd(a0,a1) == gcd(a,b));   // By [16, 85]
/*35*/        assert_invariant(abs(x0*y1 - y0*x1) == 1);  // By [17, 86]
/*36*/        assert_invariant(s1 == -s0);                // By [20, 87]
/*37*/        assert_invariant(abs(s0) == 1);             // By [21, 88]
/*38*/        assert_invariant(s0*abs(x0) == x0);         // By [22, 89]
/*39*/        assert_invariant(s1*abs(x1) == x1);         // By [23, 90]
/*40*/        assert_invariant(-s0*abs(y0) == y0);        // By [24, 91]
/*41*/        assert_invariant(-s1*abs(y1) == y1);        // By [25, 92]
/*42*/        assert(abs(s1) == 1); // By [36,37] s1== -s0. abs(s1)==abs(s0)== 1
/*43*/     T q = a0/a1;
/*44*/        assert(1 <= q && q <= a0);
              // Proof:  By [43]  q == a0/a1  (note that a1 might not divide a0)
              // By [30, 31]  a1>0  and  a1<a0,  so  0 < a1 < a0,  and thus,
              // q == a0/a1 >= 1.
              // Since  0 < a1  implies  a1 >= 1,  we have  q == a0/a1 <= a0.
/*45*/     T a2 = a0 - q*a1;
              if (a2 != 0) {
/*46*/            assert(q <= a0 / 2);
                  // Proof : Assume a1 == 1.  Then by [43],  q == a0/a1 == a0.
                  // By [45],  a2 == a0 - q*a1, and since  q == a0,
                  // a2 == a0 - a0*a1.  Thus, given the assumption a1 == 1,
                  // a2 == a0 - a0*1 == 0.  But a2 == 0 is a contradiction, 
                  // because entering this clause requires  a2 != 0.  Therefore,
                  //    a1 != 1
                  // By [30]  a1 > 0,  and so, since a1 != 1,  a1 >= 2
                  // Since  q == a0/a1  and  a1 >= 2  and by [29] a0 > 0,
                  // q <= a0 / 2
              }
/*47*/        assert(0 < (q*a1) && (q*a1) <= a0);
              // Proof: By [44, 30],  q >= 1  and  a1 > 0,  so  q*a1 > 0.
              // By [43], q == a0/a1, and by [29, 30], a0 > 0 and a1 > 0.
              // Hence by [P3], q*a1 <= a0.
/*48*/        assert(0 <= a2 && a2 < a1);
              // Proof: By [29, 30], a0 > 0 and a1 > 0, and by [43] q == a0/a1,
              // so by [P1] q satisfies a0 == a1*q + r,  with 0 <= r < a1.
              // Thus, a0 - q*a1 == r.  By [45]  a0 - q*a1 == a2, so  a2 == r.
              // Since 0 <= r < a1, we know 0 <= a2 < a1
/*49*/        assert(gcd(a0,a1) == gcd(a1,a2));
              // Proof: By definition d = gcd(a0,a1) divides both a0 and a1.  So
              // since by [45]  a2 == a0 - q*a1,  d must also divide a2.  Thus d
              // is a common divisor of a1 and a2, and so d divides gcd(a1,a2).
              // Thus gcd(a0,a1) divides gcd(a1,a2).
              // Similarly, c = gcd(a1,a2) divides both a1 and a2, and since
              // by [45]  a0 == a2 + q*a1,  c must also divide a0.  Thus c is a
              // common divisor of a0 and a1, and so c divides gcd(a0,a1).  Thus
              // gcd(a1,a2) divides gcd(a0,a1).  Since both gcd(a0,a1) divides
              // gcd(a1,a2), and gcd(a1,a2) divides gcd(a0,a1), we know by [P5],
              //     gcd(a0,a1) == +- gcd(a1,a2).
              // Since gcds are never negative, gcd(a0,a1) == gcd(a1,a2).
/*50*/        assert(gcd(a1,a2) == gcd(a,b));
              // Proof: By [49] gcd(a0,a1) == gcd(a1,a2). And by [34]
              // gcd(a0,a1) == gcd(a,b). Therefore  gcd(a1,a2) == gcd(a,b).
/*51*/     T x2 = x0 - q*x1;
/*52*/        assert(x2 == s0*(abs(x0) + abs(q*x1)));
              // Proof: By [38, 39],  x0 == s0*abs(x0)  and  x1 == s1*abs(x1).
              // By [51], x2 == x0 - q*x1, thus  x2 == s0*abs(x0) - q*s1*abs(x1)
              // By [36], s1 == -s0,  so  x2 == s0*abs(x0) + q*s0*abs(x1).
              // And thus  x2 == s0*(abs(x0) + q*abs(x1)).  By [44], q >= 1, so
              // x2 == s0*(abs(x0) + abs(q*x1))
/*53*/        assert(abs(x2) == abs(x0) + abs(q*x1));
              // Proof: By [52],  x2 == s0*(abs(x0) + abs(q*x1)),  so
              // abs(x2) == abs(s0)*abs(abs(x0) + abs(q*x1))
              // abs(x2) == abs(s0)*(abs(x0) + abs(q*x1)
              // Since by [37], abs(s0) == 1,  abs(x2) == abs(x0) + abs(q*x1).
/*54*/        assert(abs(q*x1) <= abs(x2));     // By [53]
/*55*/        assert(abs(x1) <= abs(x2));
              // Proof: By [44], q >= 1, so  abs(x1) <= abs(q*x1)
              // By [54], abs(q*x1) <= abs(x2), thus
              // abs(x1) <= abs(q*x1) <= abs(x2)
/*56*/     T y2 = y0 - q*y1;
/*57*/        assert(y2 == -s0*(abs(y0) + abs(q*y1)));
              // Proof: By [40, 41],  y0 == -s0*abs(y0)  and  y1 == -s1*abs(y1).
              // By [56], y2 == y0 - q*y1,  so  y2 == -s0*abs(y0) + q*s1*abs(y1)
              // By [36], s1 == -s0,  so  y2 == -s0*abs(y0) - q*s0*abs(y1).
              // And thus  y2 == -s0*(abs(y0) + q*abs(y1)).  By [44], q >= 1, so
              // y2 == -s0*(abs(y0) + abs(q*y1))
/*58*/        assert(abs(y2) == abs(y0) + abs(q*y1));
              // Proof: By [57],  y2 == -s0*(abs(y0) + abs(q*y1)),  so
              // abs(y2) == abs(-s0)*abs(abs(y0) + abs(q*y1))
              // abs(y2) == abs(s0)*(abs(y0) + abs(q*y1))
              // Since by [37], abs(s0) == 1,  abs(y2) == abs(y0) + abs(q*y1).
/*59*/        assert(abs(q*y1) <= abs(y2));     // By [58]
/*60*/        assert(abs(y1) <= abs(y2));
              // Proof: By [44], q >= 1, so  abs(y1) <= abs(q*y1)
              // By [59], abs(q*y1) <= abs(y2), thus
              // abs(y1) <= abs(q*y1) <= abs(y2)

/*61*/        T s2 = -s1;
/*62*/        assert(s2 == s0);                // By [61, 36]
/*63*/        assert(s2*abs(x2) == x2);
              // Proof: By [53], abs(x2) == (abs(x0) + abs(q*x1)).
              // By [52], x2 == s0*(abs(x0) + abs(q*x1)),  so  x2 == s0*abs(x2).
              // By [62], s2 == s0,  thus  x2 == s2*abs(x2).
/*64*/        assert(-s2*abs(y2) == y2);
              // Proof: By [58], abs(y2) == (abs(y0) + abs(q*y1))
              // By [57], y2 == -s0*(abs(y0) + abs(q*y1)), so  y2 == -s0*abs(y2)
              // By [62], s2 == s0,  thus  y2 == -s2*abs(y2).
/*65*/        if (a2 == 0) {
/*66*/            assert(q >= 2);
                  // Proof: By [45], a2 == a0 - q*a1
                  // Hence by [65],  0 == a0 - q*a1  and  a0 == q*a1.
                  // If we assume  q==1, then since we just showed  a0 == q*a1,
                  // we would have  a0 == a1,  which contradicts [31]  a1 < a0.
                  // Therefore q!=1, and since by [44], q >= 1, we know  q >= 2.
/*67*/            assert(abs(x2) >= 2*abs(x1));
                  // Proof: By [54], abs(x2) >= abs(q*x1). Since by [66] q >= 2,
                  // abs(x2) >= q*abs(x1) >= 2*abs(x1).
/*68*/            assert(abs(y2) >= 2*abs(y1));
                  // Proof: By [59], abs(y2) >= abs(q*y1). Since by [66] q >= 2,
                  // abs(y2) >= q*abs(y1) >= 2*abs(y1).
              }
/*69*/        assert((x1*y2 - y1*x2) == -(x0*y1 - y0*x1));
              // Proof: Using the definition of the determinant, let
              //    D0 = x0*y1 - y0*x1  and  D1 = x1*y2 - y1*x2.
              // By [56, 51],
              //    D1 == x1*(y0 - q*y1) - y1*(x0 - q*x1)
              //    D1 == x1*y0 - y1*q*x1 - y1*x0 + y1*q*x1
              //    D1 == x1*y0 - y1*x0
              //    D1 == -D0
/*70*/        assert(abs(x1*y2 - y1*x2) == 1);
              // Proof: By [35],  abs(x0*y1 - y0*x1) == 1
              // By [69],  (x1*y2 - y1*x2) == -(x0*y1 - y0*x1)
              // Thus,  abs(x1*y2 - y1*x2) == abs(x0*y1 - y0*x1) == 1
/*71*/        assert(a*x2 + b*y2 == a2);
              // Proof: By [45],  a2 == a0 - q*a1
              // and thus by [32, 33],
              //    a2 == a*x0 + b*y0 - q*(a*x1 + b*y1)
              //    a2 == a*x0 - q*a*x1 + b*y0 - q*b*y1
              //    a2 == a*(x0 - q*x1) + b*(y0 - q*y1)
              // and by [51, 56],
              //    a2 == a*x2 + b*y2
/*72*/     x0 = x1;
/*73*/     y0 = y1;
/*74*/     a0 = a1;
/*75*/     x1 = x2;
/*76*/     y1 = y2;
/*77*/     a1 = a2;
/*78*/        s0 = s1;
/*79*/        s1 = s2;
              // trivially, we know at this point
/*80*/        assert_invariant(a0 > 0);               // By [30, 74]
/*81*/        assert(a1 >= 0);                        // By [48, 77]
/*82*/        assert_invariant(a1 < a0);              // By [48, 74, 77]
/*83*/        assert_invariant(a*x0 + b*y0 == a0);    // By [33, 72, 73, 74]
/*84*/        assert_invariant(a*x1 + b*y1 == a1);    // By [71, 75, 76, 77]
/*85*/        assert_invariant(gcd(a0,a1) == gcd(a,b));  // By [50, 74, 77]
/*86*/        assert_invariant(abs(x0*y1 - y0*x1) == 1); // By [70,72,73,75,76]
/*87*/        assert_invariant(s1 == -s0);            // By [61, 79, 78]
/*88*/        assert_invariant(abs(s0) == 1);         // By [42, 78]
/*89*/        assert_invariant(s0*abs(x0) == x0);     // By [39, 78, 72]
/*90*/        assert_invariant(s1*abs(x1) == x1);     // By [63, 79, 75]
/*91*/        assert_invariant(-s0*abs(y0) == y0);    // By [41, 78, 73]
/*92*/        assert_invariant(-s1*abs(y1) == y1);    // By [64, 79, 76]
/*93*/        assert(abs(x1) >= abs(x0));             // By [55, 75, 72]
/*94*/        assert(abs(y1) >= abs(y0));             // By [60, 76, 73]
/*95*/        if (a1 == 0) {
/*96*/             assert(abs(x1) >= 2*abs(x0));      // By [65, 67, 77, 75, 72]
/*97*/             assert(abs(y1) >= 2*abs(y0));      // By [65, 68, 77, 76, 73]
              }
              // Less trivially,
/*98*/        assert_invariant(gcd(x1, y1) == 1);
              // Proof: By [86]  x0*y1 - y0*x1 == +-1,  so there obviously
              // exist integers u and v such that u*y1 + v*x1 == 1.
              // Let d be any common divisor of x1 and y1 (we know a common
              // divisor exists since 1 divides x1 and y1).  Since d divides
              // both x1 and y1,  d divides u*y1 + v*x1 == 1,  and thus
              // d divides 1.  Since d divides 1, d == +-1.  Thus a common 
              // divisor of x1 and y1 can only be -1 or 1, and since 1 is a
              // common divisor of x1 and y1, the greatest common divisor of x1
              // and y1 is 1.  For a similar proof see 
              // http://people.sju.edu/~pklingsb/rp.fta.pdf
        }

/*99*/     assert(a1 == 0);
           // Since we finished the loop, we know a1 == 0 at this point.
/*M0*/     assert(x1*(a/gcd(a,b)) == -y1*(b/gcd(a,b)));
           // Proof: By [15,84],  a*x1 + b*y1 == a1,  and so by [99]
           //    a*x1 + b*y1 == 0
           //    x1*a == -y1*b
           // Letting d = gcd(a,b), by [10] d >= 1.  Since d divides a and b,
           // and x1*a == -y1*b,  we know  x1*(a/d) == -y1*(b/d)
/*M1*/     assert(gcd(a/gcd(a,b), b/gcd(a,b)) == 1);
           // Proof: Letting d=gcd(a,b), by [10] d >= 1.  Since d contains all
           // the common divisors of a and b, d divides both a and b, and the
           // quotients of a/d and b/d have no common divisors except 1 and -1.
           // Therefore gcd(a/d, b/d) == 1.
/*M2*/     assert(abs(x1) == b/gcd(a,b));
           // Proof: Letting d = gcd(a,b), by [M0]  x1*(a/d) == -y1*(b/d).
           // By [M1] (a/d) and (b/d) are coprime, and by [27,98] x1 and -y1 are
           // coprime.  So by [P6], abs(a/d)==abs(-y1)  and  abs(x1)==abs(b/d).
           // By [10,01],  d>0 and b>=0,  so  abs(b/d) == b/d.
           // Thus, abs(x1) == abs(b/d) == b/d
/*M3*/     assert(abs(y1) == a/gcd(a,b));
           // Proof: Letting d = gcd(a,b), by [M0]  x1*(a/d) == -y1*(b/d).
           // By [M1] (a/d) and (b/d) are coprime, and by [27,98] x1 and -y1 are
           // coprime.  So by [P6], abs(a/d)==abs(-y1)  and  abs(x1)==abs(b/d).
           // By [10,09],  d>0 and a>0,  so  abs(a/d) == a/d.
           // Thus, abs(y1) == abs(-y1) == abs(a/d) == a/d
/*M4*/     assert((x0 == 1 && x1 == 0) || (abs(x1) >= 2*abs(x0)));
           // Proof: By [03, 06, 95, 96, 99]
/*M5*/     assert(abs(y1) >= 2*abs(y0));           // By [26, 95, 97, 99]
/*M6*/     assert(x0 == 1 || abs(x0) <= (b/gcd(a,b))/2);
           // Proof: By [M4], (x0 == 1 && x1 == 0) || (abs(x1) >= 2*abs(x0)),
           // Assume (x0 == 1 && x1 == 0).  Then we would have  x0 == 1.
           // Assume instead  (abs(x1) >= 2*abs(x0)).  By [M2],
           // abs(x1) == b/gcd(a,b).  Thus we would have 
           // b/gcd(a,b) == abs(x1) >= 2*abs(x0).  Letting d = gcd(a,b), we
           // would have  abs(x0)*2 <= b/d.  By [01,10] b >= 0 and d > 0, so
           // (b/d) >= 0.  Since (b/d) >= 0 and 2 > 0 and abs(x0)*2 <= (b/d),
           // by [P2] we would have  abs(x0) <= (b/d)/2.
           // Thus x0 == 1, or abs(x0) <= (b/d)/2.
/*M7*/     assert(abs(y0) <= (a/gcd(a,b))/2);
           // Proof: By [M5], abs(y1) >= 2*abs(y0), and by [M3],
           // abs(y1) == a/gcd(a,b).  Thus,  a/gcd(a,b) == abs(y1) >= 2*abs(y0).
           // Letting d = gcd(a,b),  abs(y0)*2 <= a/d.  By [09, 10] a > 0 and
           // d > 0, so (a/d) >= 0.  Since (a/d) >= 0 and 2 > 0 and
           // abs(y0)*2 <= (a/d), by [P2]  abs(y0) <= (a/d)/2.
/*M8*/     assert(a0 == gcd(a,b));
           // Proof: By [99] a1 == 0, and by [11,80] a0 > 0, so
           // gcd(a0,a1) == gcd(a0,0) == a0.
           // By [16,85] gcd(a0,a1) == gcd(a,b).  Therefore,
           // a0 == gcd(a0,a1) == gcd(a,b)
/*M9*/     assert(a*x0 + b*y0 == gcd(a,b));
           // By [14,83] a*x0 + b*y0 == a0, and so by [M8],
           // a*x0 + b*y0 == a0 == gcd(a,b)
           // Note: Since a*x0 + b*y0 == gcd(a,b), we know x0 and y0 are the
           // Bezout coefficients.
        *pX = x0;
        *pY = y0;
        *pGcd = a0;
}

#undef assert_invariant
#undef assert_precondition

#endif
