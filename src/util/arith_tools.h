/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_ARITH_TOOLS_H
#define CPROVER_UTIL_ARITH_TOOLS_H

#include "mp_arith.h"
#include "optional.h"
#include "invariant.h"

class exprt;
class constant_exprt;
class typet;

// PRECONDITION(false) in case of unsupported type
constant_exprt from_integer(const mp_integer &int_value, const typet &type);

// ceil(log2(size))
mp_integer address_bits(const mp_integer &size);

mp_integer power(const mp_integer &base, const mp_integer &exponent);

void mp_min(mp_integer &a, const mp_integer &b);
void mp_max(mp_integer &a, const mp_integer &b);

#endif // CPROVER_UTIL_ARITH_TOOLS_H
