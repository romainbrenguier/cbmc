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

// this one will go away
// returns 'true' on error
/// \deprecated: use the constant_exprt version instead
bool to_integer(const exprt &expr, mp_integer &int_value);

// returns 'true' on error
/// \deprecated: use numeric_cast<mp_integer> instead
bool to_integer(const constant_exprt &expr, mp_integer &int_value);

// returns 'true' on error
bool to_unsigned_integer(const constant_exprt &expr, unsigned &uint_value);

template <>
struct numeric_castt<mp_integer, exprt> final
{
  static optionalt<mp_integer> numeric_cast(const exprt &expr)
  {
    mp_integer out;
    if(to_integer(expr, out))
      return {};
    return out;
  }
};

/// Convert an expression to an integer type.
/// \tparam T: type to convert to
/// \param expr: constant expression
/// \return optional value of type T
template <typename T>
struct numeric_castt<T,
                     exprt,
                     typename std::enable_if<std::is_integral<T>::value>::type>
{
  static optionalt<T> numeric_cast(const exprt &expr)
  {
    auto mpi_opt = numeric_castt<mp_integer, exprt>::numeric_cast(expr);
    if(mpi_opt)
      return numeric_castt<T, mp_integer>::numeric_cast(*mpi_opt);
    else
      return {};
  }
};

// PRECONDITION(false) in case of unsupported type
constant_exprt from_integer(const mp_integer &int_value, const typet &type);

// ceil(log2(size))
mp_integer address_bits(const mp_integer &size);

mp_integer power(const mp_integer &base, const mp_integer &exponent);

void mp_min(mp_integer &a, const mp_integer &b);
void mp_max(mp_integer &a, const mp_integer &b);

#endif // CPROVER_UTIL_ARITH_TOOLS_H
