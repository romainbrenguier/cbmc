/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_MP_ARITH_H
#define CPROVER_UTIL_MP_ARITH_H

#include <string>
#include <iosfwd>
#include <limits>

#include "big-int/bigint.hh"
#include "optional.h"

// NOLINTNEXTLINE(readability/identifiers)
typedef BigInt mp_integer;

class exprt;

std::ostream &operator<<(std::ostream &, const mp_integer &);
mp_integer operator>>(const mp_integer &, const mp_integer &);
mp_integer operator<<(const mp_integer &, const mp_integer &);
mp_integer bitwise_or(const mp_integer &, const mp_integer &);
mp_integer bitwise_and(const mp_integer &, const mp_integer &);
mp_integer bitwise_xor(const mp_integer &, const mp_integer &);
mp_integer bitwise_neg(const mp_integer &);

mp_integer arith_left_shift(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer arith_right_shift(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer logic_left_shift(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer logic_right_shift(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer rotate_right(
  const mp_integer &, const mp_integer &, std::size_t true_size);

mp_integer rotate_left(
  const mp_integer &, const mp_integer &, std::size_t true_size);

const std::string integer2string(const mp_integer &, unsigned base=10);
const mp_integer string2integer(const std::string &, unsigned base=10);
const std::string integer2binary(const mp_integer &, std::size_t width);
const mp_integer binary2integer(const std::string &, bool is_signed);

/// \deprecated use numeric_cast<unsigned long long> instead
mp_integer::ullong_t integer2ulong(const mp_integer &);

/// \deprecated use numeric_cast<std::size_t> instead
std::size_t integer2size_t(const mp_integer &);

/// \deprecated use numeric_cast<unsigned> instead
unsigned integer2unsigned(const mp_integer &);

const mp_integer mp_zero=string2integer("0");

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

/// Numerical cast provides a unified way of converting from one numerical type
/// to another.
/// Generic case doesn't exist, this has to be specialized for different types.
template <typename Target, typename = void>
struct numeric_castt final
{
};

template <>
struct numeric_castt<mp_integer> final
{
  optionalt<mp_integer> operator()(const exprt &expr) const
  {
    mp_integer out;
    if(to_integer(expr, out))
      return {};
    return out;
  }
};

/// Convert mp_integer to any signed type
/// \tparam T: type to convert to
/// \param mpi: mp_integer to convert
/// \return optional integer of type T if conversion is possible,
///         empty optional otherwise.
template <typename T>
struct numeric_castt<T,
                     typename std::enable_if<std::is_integral<T>::value>::type>
{
  template <typename U = T,
            typename std::enable_if<std::is_signed<U>::value, int>::type = 0>
  static auto get_val(const mp_integer &mpi) -> decltype(mpi.to_long())
  {
    return mpi.to_long();
  }

  template <typename U = T,
            typename std::enable_if<!std::is_signed<U>::value, int>::type = 0>
  static auto get_val(const mp_integer &mpi) -> decltype(mpi.to_ulong())
  {
    return mpi.to_ulong();
  }

  optionalt<T> operator()(const mp_integer &mpi) const
  {
    constexpr const auto precondition =
      std::numeric_limits<T>::max() <=
        std::numeric_limits<decltype(get_val(mpi))>::max() &&
      std::numeric_limits<T>::min() >=
        std::numeric_limits<decltype(get_val(mpi))>::min();
#if !defined(_MSC_VER) || _MSC_VER >= 1900
    static_assert(
      precondition,
      "Numeric cast only works for types within appropriate range");
#else
    PRECONDITION(precondition);
#endif
    if(
      mpi <= std::numeric_limits<T>::max() &&
      mpi >= std::numeric_limits<T>::min())
    {
      return static_cast<T>(get_val(mpi));
    }
    return {};
  }

  optionalt<T> operator()(const exprt &expr) const
  {
    auto mpi_opt = numeric_castt<mp_integer>{}(expr);
    if(mpi_opt)
      return numeric_castt<T>{}(*mpi_opt);
    else
      return {};
  }
};

template <typename Target, typename Source>
optionalt<Target> numeric_cast(const Source &arg)
{
  return numeric_castt<Target>{}(arg);
}

/// An invariant with fail with message "Bad conversion" if conversion
/// is not possible.
/// \tparam Target: type to convert to
/// \tparam Source: type to convert from
/// \param arg: constant expression
/// \return value of type T
template <typename Target, typename Source>
Target numeric_cast_v(const Source &arg)
{
  const auto maybe = numeric_castt<Target>{}(arg);
  INVARIANT(maybe, "Bad conversion");
  return *maybe;
}

#endif // CPROVER_UTIL_MP_ARITH_H
