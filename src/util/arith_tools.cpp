/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arith_tools.h"

#include <cassert>

#include "fixedbv.h"
#include "ieee_float.h"
#include "std_types.h"
#include "std_expr.h"

constant_exprt from_integer(
  const mp_integer &int_value,
  const typet &type)
{
  const irep_idt &type_id=type.id();

  if(type_id==ID_integer)
  {
    constant_exprt result(type);
    result.set_value(integer2string(int_value));
    return result;
  }
  else if(type_id==ID_natural)
  {
    if(int_value<0)
    {
      constant_exprt r;
      r.make_nil();
      return r;
    }
    constant_exprt result(type);
    result.set_value(integer2string(int_value));
    return result;
  }
  else if(type_id==ID_unsignedbv)
  {
    std::size_t width=to_unsignedbv_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_bv)
  {
    std::size_t width=to_bv_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_signedbv)
  {
    std::size_t width=to_signedbv_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_c_enum)
  {
    std::size_t width=to_c_enum_type(type).subtype().get_unsigned_int(ID_width);
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_c_bool)
  {
    std::size_t width=to_c_bool_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_bool)
  {
    if(int_value==0)
      return false_exprt();
    else if(int_value==1)
      return true_exprt();
  }
  else if(type_id==ID_pointer)
  {
    if(int_value==0)
      return null_pointer_exprt(to_pointer_type(type));
  }
  else if(type_id==ID_c_bit_field)
  {
    std::size_t width=to_c_bit_field_type(type).get_width();
    constant_exprt result(type);
    result.set_value(integer2binary(int_value, width));
    return result;
  }
  else if(type_id==ID_fixedbv)
  {
    fixedbvt fixedbv;
    fixedbv.spec=fixedbv_spect(to_fixedbv_type(type));
    fixedbv.from_integer(int_value);
    return fixedbv.to_expr();
  }
  else if(type_id==ID_floatbv)
  {
    ieee_floatt ieee_float(to_floatbv_type(type));
    ieee_float.from_integer(int_value);
    return ieee_float.to_expr();
  }

  {
    PRECONDITION(false);
    constant_exprt r;
    r.make_nil();
    return r;
  }
}

/// ceil(log2(size))
mp_integer address_bits(const mp_integer &size)
{
  mp_integer result, x=2;

  for(result=1; x<size; result+=1, x*=2) {}

  return result;
}

/// A multi-precision implementation of the power operator.
/// \par parameters: Two mp_integers, base and exponent
/// \return One mp_integer with the value base^{exponent}
mp_integer power(const mp_integer &base,
                 const mp_integer &exponent)
{
  assert(exponent>=0);

  /* There are a number of special cases which are:
   *  A. very common
   *  B. handled more efficiently
   */
  if(base.is_long() && exponent.is_long())
  {
    switch(base.to_long())
    {
    case 2:
      {
        mp_integer result;
        result.setPower2(exponent.to_ulong());
        return result;
      }
    case 1: return 1;
    case 0: return 0;
    default:
      {
      }
    }
  }

  if(exponent==0)
    return 1;

  if(base<0)
  {
    mp_integer result = power(-base, exponent);
    if(exponent.is_odd())
      return -result;
    else
      return result;
  }

  mp_integer result=base;
  mp_integer count=exponent-1;

  while(count!=0)
  {
    result*=base;
    --count;
  }

  return result;
}

void mp_min(mp_integer &a, const mp_integer &b)
{
  if(b<a)
    a=b;
}

void mp_max(mp_integer &a, const mp_integer &b)
{
  if(b>a)
    a=b;
}
