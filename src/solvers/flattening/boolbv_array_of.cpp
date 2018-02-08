/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/arith_tools.h>
#include <util/std_types.h>

bvt boolbvt::convert_array_of(const array_of_exprt &expr)
{
  const array_typet &array_type=to_array_type(expr.type());
  if(is_unbounded_array(array_type))
    return conversion_failed(expr);

  const std::size_t width = boolbv_width(array_type);
  if(width==0)
  {
    // A zero-length array is acceptable;
    // an element with unknown size is not.
    if(boolbv_width(array_type.subtype())==0)
      return conversion_failed(expr);
    else
      return bvt();
  }

  const exprt &array_size=array_type.size();
  const auto size = numeric_cast<mp_integer>(array_size);

  if(!size)
    return conversion_failed(expr);

  const bvt &tmp=convert_bv(expr.op0());

  bvt bv;
  bv.resize(width);
  CHECK_RETURN(*size * tmp.size() == width);

  std::size_t offset=0;
  for(mp_integer i=0; i<size; i=i+1)
  {
    for(std::size_t j=0; j<tmp.size(); j++, offset++)
      bv[offset]=tmp[j];
  }

  INVARIANT(offset == bv.size(), "final offset should correspond to size");

  return bv;
}
