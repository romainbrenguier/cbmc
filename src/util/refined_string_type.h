/********************************************************************\

Module: Type for string expressions used by the string solver.
        These string expressions contain a field `length`, of type
        `index_type`, a field `content` of type `content_type`.
        This module also defines functions to recognise the C and java
        string types.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Type for string expressions used by the string solver. These string
///   expressions contain a field `length`, of type `index_type`, a field
///   `content` of type `content_type`. This module also defines functions to
///   recognise the C and java string types.

#ifndef CPROVER_UTIL_REFINED_STRING_TYPE_H
#define CPROVER_UTIL_REFINED_STRING_TYPE_H

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>

// Internal type used for string refinement
class refined_string_typet: public array_typet
{
public:
  refined_string_typet(const typet &char_type, const exprt &length):
    array_typet(char_type, length)
  { }

  // Type for the content (list of characters) of a string
  const array_typet &get_content_type() const
  {
    return to_array_type(*this);
  }

  const typet &get_char_type() const
  {
    return get_content_type().subtype();
  }

  const typet &get_index_type() const
  {
    return size().type();
  }

  static bool is_refined_string_type(const typet &type);
};

extern inline const refined_string_typet &to_refined_string_type(
  const typet &type)
{
  PRECONDITION(refined_string_typet::is_refined_string_type(type));
  return static_cast<const refined_string_typet &>(type);
}

#endif
