/******************************************************************\

Module: String expressions for the string solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// String expressions for the string solver

#ifndef CPROVER_UTIL_STRING_EXPR_H
#define CPROVER_UTIL_STRING_EXPR_H

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/refined_string_type.h>

class string_exprt: public exprt
{
public:
  string_exprt(): exprt() {}

#if 0
  explicit string_exprt(array_typet type): exprt(type)
  { }
#endif

  string_exprt(const exprt &_content): exprt(_content)
  {
    type()=refined_string_typet(
          _content.type().subtype(), to_array_type(_content.type()).size());
  }

  // type is always an array
  const array_typet &type() const { return to_array_type(exprt::type()); }
  array_typet &type() { return to_array_type(exprt::type()); }

  // Expression corresponding to the length of the string
  const exprt &length() const { return type().size(); }
  exprt &length() { return type().size(); }

  // Expression corresponding to the content (array of characters) of the string
  const exprt &content() const { return op0(); }
  exprt &content() { return op0(); }

  static exprt within_bounds(const exprt &idx, const exprt &bound);

  // Expression of the character at position idx in the string
  index_exprt operator[] (const exprt &idx) const
  {
    return index_exprt(content(), idx);
  }

  index_exprt operator[] (int i) const
  {
    return index_exprt(content(), from_integer(i, length().type()));
  }

  // Comparison on the length of the strings
  binary_relation_exprt axiom_for_length_ge(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_ge, rhs.length());
  }

  binary_relation_exprt axiom_for_length_ge(
    const exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_ge, rhs);
  }

  binary_relation_exprt axiom_for_length_gt(
    const exprt &rhs) const
  {
    return binary_relation_exprt(rhs, ID_lt, length());
  }

  binary_relation_exprt axiom_for_length_gt(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(rhs.length(), ID_lt, length());
  }

  binary_relation_exprt axiom_for_length_gt(mp_integer i) const
  {
    return axiom_for_length_gt(from_integer(i, length().type()));
  }

  binary_relation_exprt axiom_for_length_le(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_le, rhs.length());
  }

  binary_relation_exprt axiom_for_length_le(
    const exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_le, rhs);
  }

  binary_relation_exprt axiom_for_length_le(mp_integer i) const
  {
    return axiom_for_length_le(from_integer(i, length().type()));
  }

  binary_relation_exprt axiom_for_length_lt(
    const string_exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_lt, rhs.length());
  }

  binary_relation_exprt axiom_for_length_lt(
    const exprt &rhs) const
  {
    return binary_relation_exprt(length(), ID_lt, rhs);
  }

  equal_exprt axiom_for_has_same_length_as(
    const string_exprt &rhs) const
  {
    return equal_exprt(length(), rhs.length());
  }

  equal_exprt axiom_for_has_length(const exprt &rhs) const
  {
    return equal_exprt(length(), rhs);
  }

  equal_exprt axiom_for_has_length(mp_integer i) const
  {
    return axiom_for_has_length(from_integer(i, length().type()));
  }

  friend inline string_exprt &to_string_expr(exprt &expr);
};

inline string_exprt &to_string_expr(exprt &expr)
{
  PRECONDITION(expr.type().id()==ID_array);
  PRECONDITION(expr.operands().size()==1);
  return static_cast<string_exprt &>(expr);
}

inline const string_exprt &to_string_expr(const exprt &expr)
{
  PRECONDITION(expr.type().id()==ID_array);
  PRECONDITION(expr.operands().size()==1);
  return static_cast<const string_exprt &>(expr);
}

#endif
