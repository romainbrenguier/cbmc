/******************************************************************\

Module: String expressions for the string solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// String expressions for the string solver

#ifndef CPROVER_UTIL_STRING_EXPR_H
#define CPROVER_UTIL_STRING_EXPR_H

#include "arith_tools.h"
#include "refined_string_type.h"
#include "std_expr.h"

/// Wrapper for expressions which have a fixed type
template<typename T_typet, typename T_exprt=exprt>
struct expr_with_typet
{
  T_exprt expr;
  T_typet &type;

  explicit expr_with_typet(T_exprt e)
    : expr(std::move(e)),
      type(type_checked_cast<T_typet>(expr.type()))
  {
  }
};

// Comparison on the length of the strings
template <typename T>
inline binary_relation_exprt length_ge(
  const T &lhs, const exprt &rhs)
{
  PRECONDITION(rhs.type() == lhs.length().type());
  return binary_relation_exprt(lhs.length(), ID_ge, rhs);
}

template <typename T>
inline binary_relation_exprt length_gt(
  const T &lhs, const exprt &rhs)
{
  PRECONDITION(rhs.type() == lhs.length().type());
  return binary_relation_exprt(rhs, ID_lt, lhs.length());
}

template <typename T>
inline binary_relation_exprt length_gt(
  const T &lhs, mp_integer i)
{
  return length_gt(lhs, from_integer(i, lhs.length().type()));
}

template <typename T>
inline binary_relation_exprt length_le(
  const T &lhs, const exprt &rhs)
{
  PRECONDITION(rhs.type() == lhs.length().type());
  return binary_relation_exprt(lhs.length(), ID_le, rhs);
}

template <typename T>
inline binary_relation_exprt length_le(
  const T &lhs, mp_integer i)
{
  return length_le(lhs, from_integer(i, lhs.length().type()));
}

template <typename T>
inline equal_exprt length_eq(
  const T &lhs, const exprt &rhs)
{
  PRECONDITION(rhs.type() == lhs.length().type());
  return equal_exprt(lhs.length(), rhs);
}

template <typename T>
inline equal_exprt length_eq(const T &lhs, mp_integer i)
{
  return length_eq(lhs, from_integer(i, lhs.length().type()));
}

// Representation of strings as arrays
class array_string_exprt : public expr_with_typet<array_typet>
{
  array_string_exprt();
public:
  array_string_exprt(exprt e)
    : expr_with_typet<array_typet>(std::move(e))
  {
  }

  exprt &length()
  {
    return type.size();
  }

  const exprt &length() const
  {
    return type.size();
  }

  exprt &content()
  {
    return expr;
  }

  const exprt &content() const
  {
    return expr;
  }

  exprt operator[](const exprt &i) const
  {
    return index_exprt(content(), i);
  }

  index_exprt operator[](int i) const
  {
    return index_exprt(content(), from_integer(i, length().type()));
  }
};

// Represent strings as a struct with a length field and a content field
class refined_string_exprt : public struct_exprt
{
public:
  refined_string_exprt() : struct_exprt()
  {
  }

  refined_string_exprt(
    const exprt &_length,
    const exprt &_content,
    const typet &type)
    : struct_exprt(type)
  {
    copy_to_operands(_length, _content);
  }

  refined_string_exprt(const exprt &_length, const exprt &_content)
    : refined_string_exprt(
        _length,
        _content,
        refined_string_typet(_length.type(), to_pointer_type(_content.type())))
  {
  }

  // Expression corresponding to the length of the string
  const exprt &length() const
  {
    return op0();
  }
  exprt &length()
  {
    return op0();
  }

  // Expression corresponding to the content (array of characters) of the string
  const exprt &content() const
  {
    return op1();
  }
  exprt &content()
  {
    return op1();
  }

  friend inline refined_string_exprt &to_string_expr(exprt &expr);
};

inline refined_string_exprt &to_string_expr(exprt &expr)
{
  PRECONDITION(expr.id()==ID_struct);
  PRECONDITION(expr.operands().size()==2);
  return static_cast<refined_string_exprt &>(expr);
}

inline const refined_string_exprt &to_string_expr(const exprt &expr)
{
  PRECONDITION(expr.id()==ID_struct);
  PRECONDITION(expr.operands().size()==2);
  return static_cast<const refined_string_exprt &>(expr);
}

template <>
inline bool can_cast_expr<refined_string_exprt>(const exprt &base)
{
  return base.id() == ID_struct && base.operands().size() == 2;
}

inline void validate_expr(const refined_string_exprt &x)
{
  INVARIANT(x.id() == ID_struct, "refined string exprs are struct");
  validate_operands(x, 2, "refined string expr has length and content fields");
  INVARIANT(x.length().type().id() == ID_signedbv, "length is a signed int");
  INVARIANT(x.content().type().id() == ID_array, "content is an array");
}

#endif
