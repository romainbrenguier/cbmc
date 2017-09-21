/*******************************************************************\

Module: Generates string constraints for the family of insert Java functions

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for the family of insert Java functions

#include <solvers/refinement/string_refinement_invariant.h>
#include <solvers/refinement/string_constraint_generator.h>

/// add axioms stating that the result correspond to the first string where we
/// inserted the second one at position offset
/// \par parameters: two string expression and an integer offset
/// \return an expression whose value would be different from zero if there is
///   an exception to signal
exprt string_constraint_generatort::add_axioms_for_insert(
  const array_string_exprt &res,
  const array_string_exprt &s1,
  const array_string_exprt &s2,
  const exprt &offset)
{
  PRECONDITION(offset.type()==s1.length().type());
  const typet &index_type=s1.length().type();
  const typet &char_type=s1.content().type().subtype();
  array_string_exprt pref=fresh_string(index_type, char_type);
  exprt return_code1=add_axioms_for_substring(
    pref, s1, from_integer(0, offset.type()), offset);
  array_string_exprt suf=fresh_string(index_type, char_type);
  exprt return_code2=add_axioms_for_substring(
    suf, s1, offset, s1.length());
  array_string_exprt concat1=fresh_string(index_type, char_type);
  exprt return_code3=add_axioms_for_concat(concat1, pref, s2);
  exprt return_code4=add_axioms_for_concat(res, concat1, suf);
  return if_exprt(
    equal_exprt(return_code1, from_integer(0, return_code1.type())),
    if_exprt(equal_exprt(return_code2, from_integer(0, return_code1.type())),
      if_exprt(equal_exprt(return_code3, from_integer(0, return_code1.type())),
               return_code4,
               return_code3),
             return_code2),
    return_code1);
}

/// add axioms corresponding to the StringBuilder.insert(int, CharSequence) and
/// StringBuilder.insert(int, CharSequence, int, int) java functions
/// \par parameters: function application with three arguments: two strings and
///   an index
/// \return a new string expression
exprt string_constraint_generatort::add_axioms_for_insert(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()==5 || f.arguments().size()==7);
  array_string_exprt s1=get_string_expr(f.arguments()[2]);
  array_string_exprt s2=get_string_expr(f.arguments()[4]);
  // TODO: where is arguments[3] used?
  array_string_exprt res=
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const exprt &offset=f.arguments()[3];
  if(f.arguments().size()==7)
  {
    const exprt &start=f.arguments()[5];
    const exprt &end=f.arguments()[6];
    const typet &char_type=s1.content().type().subtype();
    const typet &index_type=s1.length().type();
    array_string_exprt substring=fresh_string(index_type, char_type);
    exprt return_code1=add_axioms_for_substring(substring, s2, start, end);
    exprt return_code2=add_axioms_for_insert(res, s1, substring, offset);
    return
      if_exprt(equal_exprt(return_code1, from_integer(0, return_code1.type())),
               return_code2,
               return_code1);
  }
  else // 5 arguments
  {
    return add_axioms_for_insert(res, s1, s2, offset);
  }
}
/// add axioms corresponding to the StringBuilder.insert(I) java function
/// \param f: function application with three arguments: a string, an
///   integer offset, and an integer
/// \return an expression
exprt string_constraint_generatort::add_axioms_for_insert_int(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()==5);
  const array_string_exprt s1=get_string_expr(f.arguments()[2]);
  const array_string_exprt res=
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const exprt &offset=f.arguments()[3];
  const typet &index_type=s1.length().type();
  const typet &char_type=s1.content().type().subtype();
  array_string_exprt s2=fresh_string(index_type, char_type);
  exprt return_code=add_axioms_from_int(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}

/// add axioms corresponding to the StringBuilder.insert(J) java function
/// \param f: function application with three arguments: a string, an
///   integer offset and a long
/// \return an expression
exprt string_constraint_generatort::add_axioms_for_insert_long(
  const function_application_exprt &f)
{
  return add_axioms_for_insert_int(f);
}


/// add axioms corresponding to the StringBuilder.insert(Z) java function
/// \param f: function application with three arguments: a string, an
///   integer offset, and a Boolean
/// \return a new string expression
exprt string_constraint_generatort::add_axioms_for_insert_bool(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()==5);
  const array_string_exprt s1=get_string_expr(f.arguments()[0]);
  const array_string_exprt res=
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const exprt &offset=f.arguments()[3];
  const typet &index_type=s1.length().type();
  const typet &char_type=s1.content().type().subtype();
  array_string_exprt s2=fresh_string(index_type, char_type);
  exprt return_code=add_axioms_from_bool(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}

/// add axioms corresponding to the StringBuilder.insert(C) java function
/// \param f: function application with three arguments: a string, an
///   integer offset, and a character
/// \return an expression
exprt string_constraint_generatort::add_axioms_for_insert_char(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()==5);
  const array_string_exprt res=
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1=get_string_expr(f.arguments()[2]);
  const exprt &offset=f.arguments()[3];
  const typet &index_type=s1.length().type();
  const typet &char_type=s1.content().type().subtype();
  array_string_exprt s2=fresh_string(index_type, char_type);
  exprt return_code=add_axioms_from_char(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}

/// add axioms corresponding to the StringBuilder.insert(D) java function
/// \param f: function application with three arguments: a string, an
///   integer offset, and a double
/// \return a string expression
exprt string_constraint_generatort::add_axioms_for_insert_double(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()==5);
  const array_string_exprt res=
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1=get_string_expr(f.arguments()[2]);
  const exprt &offset=f.arguments()[3];
  const typet &index_type=s1.length().type();
  const typet &char_type=s1.content().type().subtype();
  const array_string_exprt s2=fresh_string(index_type, char_type);
  const exprt return_code=add_axioms_for_string_of_float(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}

/// add axioms corresponding to the StringBuilder.insert(F) java function
/// \param f: function application with three arguments: a string, an
///   integer offset, and a float
/// \return a new string expression
exprt string_constraint_generatort::add_axioms_for_insert_float(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()==5);
  const array_string_exprt res=
    char_array_of_pointer(f.arguments()[1], f.arguments()[0]);
  const array_string_exprt s1=get_string_expr(f.arguments()[2]);
  const exprt &offset=f.arguments()[3];
  const typet &index_type=s1.length().type();
  const typet &char_type=s1.content().type().subtype();
  const array_string_exprt s2=fresh_string(index_type, char_type);
  const exprt return_code=add_axioms_for_string_of_float(s2, f.arguments()[4]);
  return add_axioms_for_insert(res, s1, s2, offset);
}
