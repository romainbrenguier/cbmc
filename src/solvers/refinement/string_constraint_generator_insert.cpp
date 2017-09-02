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
  const char_array_exprt &res,
  const char_array_exprt &s1,
  const char_array_exprt &s2,
  const exprt &offset)
{
  PRECONDITION(offset.type()==s1.length().type());
  const typet &index_type=s1.length().type();
  const typet &char_type=s1.content().type().subtype();
  char_array_exprt pref=fresh_string(index_type, char_type);
  exprt return_code1=add_axioms_for_substring(
    pref, s1, from_integer(0, offset.type()), offset);
  char_array_exprt suf=fresh_string(index_type, char_type);
  exprt return_code2=add_axioms_for_substring(
    suf, s1, offset, s1.length());
  char_array_exprt concat1=fresh_string(index_type, char_type);
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
  char_array_exprt s1=get_string_expr(f.arguments()[2]);
  char_array_exprt s2=get_string_expr(f.arguments()[4]);
  // TODO: where is arguments[3] used?
  char_array_exprt res=char_array_of_string_expr(
    string_exprt(f.arguments()[0], f.arguments()[1], s1.type()));
  const exprt &offset=f.arguments()[1];
  if(f.arguments().size()==7)
  {
    const exprt &start=f.arguments()[5];
    const exprt &end=f.arguments()[6];
    const typet &char_type=s1.content().type().subtype();
    const typet &index_type=s1.length().type();
    char_array_exprt substring=fresh_string(index_type, char_type);
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
