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
  const string_exprt &res,
  const string_exprt &s1,
  const string_exprt &s2,
  const exprt &offset)
{
  PRECONDITION(offset.type()==s1.length().type());
  string_exprt pref=add_axioms_for_substring(
    s1, from_integer(0, offset.type()), offset);
  string_exprt suf=add_axioms_for_substring(s1, offset, s1.length());
  string_exprt concat1=fresh_string(to_refined_string_type(s1.type()));
  exprt return_code1=add_axioms_for_concat(concat1, pref, s2);
  exprt return_code2=add_axioms_for_concat(res, concat1, suf);
  return if_exprt(
    equal_exprt(return_code1, from_integer(0, return_code1.type())),
    return_code2,
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
  string_exprt s1=get_string_expr(f.arguments()[2]);
  string_exprt s2=get_string_expr(f.arguments()[4]);
  // TODO: where is arguments[3] used?
  string_exprt res(f.arguments()[0], f.arguments()[1], s1.type());
  const exprt &offset=f.arguments()[1];
  if(f.arguments().size()==7)
  {
    const exprt &start=f.arguments()[5];
    const exprt &end=f.arguments()[6];
    string_exprt substring=add_axioms_for_substring(s2, start, end);
    return add_axioms_for_insert(res, s1, substring, offset);
  }
  else // 5 arguments
  {
    return add_axioms_for_insert(res, s1, s2, offset);
  }
}
