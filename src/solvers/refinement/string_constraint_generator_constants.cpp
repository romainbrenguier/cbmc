/*******************************************************************\

Module: Generates string constraints for constant strings

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Generates string constraints for constant strings

#include <solvers/refinement/string_constraint_generator.h>

#include <ansi-c/string_constant.h>
#include <util/prefix.h>
#include <util/unicode.h>

/// add axioms saying the returned string expression should be equal to the
/// string constant
/// \par parameters: a string constant
/// \return a string expression
exprt string_constraint_generatort::add_axioms_for_constant(
  const array_string_exprt &res, irep_idt sval)
{
  const typet &index_type=res.length().type();
  const typet &char_type=res.content().type().subtype();
  std::string c_str=id2string(sval);
  std::wstring str;

  // TODO: we should have a special treatment for java strings when the
  // conversion function is available:
#if 0
  if(mode==ID_java)
    str=utf8_to_utf16_little_endian(c_str);
  else
#endif
    str=widen(c_str);

  for(std::size_t i=0; i<str.size(); i++)
  {
    const exprt idx=from_integer(i, index_type);
    const exprt c=from_integer(str[i], char_type);
    const equal_exprt lemma(res[idx], c);
    m_axioms.push_back(lemma);
  }

  const exprt s_length=from_integer(str.size(), index_type);

  m_axioms.push_back(res.axiom_for_has_length(s_length));
  return from_integer(0, signedbv_typet(32));
}

/// add axioms to say that the returned string expression is empty
/// \par parameters: function application without argument
/// \return string expression
exprt string_constraint_generatort::add_axioms_for_empty_string(
  const function_application_exprt &f)
{
  PRECONDITION(f.arguments().size()==2);
  exprt length=f.arguments()[0];
  m_axioms.push_back(equal_exprt(length, from_integer(0, length.type())));
  return from_integer(0, length.type());
}

/// add axioms to say that the returned string expression is equal to the string
/// literal
/// \param f: function application with an argument which is a string literal
/// that is a constant with a string value.
/// \return string expression
exprt string_constraint_generatort::add_axioms_from_literal(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  PRECONDITION(args.size()==3); // Bad args to string literal?
  const array_string_exprt res=char_array_of_pointer(args[1], args[0]);
  const exprt &arg=args[2];
  irep_idt sval=to_constant_expr(arg).get_value();
  return add_axioms_for_constant(res, sval);
}
