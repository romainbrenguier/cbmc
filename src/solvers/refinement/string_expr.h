/******************************************************************\

Module: String expressions for the string solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_EXPR_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_EXPR_H

#include <langapi/language_ui.h>

#include <solvers/refinement/bv_refinement.h>
#include <solvers/refinement/refined_string_type.h>


// Expressions that encode strings
class string_exprt: public struct_exprt
{
public:
  // Initialize string from the type of characters
  explicit string_exprt(unsignedbv_typet char_type);

  // Default uses C character type
  string_exprt() : string_exprt(refined_string_typet::char_type()) {}

  // Generate a new symbol of the given type tp with a prefix
  static symbol_exprt fresh_symbol
  (const irep_idt &prefix, const typet &tp=bool_typet());

  // Expression corresponding to the length of the string
  inline const exprt & length() const
  { return op0(); }

  // Expression corresponding to the content (array of characters) of the string
  inline const exprt & content() const
  { return op1(); }

  static exprt within_bounds(const exprt & idx, const exprt & bound);

  // Expression of the character at position idx in the string
  inline index_exprt operator[] (const exprt & idx) const
  { return index_exprt(content(), idx);}
  inline index_exprt operator[] (int i) const
  { return index_exprt(content(), refined_string_typet::index_of_int(i));}

  // Comparison on the length of the strings
  inline binary_relation_exprt axiom_for_is_longer_than(const string_exprt & rhs) const
  { return binary_relation_exprt(length(), ID_ge, rhs.length()); }
  inline binary_relation_exprt axiom_for_is_longer_than(const exprt & rhs) const
  { return binary_relation_exprt(length(), ID_ge, rhs); }
  inline binary_relation_exprt axiom_for_is_strictly_longer_than(
    const exprt & rhs) const
  { return binary_relation_exprt(rhs, ID_lt, length()); }
  inline binary_relation_exprt axiom_for_is_strictly_longer_than(
    const string_exprt & rhs) const
  { return binary_relation_exprt(rhs.length(), ID_lt, length()); }
  inline binary_relation_exprt axiom_for_is_strictly_longer_than(int i) const
  { return axiom_for_is_strictly_longer_than(refined_string_typet::index_of_int(i)); }
  inline binary_relation_exprt axiom_for_is_shorter_than(
    const string_exprt & rhs) const
  { return binary_relation_exprt(length(), ID_le, rhs.length()); }
  inline binary_relation_exprt axiom_for_is_shorter_than(
    const exprt & rhs) const
  { return binary_relation_exprt(length(), ID_le, rhs); }
  inline binary_relation_exprt axiom_for_is_shorter_than(int i) const
  { return axiom_for_is_shorter_than(refined_string_typet::index_of_int(i)); }
  inline binary_relation_exprt axiom_for_is_strictly_shorter_than(
    const string_exprt & rhs) const
  { return binary_relation_exprt(length(), ID_lt, rhs.length()); }
  inline binary_relation_exprt axiom_for_is_strictly_shorter_than(
    const exprt & rhs) const
  { return binary_relation_exprt(length(), ID_lt, rhs); }
  inline equal_exprt axiom_for_has_same_length_as(const string_exprt & rhs) const
  { return equal_exprt(length(), rhs.length()); }
  inline equal_exprt axiom_for_has_length(const exprt & rhs) const
  { return equal_exprt(length(), rhs); }
  inline equal_exprt axiom_for_has_length(int i) const
  { return axiom_for_has_length(refined_string_typet::index_of_int(i)); }

  static irep_idt extract_java_string(const symbol_exprt & s);

  static unsigned next_symbol_id;

  friend inline string_exprt &to_string_expr(exprt &expr);
};


inline string_exprt &to_string_expr(exprt &expr)
{
  assert(expr.id()==ID_struct);
  return static_cast<string_exprt &>(expr);
}


#endif
