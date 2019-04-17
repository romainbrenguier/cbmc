/*******************************************************************\

Module: String solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include "array_pool.h"

symbol_exprt symbol_generatort::
operator()(const irep_idt &prefix, const typet &type)
{
  std::ostringstream buf;
  buf << "string_refinement#" << prefix << "#" << ++symbol_count;
  irep_idt name(buf.str());
  symbol_exprt result(name, type);
#ifdef DEBUG
  created_symbols.push_back(result);
#endif
  return result;
}

exprt array_poolt::get_length(const array_string_exprt &s) const
{
  if(s.length() == infinity_exprt(s.length().type()))
  {
    auto it = length_of_array.find(s);
    if(it != length_of_array.end())
      return it->second;
  }
  return s.length();
}

array_string_exprt
array_poolt::fresh_string(const typet &index_type, const typet &char_type)
{
  symbol_exprt length = fresh_symbol("string_length", index_type);
  array_typet array_type(char_type, length);
  symbol_exprt content = fresh_symbol("string_content", array_type);
  array_string_exprt str = to_array_string_expr(content);
  created_strings_value.insert(str);
  return str;
}

/// Helper function for \ref find.
/// Make a new char array for a char pointer. The size of the char array is a
/// variable with no constraint.
array_string_exprt array_poolt::make_char_array_for_char_pointer(
  const exprt &char_pointer,
  const typet &char_array_type)
{
  PRECONDITION(char_pointer.type().id() == ID_pointer);
  PRECONDITION(char_array_type.id() == ID_array);
  PRECONDITION(
    char_array_type.subtype().id() == ID_unsignedbv ||
    char_array_type.subtype().id() == ID_signedbv);

  if(char_pointer.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(char_pointer);
    const array_string_exprt t =
      make_char_array_for_char_pointer(if_expr.true_case(), char_array_type);
    const array_string_exprt f =
      make_char_array_for_char_pointer(if_expr.false_case(), char_array_type);
    const array_typet array_type(
      char_array_type.subtype(),
      if_exprt(
        if_expr.cond(),
        to_array_type(t.type()).size(),
        to_array_type(f.type()).size()));
    // BEWARE: this expression is possibly type-inconsistent and must not be
    // used for any purposes other than passing it to concretisation
    return to_array_string_expr(if_exprt(if_expr.cond(), t, f, array_type));
  }
  const bool is_constant_array =
    char_pointer.id() == ID_address_of &&
    (to_address_of_expr(char_pointer).object().id() == ID_index) &&
    char_pointer.op0().op0().id() == ID_array;
  if(is_constant_array)
  {
    return to_array_string_expr(
      to_index_expr(to_address_of_expr(char_pointer).object()).array());
  }
  const std::string symbol_name = "char_array_" + id2string(char_pointer.id());
  const auto array_sym =
    to_array_string_expr(fresh_symbol(symbol_name, char_array_type));
  const auto insert_result =
    arrays_of_pointers.insert({char_pointer, array_sym});
  return to_array_string_expr(insert_result.first->second);
}

void array_poolt::insert(
  const exprt &pointer_expr,
  array_string_exprt &array_expr)
{
  const exprt &length = array_expr.length();
  if(length == infinity_exprt(length.type()))
  {
    auto pair = length_of_array.insert(
      std::make_pair(array_expr, fresh_symbol("string_length", length.type())));
    array_expr.length() = pair.first->second;
  }

  const auto it_bool =
    arrays_of_pointers.insert(std::make_pair(pointer_expr, array_expr));
  created_strings_value.insert(array_expr);
  INVARIANT(
    it_bool.second, "should not associate two arrays to the same pointer");
}

const std::set<array_string_exprt> &array_poolt::created_strings() const
{
  return created_strings_value;
}

const array_string_exprt &
array_poolt::find(const exprt &pointer, const exprt &length)
{
  const array_typet array_type(pointer.type().subtype(), length);
  const array_string_exprt array =
    make_char_array_for_char_pointer(pointer, array_type);
  return *created_strings_value.insert(array).first;
}

array_string_exprt of_argument(array_poolt &array_pool, const exprt &arg)
{
  const auto string_argument = expr_checked_cast<struct_exprt>(arg);
  return array_pool.find(string_argument.op1(), string_argument.op0());
}

array_string_exprt get_string_expr(array_poolt &pool, const exprt &expr)
{
  PRECONDITION(is_refined_string_type(expr.type()));
  const refined_string_exprt &str = to_string_expr(expr);
  return pool.find(str.content(), str.length());
}
