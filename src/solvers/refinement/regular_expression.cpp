/*******************************************************************\

Module: Generates string constraints for regular expressions.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <iostream>
#include "regular_expression.h"

std::vector<std::pair<char, char>> charsett::parse(const std::string &s)
{
  std::vector<std::pair<char, char>> intervals;
  const std::size_t length = s.length();
  for(std::size_t i=0; i < length; ++i)
  {
    if(i+2 < length && s[i+1] == '-')
    {
      if(s[i] < s[i+2])
        intervals.emplace_back(s[i], s[i+2]);
      else
        intervals.emplace_back(s[i+2], s[i]);
      i = i + 2;
    }
    else
      intervals.emplace_back(s[i], s[i]);
  }
  return intervals;
}

/// Return an expression which is true when the expression is contained in the
/// charset
exprt charsett::contains(const exprt &char_expr) const
{
  std::vector<exprt> ops;
  for(const auto &pair : intervals)
  {
    const exprt min = from_integer(pair.first, char_expr.type());
    const exprt max = from_integer(pair.second, char_expr.type());
    ops.push_back(and_exprt(
      binary_relation_exprt(min, ID_le, char_expr),
      binary_relation_exprt(char_expr, ID_le, max)));
  }
  return disjunction(ops);
}

/// Compiles a flat pattern.
/// The only special characters are '[', '?', '*' and '+'.
/// '(', '|' and such are considered as the corresponding characters and don't
/// have a special meaning.
std::vector<atomic_patternt> flat_patternt::parse(const std::string &regex)
{
  std::vector<atomic_patternt> result;
  const std::size_t length = regex.length();
  for(std::size_t i = 0; i < length;) // `i` is incremented inside the loop
  {
    const std::size_t start_index = regex[i] == '[' ? i + 1 : i;
    std::size_t end_index = regex[i] == '[' ? regex.find(']', i) : i + 1;
    const charsett cs(regex.substr(start_index, end_index - start_index));
    // skip the closing square bracket
    if(regex[i] == '[')
      end_index += 1;

    quantifiert quant = quantifiert::ONCE;
    if(end_index < length)
    {
      if(regex[end_index] == '?')
      {
        quant = quantifiert::QUESTION_MARK;
        end_index += 1;
      }
      else if(regex[end_index] == '+')
      {
        quant = quantifiert::PLUS;
        end_index += 1;
      }
      else if(regex[end_index] == '*')
      {
        quant = quantifiert::STAR;
        end_index += 1;
      }
    }

    result.emplace_back(cs, quant);
    i = end_index;
  }
  return result;
}

/// \param usable_name: a name we can use as a prefix for symbols without
///        interfering without other symbols.
std::vector<exprt> flat_patternt::generate_constraints(
  const symbol_exprt &match_result,
  const refined_string_exprt &str,
  const std::string &usable_name) const
{
  std::vector<exprt> result;
  const typet length_type = str.length().type();
  symbol_exprt q_var(usable_name+"_QA", length_type);
  std::vector<symbol_exprt> delimiters;
  for(std::size_t i = 0; i < atoms.size(); ++i)
  {
    delimiters.emplace_back(
      usable_name + "_" + std::to_string(i), length_type);
  }

  for(std::size_t i = 0; i < atoms.size(); ++i)
  {
    const exprt lower_bound =
      i == 0
      ? static_cast<exprt>(from_integer(0, length_type))
      : delimiters[i-1];
    const plus_exprt lower_bound_plus_1(
      lower_bound, from_integer(1, lower_bound.type()));

    // forall q_var \in [d[i-1], d[i]]. str[i] \in charset
    result.push_back(string_constraintt(
      q_var,
      lower_bound,
      delimiters[i],
      match_result,
      atoms[i].charset.contains(str[q_var])));

    if(atoms[i].quantifier == quantifiert::ONCE)
      result.push_back(equal_exprt(delimiters[i], lower_bound_plus_1));
    else if(atoms[i].quantifier == quantifiert::PLUS)
      result.push_back(
        binary_relation_exprt(delimiters[i], ID_ge, lower_bound_plus_1));
    else
    {
      result.push_back(binary_relation_exprt(
        delimiters[i], ID_ge, lower_bound));
      if(atoms[i].quantifier == quantifiert::QUESTION_MARK)
        result.push_back(binary_relation_exprt(
          delimiters[i], ID_le, lower_bound_plus_1));
    }
  }
  return result;
}