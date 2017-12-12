/*******************************************************************\

Module: Generates string constraints for regular expressions.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_REGULAR_EXPRESSION_H
#define CPROVER_SOLVERS_REFINEMENT_REGULAR_EXPRESSION_H

#include <string>
#include <vector>
#include "string_constraint.h"

class charsett
{
public:
  explicit charsett(const std::string &s) : intervals(parse(s)) { };
  explicit charsett(const char c) : charsett(std::string(c, 1)) { };

  exprt contains(const exprt &char_expr) const;

private:
  // The charset is represented by a list of intervals.
  // We use mp_integer because char may not be limited to 8 bits.
  const std::vector<std::pair<char, char>> intervals;

  static std::vector<std::pair<char, char>> parse(const std::string &str);
};

enum class quantifiert { QUESTION_MARK, STAR, PLUS, ONCE};

/// What we call atomic patternt are regular expressions of the form
/// [charset]* or [charset]+ or [charset]? or [charset]
class atomic_patternt
{
public:
  atomic_patternt(charsett charset, quantifiert quantifier=quantifiert::ONCE)
    :charset(charset), quantifier(quantifier)
  { };

  const charsett charset;
  const quantifiert quantifier;
};

/// Regular expression with no nested quantifiers.
/// For instance (a b)* is flat but (a* b)* is not.
class flat_patternt
{
public:
  explicit flat_patternt(const std::string &regex): atoms(parse(regex))
  { };

  std::vector<exprt> generate_constraints(
    const symbol_exprt &match_result,
    const refined_string_exprt &str,
    const std::string &usable_name) const;

private:
  static std::vector<atomic_patternt> parse(const std::string &regex);
  const std::vector<atomic_patternt> atoms;
};

#endif // CPROVER_SOLVERS_REFINEMENT_REGULAR_EXPRESSION_H
