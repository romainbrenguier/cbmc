/// Module: String solver
/// Author: Romain Brenguier

#ifndef CPROVER_SOLVERS_STRINGS_STRING_FORMAT_BUILTIN_FUNCTION_H
#define CPROVER_SOLVERS_STRINGS_STRING_FORMAT_BUILTIN_FUNCTION_H

#include "string_builtin_function.h"

class string_format_builtin_functiont final
  : public string_builtin_functiont
{
public:
  array_string_exprt result;
  /// Only set when the format string is a constant. In the other case, the
  /// result will be non-deterministic
  optionalt<std::string> format_string;
  std::vector<array_string_exprt> inputs;

  /// Constructor from arguments of a function application.
  /// The arguments in `fun_args` should be in order:
  /// an integer `result.length`, a character pointer `&result[0]`,
  /// a string of type refined_string_typet for the format string,
  /// any number of strings of type refined_string_typet.
  string_format_builtin_functiont(
    const exprt &return_code,
    const std::vector<exprt> &fun_args,
    array_poolt &array_pool);

  optionalt<array_string_exprt> string_result() const override
  {
    return result;
  }

  std::vector<array_string_exprt> string_arguments() const override
  {
    return inputs;
  }

  optionalt<exprt>
  eval(const std::function<exprt(const exprt &)> &get_value) const override;

  std::string name() const override
  {
    return "format";
  }

  string_constraintst
  constraints(string_constraint_generatort &generator) const override;

  exprt length_constraint() const override;

  bool maybe_testing_function() const override
  {
    return false;
  }
};

#endif // CPROVER_SOLVERS_STRINGS_STRING_FORMAT_BUILTIN_FUNCTION_H
