/// Module: String solver
/// Author: Romain Brenguier

#include <util/range.h>
#include "format_specifier.h"
#include "string_format_builtin_function.h"

string_format_builtin_functiont::string_format_builtin_functiont(
  const exprt &return_code,
  const std::vector<exprt> &fun_args,
  array_poolt &array_pool)
  : string_builtin_functiont(return_code)
{
  PRECONDITION(fun_args.size() >= 3);
  result = array_pool.find(fun_args[1], fun_args[0]);
  const array_string_exprt format_string_expr =
    get_string_expr(array_pool, fun_args[2]);

  // List of arguments after the format string
  inputs = make_range(fun_args.begin() + 3, fun_args.end()).map(
    [&](const exprt &arg){
      INVARIANT(
        is_refined_string_type(arg.type()),
        "arguments of format should be strings");
      return get_string_expr(array_pool, arg);
    }).collect<std::vector<array_string_exprt>>();

  // format_string is only initialized if the expression is constant
  if(format_string_expr.length().id() == ID_constant &&
     format_string_expr.content().id() == ID_array)
  {
    const auto length = numeric_cast_v<std::size_t>(
      to_constant_expr(format_string_expr.length()));
    format_string = utf16_constant_array_to_java(
      to_array_expr(format_string_expr.content()), length);
  }
}

std::vector<mp_integer> eval_format_arg_from_string(
  std::vector<mp_integer> string, const irep_idt &id)
{
  if(id == "string_expr")
    return string;
  if(id == ID_int || id == ID_float)
    UNIMPLEMENTED;
  //  return {string[0] << 48 | string[1] << 32 | string[2] << 16 | string[3]};
  if(id == ID_char)
    return string;
  if(id == ID_boolean)
    return { string[0] != 'n' };
  UNHANDLED_CASE;
}

bool eval_is_null(const std::vector<mp_integer> &string)
{
  return string.size() == 4 && string[0] == 'n' && string[1] == 'u'
         && string[2] == 'l' && string[3] == 'l';
}

static std::vector<mp_integer> eval_format_specifier(
  const format_specifiert &fs,
  const std::vector<mp_integer> &arg,
  const typet &index_type)
{
  switch(fs.conversion)
  {
    case format_specifiert::DECIMAL_INTEGER:
      UNIMPLEMENTED;
    case format_specifiert::HEXADECIMAL_INTEGER:
      UNIMPLEMENTED;
    case format_specifiert::SCIENTIFIC:
      UNIMPLEMENTED;
    case format_specifiert::DECIMAL_FLOAT:
      UNIMPLEMENTED;
    case format_specifiert::CHARACTER:
    {
      std::vector<mp_integer> arg_string = eval_format_arg_from_string(arg, ID_char);
      // In the case the arg is null, the result will be equal to "null" and
      // and otherwise we just take the 4th character of the string.
      if(eval_is_null(arg_string))
        return std::vector<mp_integer>{'n', 'u', 'l', 'l'};
      return arg_string;
    }
    case format_specifiert::BOOLEAN:
    {
      if(eval_format_arg_from_string(arg, ID_boolean)[0] > 0)
        return std::vector<mp_integer>{'t', 'r', 'u', 'e'};
      return std::vector<mp_integer>{'f', 'a', 'l', 's', 'e'};
    }
    case format_specifiert::STRING:
      return eval_format_arg_from_string(arg, "string_expr");
    case format_specifiert::HASHCODE:
      UNIMPLEMENTED;
    case format_specifiert::LINE_SEPARATOR:
      // TODO: the constant should depend on the system: System.lineSeparator()
      return std::vector<mp_integer>{'\n'};
    case format_specifiert::PERCENT_SIGN:
      return std::vector<mp_integer>{'%'};
    case format_specifiert::SCIENTIFIC_UPPER:
    case format_specifiert::GENERAL_UPPER:
    case format_specifiert::HEXADECIMAL_FLOAT_UPPER:
    case format_specifiert::CHARACTER_UPPER:
    case format_specifiert::DATE_TIME_UPPER:
    case format_specifiert::BOOLEAN_UPPER:
    case format_specifiert::STRING_UPPER:
    case format_specifiert::HASHCODE_UPPER:
    {
      format_specifiert fs_lower = fs;
      fs_lower.conversion = tolower(fs.conversion);
      auto lower_case = eval_format_specifier(fs_lower, arg, index_type);
      return make_range(lower_case).map([](const mp_integer &c){
        // TODO: incomplete
        if ('a' <= c && c <= 'z')
          return c + 0x20;
        return c;
      });
    }
    case format_specifiert::OCTAL_INTEGER:
      /// \todo Conversion of octal is not implemented.
    case format_specifiert::GENERAL:
      /// \todo Conversion for format specifier general is not implemented.
    case format_specifiert::HEXADECIMAL_FLOAT:
      /// \todo Conversion of hexadecimal float is not implemented.
    case format_specifiert::DATE_TIME:
      /// \todo Conversion of date-time is not implemented
      // For all these unimplemented cases we return a non-deterministic string
      UNIMPLEMENTED;
  }

  INVARIANT(false, "format specifier must belong to [bBhHsScCdoxXeEfgGaAtT%n]");
}

optionalt<exprt> string_format_builtin_functiont::eval(
  const std::function<exprt(const exprt &)> &get_value) const
{
  if(!format_string.has_value())
    return {};

  // TODO: factor the part that is common with other constraints
  const std::vector<format_elementt> format_strings =
    parse_format_string(format_string.value());
  std::vector<mp_integer> result_vector;
  std::size_t arg_count = 0;

  for(const format_elementt &fe : format_strings)
  {
    if(fe.is_format_specifier())
    {
      const format_specifiert &fs = fe.get_format_specifier();
      if(
        fs.conversion != format_specifiert::PERCENT_SIGN &&
        fs.conversion != format_specifiert::LINE_SEPARATOR)
      {

        if(fs.index == -1)
        {
          INVARIANT(
            arg_count < inputs.size(), "number of format must match specifiers");
          if(auto arg_value = eval_string(inputs[arg_count++], get_value))
          {
            std::move(
              arg_value->begin(),
              arg_value->end(),
              std::back_inserter(result_vector));
          }
          else
            return {};
        }
        else
        {
          INVARIANT(fs.index > 0, "index in format should be positive");
          INVARIANT(
            static_cast<std::size_t>(fs.index) <= inputs.size(),
            "number of format must match specifiers");

          // first argument `args[0]` corresponds to index 1
          if(auto arg_value = eval_string(inputs[fs.index - 1], get_value))
          {
            std::move(
              arg_value->begin(),
              arg_value->end(),
              std::back_inserter(result_vector));
          }
          else
            return {};
        }
      }

    }
    else
    {
      for(char c : fe.get_format_text().get_content())
        result_vector.emplace_back(c);
    }
  }
  return make_string(result_vector, to_array_type(result.type()));
}

string_constraintst string_format_builtin_functiont::constraints(
  string_constraint_generatort &generator) const
{
  // When `format_string` was not set, leave the result non-deterministic
  if(!format_string.has_value())
    return {};

  null_message_handlert message_handler;
  auto result_constraint_pair = add_axioms_for_format(
    generator.fresh_symbol,
    result,
    format_string.value(),
    // TODO: fix the type of this argument
    make_range(inputs).collect<std::vector<exprt>>(),
    generator.array_pool,
    // TODO: get rid of this argument
    messaget{message_handler},
    generator.ns);
  // TODO: change interface of add_axioms_for_format to return only
  // TODO: string_constraints
  result_constraint_pair.second.existential.push_back(
    std::move(result_constraint_pair.first));
  return result_constraint_pair.second;
}

static exprt length_for_format_specifier(
  const format_specifiert &fs,
  const array_string_exprt &arg,
  const typet &index_type)
{
  switch(fs.conversion)
  {
    case format_specifiert::DECIMAL_INTEGER:
      UNIMPLEMENTED;
    case format_specifiert::HEXADECIMAL_INTEGER:
      UNIMPLEMENTED;
    case format_specifiert::SCIENTIFIC:
      UNIMPLEMENTED;
    case format_specifiert::DECIMAL_FLOAT:
      UNIMPLEMENTED;
    case format_specifiert::CHARACTER:
    {
      exprt arg_string = format_arg_from_string(arg, ID_char);
      array_string_exprt &string_expr = to_array_string_expr(arg_string);
      // In the case the arg is null, the result will be equal to "null" and
      // and otherwise we just take the 4th character of the string.
      return if_exprt{
        is_null(string_expr),
        from_integer(4, index_type),
        from_integer(1, index_type)};
    }
    case format_specifiert::BOOLEAN:
    {
      return if_exprt{
        format_arg_from_string(arg, ID_boolean),
        from_integer(4, index_type),
        from_integer(5, index_type)};
    }
    case format_specifiert::STRING:
    {
      const exprt arg_string = format_arg_from_string(arg, "string_expr");
      const array_string_exprt string_expr = to_array_string_expr(arg_string);
      return string_expr.length();
    }
    case format_specifiert::HASHCODE:
      UNIMPLEMENTED;
    case format_specifiert::LINE_SEPARATOR:
      // TODO: the constant should depend on the system: System.lineSeparator()
      return from_integer(1, index_type);
    case format_specifiert::PERCENT_SIGN:
      return from_integer(1, index_type);
    case format_specifiert::SCIENTIFIC_UPPER:
    case format_specifiert::GENERAL_UPPER:
    case format_specifiert::HEXADECIMAL_FLOAT_UPPER:
    case format_specifiert::CHARACTER_UPPER:
    case format_specifiert::DATE_TIME_UPPER:
    case format_specifiert::BOOLEAN_UPPER:
    case format_specifiert::STRING_UPPER:
    case format_specifiert::HASHCODE_UPPER:
    {
      format_specifiert fs_lower = fs;
      fs_lower.conversion = tolower(fs.conversion);
      return length_for_format_specifier(fs_lower, arg, index_type);
    }
    case format_specifiert::OCTAL_INTEGER:
      /// \todo Conversion of octal is not implemented.
    case format_specifiert::GENERAL:
      /// \todo Conversion for format specifier general is not implemented.
    case format_specifiert::HEXADECIMAL_FLOAT:
      /// \todo Conversion of hexadecimal float is not implemented.
    case format_specifiert::DATE_TIME:
      /// \todo Conversion of date-time is not implemented
      // For all these unimplemented cases we return a non-deterministic string
      UNIMPLEMENTED;
  }

  INVARIANT(false, "format specifier must belong to [bBhHsScCdoxXeEfgGaAtT%n]");
}

exprt string_format_builtin_functiont::length_constraint() const
{
  if(!format_string.has_value())
    return true_exprt{};

  // TODO: factor the part that is common with other constraints
  exprt::operandst constraints;
  const std::vector<format_elementt> format_strings =
    parse_format_string(format_string.value());
  std::vector<exprt> intermediary_string_lengths;
  std::size_t arg_count = 0;
  const typet &index_type = result.length().type();

  for(const format_elementt &fe : format_strings)
  {
    if(fe.is_format_specifier())
    {
      const format_specifiert &fs = fe.get_format_specifier();
      array_string_exprt arg;
      if(
        fs.conversion != format_specifiert::PERCENT_SIGN &&
        fs.conversion != format_specifiert::LINE_SEPARATOR)
      {

        if(fs.index == -1)
        {
          INVARIANT(
            arg_count < inputs.size(), "number of format must match specifiers");
          arg = inputs[arg_count++];
        }
        else
        {
          INVARIANT(fs.index > 0, "index in format should be positive");
          INVARIANT(
            static_cast<std::size_t>(fs.index) <= inputs.size(),
            "number of format must match specifiers");

          // first argument `args[0]` corresponds to index 1
          arg = inputs[fs.index - 1];
        }
      }

      intermediary_string_lengths.push_back(
        length_for_format_specifier(fs, arg, index_type));
    }
    else
    {
      intermediary_string_lengths.push_back(
        from_integer(
          fe.get_format_text().get_content().size(), result.length().type()));
    }
  }

  constraints.push_back(
    equal_exprt{return_code, from_integer(0, get_return_code_type())});

  if(intermediary_string_lengths.empty())
  {
    constraints.push_back(
      equal_exprt(result.length(), from_integer(0, index_type)));
    return conjunction(constraints);
  }

  exprt total_length = intermediary_string_lengths[0];
  for(std::size_t i = 1; i < intermediary_string_lengths.size(); ++i)
  {
    total_length =
      plus_exprt{std::move(total_length), intermediary_string_lengths[i]};
  }
  constraints.push_back(equal_exprt{result.length(), std::move(total_length)});
  return conjunction(constraints);
}