/*******************************************************************\

Module: Produce code for simple implementation of String Java libraries

Author: Romain Brenguier

Date:  April 2017

\*******************************************************************/

#include <util/std_expr.h>
#include <util/ieee_float.h>
#include "java_types.h"

#include "java_string_library_preprocess.h"

/*******************************************************************\

Function: get_exponent

  Inputs:
    src - a floating point expression
    spec - specification for floating points

 Outputs:
    a java integer representing the exponent

 Purpose: Gets the unbiased exponent in a floating-point bit-vector

\*******************************************************************/

exprt get_exponent(
  const exprt &src,
  const ieee_float_spect &spec)
{
  exprt exp_bits=extractbits_exprt(
    src, spec.f+spec.e-1, spec.f,
    unsignedbv_typet(spec.e));
  // exponent is in biased from (numbers form -128 to 127 are encoded with
  // integer from 0 to 255) we have to remove the bias.
  return minus_exprt(typecast_exprt(exp_bits, java_int_type()),
                     from_integer(spec.bias(), java_int_type()));
}

/*******************************************************************\

Function: get_magnitude

  Inputs:
    src - a floating point expression
    spec - specification for floating points

 Outputs:

 Purpose: Gets the magnitude without hidden bit

\*******************************************************************/

exprt get_magnitude(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return extractbits_exprt(
    src, spec.f-1, 0,
    unsignedbv_typet(spec.f));
}

/*******************************************************************\

Function: get_significand

  Inputs:
    src - a floating point expression
    spec - specification for floating points

 Outputs:

 Purpose: Gets the significand as a java integer, looking for the hidden bit

\*******************************************************************/

exprt get_significand(
  const exprt &src,
  const ieee_float_spect &spec)
{
  typecast_exprt magnitude(get_magnitude(src, spec), java_int_type());
  exprt exponent=get_exponent(src, spec);
  equal_exprt all_zeros(exponent, from_integer(0, exponent.type()));
  plus_exprt with_hidden_bit(
    magnitude, from_integer(0x800000, java_int_type()));
  return if_exprt(all_zeros, magnitude, with_hidden_bit);
}

/*******************************************************************\

Function:  single_precision_float

\*******************************************************************/

exprt single_precision_float(float f)
{
  ieee_float_spect float_spec=ieee_float_spect::single_precision();
  // Subcase of 0.0
  ieee_floatt fl(float_spec);
  fl.from_float(f);
  return fl.to_expr();
}

/*******************************************************************\

Function:  estimate_decimal_exponent

Purpose:
         We are looking for d such that n * 10^d = m * 10^e, so:
         d = log_10(m) + log_10(2) * e - log_10(n)
         m - the magnitude - should be between 1 and 2 so log_10(m)
         in [0,log_10(2)]
         n - the magnitude in base 10 - should be between 1 and 10 so
         log_10(n) in [0, 1]
         So the estimate is given by:
         d ~=~  floor( log10(2) * e)

\*******************************************************************/

exprt log_10_of_2=single_precision_float(0.301029995663981);

exprt estimate_decimal_exponent(const exprt &f,  const ieee_float_spect &spec)
{
  exprt bin_exp=get_exponent(f, spec);
  mult_exprt dec_exponent(
    typecast_exprt(bin_exp, java_float_type()), log_10_of_2);
  return typecast_exprt(dec_exponent, java_int_type());
}


/*******************************************************************\

Function:  estimate_decimal_magnitude

Purpose:


\*******************************************************************/


exprt estimate_decimal_magnitude(const exprt &f,  const ieee_float_spect &spec)
{
  exprt bin_frac=get_magnitude(f, spec);
  return typecast_exprt(bin_frac, java_int_type());
}

/*******************************************************************\

Function:  get_first_character_from_log_representation

Purpose: Given logarithm 10 of n, finds out what should be the first
         character in the representation of n.
         For instance if n=8, its logarithm is 0.90309, so given 0.90309
         the function should return '8'

\*******************************************************************/

double log_table[]={0.0000000, 0.3010300, 0.4771213, 0.6020600, 0.6989700,
                    0.7781513, 0.8450980, 0.9030900, 0.9542425, 0.1000000};

exprt get_first_character_from_log_representation(const exprt &log)
{
  exprt ret=from_integer('0', java_char_type());
  for(std::size_t i=9; i>0; --i)
    ret=if_exprt(
      binary_relation_exprt(log, ID_le, single_precision_float(log_table[i])),
      from_integer('0'+i, java_char_type()),
      ret);
  return ret;
}

// Table for values of 2^e / 10^(floor(log_10(2) * e)) for e from 0 to 128
std::vector<double> two_power_e_over_ten_power_d_table(
{1, 2, 4, 8, 1.6, 3.2, 6.4, 1.28, 2.56,
 5.12, 1.024, 2.048, 4.096, 8.192, 1.6384, 3.2768, 6.5536,
 1.31072, 2.62144, 5.24288, 1.04858, 2.09715, 4.19430, 8.38861, 1.67772,
 3.35544, 6.71089, 1.34218, 2.68435, 5.36871, 1.07374, 2.14748, 4.29497,
 8.58993, 1.71799, 3.43597, 6.87195, 1.37439, 2.74878, 5.49756, 1.09951,
 2.19902, 4.39805, 8.79609, 1.75922, 3.51844, 7.03687, 1.40737, 2.81475,
 5.62950, 1.12590, 2.25180, 4.50360, 9.00720, 1.80144, 3.60288, 7.20576,
 1.44115, 2.88230, 5.76461, 1.15292, 2.30584, 4.61169, 9.22337, 1.84467,
 3.68935, 7.37870, 1.47574, 2.95148, 5.90296, 1.18059, 2.36118, 4.72237,
 9.44473, 1.88895, 3.77789, 7.55579, 1.51116, 3.02231, 6.04463, 1.20893,
 2.41785, 4.83570, 9.67141, 1.93428, 3.86856, 7.73713, 1.54743, 3.09485,
 6.18970, 1.23794, 2.47588, 4.95176, 9.90352, 1.98070, 3.96141, 7.92282,
 1.58456, 3.16913, 6.33825, 1.26765, 2.53530, 5.07060, 1.01412, 2.02824,
 4.05648, 8.11296, 1.62259, 3.24519, 6.49037, 1.29807, 2.59615, 5.1923,
 1.03846, 2.07692, 4.15384, 8.30767, 1.66153, 3.32307, 6.64614, 1.32923,
 2.65846, 5.31691, 1.06338, 2.12676, 4.25353, 8.50706, 1.70141});


/*******************************************************************\

Function: java_string_library_preprocesst::code_for_scientific_notation

Purpose:
         A float is represented as $f=m*2^e$ where
         $0 <= m < 2$ is the significand and $-126 <= e <= 127$ is the exponent
         We want an alternate representation by finding n and d
         such that $f=n*10^d$. We can estimate d using the following:
         $d ~= log_10(f/n) ~= log_10(m) + log_10(2) * e - log_10(n)$
         Then $n$ can be expressed by the equation:
         $log_10(n) = log_10(m) + log_10(2) * e - d$
         log_10(m) can be 0 or -1

\*******************************************************************/

codet java_string_library_preprocesst::code_for_scientific_notation(
  const exprt &arg,
  const ieee_float_spect &float_spec,
  const string_exprt &string_expr,
  const exprt &tmp_string,
  const refined_string_typet &refined_string_type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  code_blockt code;

  // `binary_exponent` is $e$ in the formulas
  exprt binary_exponent=get_exponent(arg, float_spec);

  // `binary_significand` is `m` in the formulas
  exprt binary_significand=get_significand(arg, float_spec);

  // `decimal_exponent` is $d$ in the formulas
  exprt decimal_exponent=estimate_decimal_exponent(arg, float_spec);

  // bias_factor is $2^e/10^d$
  array_exprt bias_table(
    array_typet(java_float_type(), from_integer(128, java_int_type())));
  for(const auto &f:two_power_e_over_ten_power_d_table)
    bias_table.copy_to_operands(single_precision_float(f));
  index_exprt bias_factor(bias_table, binary_exponent, java_float_type());

  // `dec_significand` is $n = m * bias_factor$
  mult_exprt dec_significand(
    typecast_exprt(binary_significand, java_float_type()), bias_factor);

  // we divide this number by 0x80000 because it represents a fraction
  // and multiply by 1000000 to get more digits
  mult_exprt dec_significand_with_8_digits(
    dec_significand, single_precision_float(1.192092896));
  typecast_exprt dec_significand_int(
    dec_significand_with_8_digits,
    java_int_type());

  // The first character is given by dec_significand_int / 1000000
  div_exprt dec_significand_integer_part(
    dec_significand_int, from_integer(1000000, java_int_type()));
  string_exprt string_first_character=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_first_character,
      ID_cprover_string_of_int_func,
      {dec_significand_integer_part},
      symbol_table));

  // string_lit_dot = "."
  string_exprt string_lit_dot=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_string_literal_to_string_expr(
      string_lit_dot, tmp_string, ".", symbol_table));

  // string_expr_with_dot = concat(string_magnitude, string_lit_dot)
  string_exprt string_expr_with_dot=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr_with_dot,
      ID_cprover_string_concat_func,
      {string_first_character, string_lit_dot},
      symbol_table));

  // string_fractional_part
  minus_exprt dec_significand_fractional_part(
    dec_significand_int,
    mult_exprt(dec_significand_integer_part,
               from_integer(1000000, java_int_type())));

  string_exprt string_fractional_part=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_fractional_part,
      ID_cprover_string_of_int_func,
      {typecast_exprt(dec_significand_fractional_part, java_int_type())},
      symbol_table));

  // string_expr_with_fractional_part =
  //   concat(string_with_do, string_fractional_part)
  string_exprt string_expr_with_fractional_part=fresh_string_expr(
    loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr_with_fractional_part,
      ID_cprover_string_concat_func,
      {string_expr_with_dot, string_fractional_part},
      symbol_table));

  // string_lit_E = "E"
  string_exprt string_lit_E=fresh_string_expr(loc, symbol_table);

  code.copy_to_operands(
    code_assign_string_literal_to_string_expr(
      string_lit_E, tmp_string, "E", symbol_table));

  // string_expr_with_E = concat(string_magnitude, string_lit_E)
  string_exprt string_expr_with_E=fresh_string_expr(loc, symbol_table);
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr_with_E,
      ID_cprover_string_concat_func,
      {string_expr_with_fractional_part, string_lit_E},
      symbol_table));

  // exponent_string = string_of_int(decimal_exponent)
  string_exprt exponent_string=fresh_string_expr(loc, symbol_table);

  code.copy_to_operands(
    code_assign_function_to_string_expr(
      exponent_string,
      ID_cprover_string_of_int_func,
      {decimal_exponent},
      symbol_table));

  // string_expr = concat(string_expr_withE, exponent_string)
  code.copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr,
      ID_cprover_string_concat_func,
      {string_expr_with_E, exponent_string},
      symbol_table));

  return code;
}

/*******************************************************************\

Function: java_string_library_preprocesst::make_float_to_string_code

  Inputs:
    code - the code of a function call

 Outputs: code for the Float.toString(F) function:
          > String * str;
          > str = MALLOC(String);
          > String * tmp_string;
          > int string_expr_length;
          > char[] string_expr_content;
          > CPROVER_string string_expr_sym;
          > if arguments[1]==NaN
          > then {tmp_string="NaN"; string_expr=(string_expr)tmp_string}
          > if arguments[1]==Infinity
          > then {tmp_string="Infinity"; string_expr=(string_expr)tmp_string}
          > if 1e-3<arguments[1]<1e6
          > then {tmp_string=string_of_int((int)arguments[1]);
          >       string_expr=(string_expr)tmp_string}
          > string_expr_sym=string_expr;
          > str=(String*) string_expr;
          > return str;

\*******************************************************************/

codet java_string_library_preprocesst::make_float_to_string_code(
  const code_typet &type,
  const source_locationt &loc,
  symbol_tablet &symbol_table)
{
  // Getting the argument
  code_typet::parameterst params=type.parameters();
  assert(params.size()==1 && "wrong number of parameters in Float.toString");
  exprt arg=symbol_exprt(params[0].get_identifier(), params[0].type());

  // Holder for output code
  code_blockt code;

  // Declaring and allocating String * str
  exprt str=allocate_fresh_string(type.return_type(), loc, symbol_table, code);
  exprt tmp_string=fresh_string(type.return_type(), loc, symbol_table);

  // Declaring CPROVER_string string_expr
  refined_string_typet ref_type(java_int_type(), java_char_type());
  string_exprt string_expr=fresh_string_expr(loc, symbol_table);
  exprt string_expr_sym=fresh_string_expr_symbol(loc, symbol_table);

  // List of the different cases
  std::vector<code_ifthenelset> case_list;

  // First case in the list is the default
  code_ifthenelset case_sci_notation;
  ieee_float_spect float_spec=ieee_float_spect::single_precision();
  // Subcase of 0.0
  ieee_floatt zero_float(float_spec);
  zero_float.from_float(0.0);
  constant_exprt zero=zero_float.to_expr();
  case_sci_notation.cond()=ieee_float_equal_exprt(arg, zero);
  case_sci_notation.then_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "0.0", symbol_table);

  // Subcase of computerized scientific notation
  case_sci_notation.else_case()=code_for_scientific_notation(
    arg, float_spec, string_expr, tmp_string, ref_type, loc, symbol_table);
  case_list.push_back(case_sci_notation);

  // Case of NaN
  code_ifthenelset case_nan;
  case_nan.cond()=isnan_exprt(arg);
  case_nan.then_case()=code_assign_string_literal_to_string_expr(
    string_expr, tmp_string, "NaN", symbol_table);
  case_list.push_back(case_nan);

  // Case of Infinity
  code_ifthenelset case_infinity;
  case_infinity.cond()=isinf_exprt(arg);
  // TODO: should also detect -Infinity
  case_infinity.then_case()=code_assign_string_literal_to_string_expr(
        string_expr, tmp_string, "Infinity", symbol_table);
  case_list.push_back(case_infinity);

  // Case of simple notation
  code_ifthenelset case_simple_notation;

  ieee_floatt bound_inf_float(float_spec);
  ieee_floatt bound_sup_float(float_spec);
  bound_inf_float.from_float(1e-3);
  bound_sup_float.from_float(1e7);
  constant_exprt bound_inf=bound_inf_float.to_expr();
  constant_exprt bound_sup=bound_sup_float.to_expr();

  and_exprt is_simple_float(
    binary_relation_exprt(arg, ID_ge, bound_inf),
    binary_relation_exprt(arg, ID_lt, bound_sup));
  case_simple_notation.cond()=is_simple_float;
  case_simple_notation.then_case()=code_blockt();

  // integer part
  typecast_exprt integer_part(arg, java_int_type());
  string_exprt integer_part_string_expr=fresh_string_expr(loc, symbol_table);

  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      integer_part_string_expr,
      ID_cprover_string_of_int_func,
      {integer_part},
      symbol_table));

  // dot
  string_exprt dot_string_lit=fresh_string_expr(loc, symbol_table);
  case_simple_notation.then_case().copy_to_operands(
    code_assign_string_literal_to_string_expr(
      dot_string_lit, tmp_string, ".", symbol_table));
  string_exprt with_dot_string_expr=fresh_string_expr(loc, symbol_table);

  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      with_dot_string_expr,
      ID_cprover_string_concat_func,
      {integer_part_string_expr, dot_string_lit},
      symbol_table));

  // fractional_part = arg - (float) integer_part
  minus_exprt fractional_part(arg, typecast_exprt(integer_part, arg.type()));
  string_exprt fractional_part_string_expr=fresh_string_expr(loc, symbol_table);
  ieee_floatt shifting(float_spec);
  shifting.from_float(1e7);
  typecast_exprt fractional_part_shifted(
    mult_exprt(fractional_part, shifting.to_expr()), java_int_type());
  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      fractional_part_string_expr,
      ID_cprover_string_of_fractional_part_func,
      {fractional_part_shifted, from_integer(7, java_int_type())},
      symbol_table));

  // string_expr = concat(with_dot_string_expr, string_of_int(fractional_part))
  case_simple_notation.then_case().copy_to_operands(
    code_assign_function_to_string_expr(
      string_expr,
      ID_cprover_string_concat_func,
      {with_dot_string_expr, fractional_part_string_expr},
      symbol_table));

  case_list.push_back(case_simple_notation);

  // Combining all cases
  for(std::size_t i=1; i<case_list.size(); i++)
    case_list[i].else_case()=case_list[i-1];
  code.copy_to_operands(case_list[case_list.size()-1]);

  // str = string_expr
  code.copy_to_operands(code_assign_string_expr_to_java_string(
    str, string_expr, symbol_table));

  // Assign string_expr_sym = { string_expr_length, string_expr_content }
  code.copy_to_operands(code_assignt(string_expr_sym, string_expr));

  // Return str
  code.copy_to_operands(code_returnt(str));
  return code;
}
