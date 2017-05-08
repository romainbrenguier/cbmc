/*******************************************************************\

Module: Generates string constraints for functions generating strings
        from other types, in particular int, long, float, double, char, bool

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/floatbv/float_bv.h>

#include "string_constraint_generator.h"


/*******************************************************************\

Function: get_exponent

  Inputs:
    src - a floating point expression
    spec - specification for floating points

 Outputs:
    a 32 bit integer representing the exponent

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
  // TODO: this 32 bit is arbitrary
  return minus_exprt(typecast_exprt(exp_bits, unsignedbv_typet(32)),
                     from_integer(spec.bias(), unsignedbv_typet(32)));
}

/*******************************************************************\

Function: get_magnitude

  Inputs:
    src - a floating point expression
    spec - specification for floating points

 Outputs:
    an unsigned value representing the magnitude

 Purpose: Gets the magnitude without hidden bit

\*******************************************************************/

exprt get_magnitude(
  const exprt &src,
  const ieee_float_spect &spec)
{
  return extractbits_exprt(src, spec.f-1, 0, unsignedbv_typet(spec.f));
}

/*******************************************************************\

Function: get_significand

  Inputs:
    src - a floating point expression
    spec - specification for floating points

  Outputs:
    an unsigned 32 bit expression

  Purpose: Gets the significand as a java integer, looking for the hidden bit

  TODO : this should be generalized for non 32 bits

\*******************************************************************/

exprt get_significand(
  const exprt &src,
  const ieee_float_spect &spec)
{
  typecast_exprt magnitude(get_magnitude(src, spec), unsignedbv_typet(32));
  exprt exponent=get_exponent(src, spec);
  equal_exprt all_zeros(exponent, from_integer(0, exponent.type()));
  plus_exprt with_hidden_bit(
    magnitude, from_integer(0x800000, unsignedbv_typet(32)));
  return if_exprt(all_zeros, magnitude, with_hidden_bit);
}

/*******************************************************************\

Function:  single_precision_float

  Inputs:
    f - a floating point value

  Ouptus:
    an expression representing this floating point

\*******************************************************************/

exprt single_precision_float(float f)
{
  ieee_float_spect float_spec=ieee_float_spect::single_precision();
  ieee_floatt fl(float_spec);
  fl.from_float(f);
  return fl.to_expr();
}


exprt floatbv_mult(
  const exprt &f, const exprt &g, ieee_floatt::rounding_modet rounding)
{
  assert(f.type()==g.type());
  exprt mult(ID_floatbv_mult, f.type());
  mult.copy_to_operands(f);
  mult.copy_to_operands(g);
  mult.copy_to_operands(from_integer(rounding, unsignedbv_typet(32)));
  return mult;
}

/*******************************************************************\

Function:  estimate_decimal_exponent

  Inputs:
    f - a floating point expression
    spec - specification for floating point

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

exprt estimate_decimal_exponent(const exprt &f,  const ieee_float_spect &spec)
{
  exprt log_10_of_2=single_precision_float(0.301029995663981);
  exprt bin_exp=get_exponent(f, spec);
  floatbv_typecast_exprt float_bin_exp(
    bin_exp,
    from_integer(ieee_floatt::ROUND_TO_ZERO, unsignedbv_typet(32)),
    spec.to_type());
  exprt dec_exponent=floatbv_mult(
    float_bin_exp,
    log_10_of_2,
    ieee_floatt::ROUND_TO_EVEN);
  return floatbv_typecast_exprt(
    dec_exponent,
    from_integer(ieee_floatt::ROUND_TO_ZERO, unsignedbv_typet(32)),
    signedbv_typet(32));
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_float

  Inputs: function application with one float argument

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.valueOf(F) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_float(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_from_float(args(f, 1)[0], ref_type, false);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_double

  Inputs: function application with one double argument

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.valueOf(D) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_double(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_from_float(args(f, 1)[0], ref_type, true);
}

/*******************************************************************\

Function: round_expr_to_zero

  Inputs:
    f - expression representing a float

 Outputs: expression representing a 32 bit integer

 Purpose: round the float to an integer geting closer to 0

\*******************************************************************/

exprt round_expr_to_zero(const exprt &f)
{
  return floatbv_typecast_exprt(
    f,
    from_integer(ieee_floatt::ROUND_TO_ZERO, unsignedbv_typet(32)),
    signedbv_typet(32));
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_float

  Inputs: float expression and Boolean signaling that the argument has
          double precision

 Outputs: a new string expression

 Purpose: add axioms corresponding to the integer part of m, in decimal form
          with no leading zeroes, followed by '.' ('\u002E'), followed by one
          or more decimal digits representing the fractional part of m.

    TODO: this specification is not correct for negative numbers

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_float(
  const exprt &f, const refined_string_typet &ref_type, bool double_precision)
{
  // TODO: adapt this for double precision
  // shited_float is floor(f * 1e5)
  exprt shifting=single_precision_float(1e5);
  exprt shifted_float=round_expr_to_zero(
    floatbv_mult(f, shifting, ieee_floatt::ROUND_TO_ZERO));
  // fractional_part_shifted is floor(f * 100000) % 100000
  mod_exprt fractional_part_shifted(
    shifted_float, from_integer(100000, shifted_float.type()));

  // integer part
  mod_exprt integer_part(
    round_expr_to_zero(f), from_integer(10000, shifted_float.type()));
  string_exprt integer_part_string_expr=add_axioms_from_int(
    integer_part, 4, ref_type);

  string_exprt fractional_part_string_expr=add_axioms_for_fractional_part(
    fractional_part_shifted, 6, ref_type);

  return add_axioms_for_concat(
    integer_part_string_expr, fractional_part_string_expr);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_fractional_part

  Inputs:
    i - an integer expression
    max_size - a maximal size for the string
    ref_type - a type for refined strings

 Outputs: a string expression

 Purpose: add axioms for representing the fractional part of a floating
          point starting with a dot

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_fractional_part(
    const exprt &i, size_t max_size, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  const typet &type=i.type();
  assert(type.id()==ID_signedbv);
  exprt ten=from_integer(10, type);
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();
  exprt zero_char=constant_char('0', char_type);
  exprt nine_char=constant_char('9', char_type);
  exprt max=from_integer(max_size, index_type);

  // We add axioms:
  // a1 : 2 <= |res| <= max_size
  // a2 : forall 1 <= i < size '0' < res[i] < '9'
  // res[0] = '.'
  // a3 : i = sum_j 10^j res[j] - '0'
  // for all j : !(|res| = j+1 && res[j]='0')
  // for all j : |res| <= j => res[j]='0'

  and_exprt a1(res.axiom_for_is_strictly_longer_than(1),
               res.axiom_for_is_shorter_than(max));
  axioms.push_back(a1);

  equal_exprt starts_with_dot(res[0], from_integer('.', char_type));

  exprt::operandst digit_constraints;
  digit_constraints.push_back(starts_with_dot);
  exprt sum=from_integer(0, type);

  for(size_t j=1; j<max_size; j++)
  {
    binary_relation_exprt after_end(
      res.length(), ID_le, from_integer(j, res.length().type()));
    mult_exprt ten_sum(sum, ten);

    // sum = 10 * sum + (res[j]-'0')
    if_exprt to_add(
      after_end,
      from_integer(0, type),
      typecast_exprt(minus_exprt(res[j], zero_char), type));
    sum=plus_exprt(ten_sum, to_add);

    and_exprt is_number(
          binary_relation_exprt(res[j], ID_ge, zero_char),
          binary_relation_exprt(res[j], ID_le, nine_char));
    digit_constraints.push_back(is_number);

    // There are no trailing zeros except for ".0" (i.e j=2)
    if(j>1)
    {
      not_exprt no_trailing_zero(and_exprt(
        equal_exprt(res.length(), from_integer(j+1, res.length().type())),
      equal_exprt(res[j], zero_char)));
      axioms.push_back(no_trailing_zero);
    }
  }

  exprt a2=conjunction(digit_constraints);
  axioms.push_back(a2);

  equal_exprt a3(i, sum);
  axioms.push_back(a3);

  return res;
}

/*******************************************************************\

Function: string_constraint_generatort::
            add_axioms_from_float_scientific_notation(

  Inputs:
    f - a float expression
    max_size - a maximal size for the string
    ref_type - a type for refined strings

 Outputs: a string expression

 Purpose: Add axioms to write the float in scientific notation
         A float is represented as $f=m*2^e$ where
         $0 <= m < 2$ is the significand and $-126 <= e <= 127$ is the exponent
         We want an alternate representation by finding n and d
         such that $f=n*10^d$. We can estimate d using the following:
         $d ~= log_10(f/n) ~= log_10(m) + log_10(2) * e - log_10(n)$
         Then $n$ can be expressed by the equation:
         $log_10(n) = log_10(m) + log_10(2) * e - d$
         log_10(m) can be 0 or -1

 TODO: this is not precise at the moment

\*******************************************************************/

string_exprt string_constraint_generatort::
  add_axioms_from_float_scientific_notation(
    const exprt &f, const refined_string_typet &ref_type)
{
  ieee_float_spect float_spec=ieee_float_spect::single_precision();
  typet float_type=float_spec.to_type();

  // `binary_exponent` is $e$ in the formulas
  exprt binary_exponent=get_exponent(f, float_spec);

  // `binary_significand` is `m` in the formulas
  exprt binary_significand=get_significand(f, float_spec);

  // `decimal_exponent` is $d$ in the formulas
  exprt decimal_exponent=estimate_decimal_exponent(f, float_spec);

  // bias_factor is $2^e/10^d$
  // TODO: this 32 bit is arbitrary
  array_exprt bias_table(
    array_typet(unsignedbv_typet(32), from_integer(128, unsignedbv_typet(32))));

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

  for(const auto &f:two_power_e_over_ten_power_d_table)
    bias_table.copy_to_operands(single_precision_float(f));
  index_exprt bias_factor(bias_table, binary_exponent, float_type);

  floatbv_typecast_exprt binary_significand_float(
    binary_significand,
    from_integer(ieee_floatt::ROUND_TO_ZERO, unsignedbv_typet(32)),
    float_type);
  // `dec_significand` is $n = m * bias_factor$
  exprt dec_significand=floatbv_mult(
    bias_factor, binary_significand_float, ieee_floatt::ROUND_TO_ZERO);

  // we divide this number by 0x80000 because it represents a fraction
  // and multiply by 1000000 to get more digits
  exprt dec_significand_with_8_digits=floatbv_mult(
    dec_significand,
    single_precision_float(0.1192092896),
    ieee_floatt::ROUND_TO_ZERO);
  floatbv_typecast_exprt dec_significand_int(
    dec_significand_with_8_digits,
    from_integer(ieee_floatt::ROUND_TO_ZERO, unsignedbv_typet(32)),
    signedbv_typet(32));

  // The first character is given by dec_significand_int / 1000000
  div_exprt dec_significand_integer_part(
    dec_significand_int, from_integer(1000000, signedbv_typet(32)));
  string_exprt string_integer_part=add_axioms_from_int(
    dec_significand_integer_part, 4, ref_type);

  // TODO: adapt this for double precision
  // shited_float is floor(f * 1e5)
  exprt shifting=single_precision_float(1e5);
  exprt shifted_float=round_expr_to_zero(
    floatbv_mult(f, shifting, ieee_floatt::ROUND_TO_ZERO));
  // fractional_part_shifted is floor(f * 100000) % 100000
  mod_exprt fractional_part_shifted(
    shifted_float, from_integer(100000, shifted_float.type()));

  string_exprt string_fractional_part=add_axioms_for_fractional_part(
        fractional_part_shifted, 6, ref_type);

  // string_expr_with_fractional_part =
  //   concat(string_with_do, string_fractional_part)
  string_exprt string_expr_with_fractional_part=add_axioms_for_concat(
        string_integer_part, string_fractional_part);

  // string_expr_with_E = concat(string_magnitude, string_lit_E)
  string_exprt string_expr_with_E=add_axioms_for_concat_char(
      string_expr_with_fractional_part,
      from_integer('E', ref_type.get_char_type()));

  // exponent_string = string_of_int(decimal_exponent)
  string_exprt exponent_string=add_axioms_from_int(
    decimal_exponent, 3, ref_type);

  // string_expr = concat(string_expr_withE, exponent_string)
  return add_axioms_for_concat(string_expr_with_E, exponent_string);
}

/*******************************************************************\

Function: string_constraint_generatort::
            add_axioms_from_float_scientific_notation

  Inputs:
    f - a function application expression

 Outputs: a new string expression

 Purpose: add axioms corresponding to the scientific representation
          of floating point values

\*******************************************************************/

string_exprt string_constraint_generatort::
  add_axioms_from_float_scientific_notation(
    const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());

  return add_axioms_from_float_scientific_notation(
    args(f, 1)[0], ref_type);
}
