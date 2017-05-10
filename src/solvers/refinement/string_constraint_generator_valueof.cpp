/*******************************************************************\

Module: Generates string constraints for functions generating strings
        from other types, in particular int, long, float, double, char, bool

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint_generator.h>

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_int

  Inputs: function application with one integer argument

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.valueOf(I) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_int(
  const function_application_exprt &expr)
{
  const refined_string_typet &ref_type=to_refined_string_type(expr.type());
  return add_axioms_from_int(args(expr, 1)[0], MAX_INTEGER_LENGTH, ref_type);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_long

  Inputs: function application with one long argument

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.valueOf(J) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_long(
  const function_application_exprt &expr)
{
  const refined_string_typet &ref_type=to_refined_string_type(expr.type());
  return add_axioms_from_int(args(expr, 1)[0], MAX_LONG_LENGTH, ref_type);
}



/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_bool

  Inputs: function application with on Boolean argument

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.valueOf(Z) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_bool(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_from_bool(args(f, 1)[0], ref_type);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_bool

  Inputs: Boolean expression

 Outputs: a new string expression

 Purpose: add axioms stating that the returned string equals "true" when
          the Boolean expression is true and "false" when it is false

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_bool(
  const exprt &b, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  const typet &char_type=ref_type.get_char_type();

  assert(b.type()==bool_typet() || b.type().id()==ID_c_bool);

  typecast_exprt eq(b, bool_typet());

  // We add axioms:
  // a1 : eq => res = |"true"|
  // a2 : forall i < |"true"|. eq => res[i]="true"[i]
  // a3 : !eq => res = |"false"|
  // a4 : forall i < |"false"|. !eq => res[i]="false"[i]

  std::string str_true="true";
  implies_exprt a1(eq, res.axiom_for_has_length(str_true.length()));
  axioms.push_back(a1);

  for(std::size_t i=0; i<str_true.length(); i++)
  {
    exprt chr=from_integer(str_true[i], char_type);
    implies_exprt a2(eq, equal_exprt(res[i], chr));
    axioms.push_back(a2);
  }

  std::string str_false="false";
  implies_exprt a3(not_exprt(eq), res.axiom_for_has_length(str_false.length()));
  axioms.push_back(a3);

  for(std::size_t i=0; i<str_false.length(); i++)
  {
    exprt chr=from_integer(str_false[i], char_type);
    implies_exprt a4(not_exprt(eq), equal_exprt(res[i], chr));
    axioms.push_back(a4);
  }

  return res;
}

/*******************************************************************\

Function: smallest_by_digit

  Inputs: number of digit

 Outputs: an integer with the right number of digit

 Purpose: gives the smallest integer with the specified number of digits

\*******************************************************************/

static mp_integer smallest_by_digit(int nb)
{
  return power(10, nb-1);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_int

  Inputs: a signed integer expression, and a maximal size for the string
          representation

 Outputs: a string expression

 Purpose: add axioms to say the string corresponds to the result of
          String.valueOf(I) or String.valueOf(J) java functions applied on the
          integer expression

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_int(
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
  exprt minus_char=constant_char('-', char_type);
  exprt zero=from_integer(0, index_type);
  exprt max=from_integer(max_size, index_type);

  // We add axioms:
  // a1 : 0 <|res|<=max_size
  // a2 : (res[0]='-')||('0'<=res[0]<='9')

  and_exprt a1(res.axiom_for_is_strictly_longer_than(zero),
               res.axiom_for_is_shorter_than(max));
  axioms.push_back(a1);

  exprt chr=res[0];
  equal_exprt starts_with_minus(chr, minus_char);
  and_exprt starts_with_digit(
    binary_relation_exprt(chr, ID_ge, zero_char),
    binary_relation_exprt(chr, ID_le, nine_char));
  or_exprt a2(starts_with_digit, starts_with_minus);
  axioms.push_back(a2);

  // These are constraints to detect number that requiere the maximum number
  // of digits
  exprt smallest_with_max_digits=
    from_integer(smallest_by_digit(max_size-1), type);
  binary_relation_exprt big_negative(
    i, ID_le, unary_minus_exprt(smallest_with_max_digits));
  binary_relation_exprt big_positive(i, ID_ge, smallest_with_max_digits);
  or_exprt requieres_max_digits(big_negative, big_positive);

  for(size_t size=1; size<=max_size; size++)
  {
    // For each possible size, we add axioms:
    // all_numbers: forall 1<=i<=size. '0'<=res[i]<='9'
    // a3 : |res|=size&&'0'<=res[0]<='9' =>
    //      i=sum+str[0]-'0' &&all_numbers
    // a4 : |res|=size&&res[0]='-' => i=-sum
    // a5 : size>1 => |res|=size&&'0'<=res[0]<='9' => res[0]!='0'
    // a6 : size>1 => |res|=size&&res[0]'-' => res[1]!='0'
    // a7 : size==max_size => i>1000000000
    exprt sum=from_integer(0, type);
    exprt all_numbers=true_exprt();
    chr=res[0];
    exprt first_value=typecast_exprt(minus_exprt(chr, zero_char), type);

    for(size_t j=1; j<size; j++)
    {
      chr=res[j];
      sum=plus_exprt(
        mult_exprt(sum, ten),
        typecast_exprt(minus_exprt(chr, zero_char), type));
      first_value=mult_exprt(first_value, ten);
      and_exprt is_number(
        binary_relation_exprt(chr, ID_ge, zero_char),
        binary_relation_exprt(chr, ID_le, nine_char));
      all_numbers=and_exprt(all_numbers, is_number);
    }

    axioms.push_back(all_numbers);

    equal_exprt premise=res.axiom_for_has_length(size);
    equal_exprt constr3(i, plus_exprt(sum, first_value));
    implies_exprt a3(and_exprt(premise, starts_with_digit), constr3);
    axioms.push_back(a3);

    implies_exprt a4(
      and_exprt(premise, starts_with_minus),
      equal_exprt(i, unary_minus_exprt(sum)));
    axioms.push_back(a4);

    // disallow 0s at the beginning
    if(size>1)
    {
      equal_exprt r0_zero(res[zero], zero_char);
      implies_exprt a5(
        and_exprt(premise, starts_with_digit),
        not_exprt(r0_zero));
      axioms.push_back(a5);

      exprt one=from_integer(1, index_type);
      equal_exprt r1_zero(res[one], zero_char);
      implies_exprt a6(
        and_exprt(premise, starts_with_minus),
        not_exprt(r1_zero));
      axioms.push_back(a6);
    }

    // when the size is close to the maximum, either the number is very big
    // or it is negative
    if(size==max_size-1)
    {
      implies_exprt a7(premise, or_exprt(requieres_max_digits,
                                         starts_with_minus));
      axioms.push_back(a7);
    }
    // when we reach the maximal size the number is very big in the negative
    if(size==max_size)
    {
      implies_exprt a7(premise, and_exprt(starts_with_minus, big_negative));
      axioms.push_back(a7);
    }
  }
  return res;
}

/*******************************************************************\

Function: string_constraint_generatort::int_of_hex_char

  Inputs: a character expression in the following set: 0123456789abcdef

 Outputs: an integer expression

 Purpose: returns the value represented by the character

\*******************************************************************/

exprt string_constraint_generatort::int_of_hex_char(const exprt &chr) const
{
  exprt zero_char=constant_char('0', chr.type());
  exprt nine_char=constant_char('9', chr.type());
  exprt a_char=constant_char('a', chr.type());
  return if_exprt(
    binary_relation_exprt(chr, ID_gt, nine_char),
    plus_exprt(constant_char(10, chr.type()), minus_exprt(chr, a_char)),
    minus_exprt(chr, zero_char));
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_int_hex

  Inputs: one integer argument

 Outputs: a new string expression

 Purpose: add axioms stating that the returned string corresponds to the
          integer argument written in hexadecimal

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_int_hex(
  const exprt &i, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  const typet &type=i.type();
  assert(type.id()==ID_signedbv);
  const typet &index_type=ref_type.get_index_type();
  const typet &char_type=ref_type.get_char_type();
  exprt sixteen=from_integer(16, index_type);
  exprt minus_char=constant_char('-', char_type);
  exprt zero_char=constant_char('0', char_type);
  exprt nine_char=constant_char('9', char_type);
  exprt a_char=constant_char('a', char_type);
  exprt f_char=constant_char('f', char_type);

  size_t max_size=8;
  axioms.push_back(
    and_exprt(res.axiom_for_is_strictly_longer_than(0),
              res.axiom_for_is_shorter_than(max_size)));

  for(size_t size=1; size<=max_size; size++)
  {
    exprt sum=from_integer(0, type);
    exprt all_numbers=true_exprt();
    exprt chr=res[0];

    for(size_t j=0; j<size; j++)
    {
      chr=res[j];
      exprt i=int_of_hex_char(chr);
      sum=plus_exprt(mult_exprt(sum, sixteen), typecast_exprt(i, type));
      or_exprt is_number(
        and_exprt(
          binary_relation_exprt(chr, ID_ge, zero_char),
          binary_relation_exprt(chr, ID_le, nine_char)),
        and_exprt(
          binary_relation_exprt(chr, ID_ge, a_char),
          binary_relation_exprt(chr, ID_le, f_char)));
      all_numbers=and_exprt(all_numbers, is_number);
    }

    equal_exprt premise(res.axiom_for_has_length(size));
    axioms.push_back(
      implies_exprt(premise, and_exprt(equal_exprt(i, sum), all_numbers)));

    // disallow 0s at the beggining
    if(size>1)
      axioms.push_back(
        implies_exprt(premise, not_exprt(equal_exprt(res[0], zero_char))));
  }
  return res;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_int_hex

  Inputs: function application with integer argument

 Outputs: a new string expression

 Purpose: add axioms corresponding to the Integer.toHexString(I) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_int_hex(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_from_int_hex(args(f, 1)[0], ref_type);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_char

  Inputs: function application one char argument

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.valueOf(C) java function

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_char(
  const function_application_exprt &f)
{
  const refined_string_typet &ref_type=to_refined_string_type(f.type());
  return add_axioms_from_char(args(f, 1)[0], ref_type);
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_from_char

  Inputs: one expression of type char

 Outputs: a new string expression

 Purpose: add axioms stating that the returned string has length 1 and
          the character it contains correspond to the input expression

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_from_char(
  const exprt &c, const refined_string_typet &ref_type)
{
  string_exprt res=fresh_string(ref_type);
  and_exprt lemma(equal_exprt(res[0], c), res.axiom_for_has_length(1));
  axioms.push_back(lemma);
  return res;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_value_of

  Inputs: function application with one or three arguments

 Outputs: a new string expression

 Purpose: add axioms corresponding to the String.valueOf([C) and
          String.valueOf([CII) functions

\*******************************************************************/

string_exprt string_constraint_generatort::add_axioms_for_value_of(
  const function_application_exprt &f)
{
  const function_application_exprt::argumentst &args=f.arguments();
  if(args.size()==3)
  {
    const refined_string_typet &ref_type=to_refined_string_type(f.type());
    string_exprt res=fresh_string(ref_type);
    exprt char_array=args[0];
    exprt offset=args[1];
    exprt count=args[2];

    // We add axioms:
    // a1 : |res| = count
    // a2 : forall idx<count, str[idx+offset]=res[idx]

    string_exprt str=add_axioms_for_java_char_array(char_array);
    axioms.push_back(res.axiom_for_has_length(count));

    symbol_exprt idx=fresh_univ_index(
      "QA_index_value_of", ref_type.get_index_type());
    equal_exprt eq(str[plus_exprt(idx, offset)], res[idx]);
    string_constraintt a2(idx, count, eq);
    axioms.push_back(a2);
    return res;
  }
  else
  {
    assert(args.size()==1);
    return add_axioms_for_java_char_array(args[0]);
  }
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_correct_number_format

  Inputs: function application with one string expression

 Outputs: an boolean expression

 Purpose: add axioms making the return value true if the given string is
          a correct number

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_correct_number_format(
  const string_exprt &str, std::size_t max_size)
{
  symbol_exprt correct=fresh_boolean("correct_number_format");
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  const typet &index_type=ref_type.get_index_type();
  exprt zero_char=constant_char('0', char_type);
  exprt nine_char=constant_char('9', char_type);
  exprt minus_char=constant_char('-', char_type);
  exprt plus_char=constant_char('+', char_type);

  exprt chr=str[0];
  equal_exprt starts_with_minus(chr, minus_char);
  equal_exprt starts_with_plus(chr, plus_char);
  and_exprt starts_with_digit(
    binary_relation_exprt(chr, ID_ge, zero_char),
    binary_relation_exprt(chr, ID_le, nine_char));

  // TODO: we should have implications in the other direction for correct
  // correct => |str| > 0
  exprt non_empty=str.axiom_for_is_longer_than(from_integer(1, index_type));
  axioms.push_back(implies_exprt(correct, non_empty));

  // correct => (str[0] = '+' or '-' || '0' <= str[0] <= '9')
  or_exprt correct_first(
    or_exprt(starts_with_minus, starts_with_plus), starts_with_digit);
  axioms.push_back(implies_exprt(correct, correct_first));

  // correct => str[0]='+' or '-' ==> |str| > 1
  implies_exprt contains_digit(
    or_exprt(starts_with_minus, starts_with_plus),
    str.axiom_for_is_longer_than(from_integer(2, index_type)));
  axioms.push_back(implies_exprt(correct, contains_digit));

  // correct => |str| < max_size
  axioms.push_back(
    implies_exprt(correct, str.axiom_for_is_shorter_than(max_size)));

  // forall 1 <= qvar < |str| . correct => '0'<= str[qvar] <= '9'
  symbol_exprt qvar=fresh_univ_index("number_format", index_type);
  and_exprt is_digit(
    binary_relation_exprt(str[qvar], ID_ge, zero_char),
    binary_relation_exprt(str[qvar], ID_le, nine_char));
  string_constraintt all_digits(
    qvar, from_integer(1, index_type), str.length(), correct, is_digit);
  axioms.push_back(all_digits);

  return correct;
}

/*******************************************************************\

Function: string_constraint_generatort::add_axioms_for_parse_int

  Inputs: function application with one string expression

 Outputs: an integer expression

 Purpose: add axioms corresponding to the Integer.parseInt java function

\*******************************************************************/

exprt string_constraint_generatort::add_axioms_for_parse_int(
  const function_application_exprt &f)
{
  string_exprt str=get_string_expr(args(f, 1)[0]);
  const typet &type=f.type();
  symbol_exprt i=fresh_symbol("parsed_int", type);
  const refined_string_typet &ref_type=to_refined_string_type(str.type());
  const typet &char_type=ref_type.get_char_type();
  exprt zero_char=constant_char('0', char_type);
  exprt minus_char=constant_char('-', char_type);
  exprt plus_char=constant_char('+', char_type);
  assert(type.id()==ID_signedbv);
  exprt ten=from_integer(10, type);

  exprt chr=str[0];
  exprt starts_with_minus=equal_exprt(chr, minus_char);
  exprt starts_with_plus=equal_exprt(chr, plus_char);
  exprt starts_with_digit=binary_relation_exprt(chr, ID_ge, zero_char);

  // TODO: we should throw an exception when this does not hold:
  exprt correct=add_axioms_for_correct_number_format(str);
  axioms.push_back(correct);

  for(unsigned size=1; size<=10; size++)
  {
    exprt sum=from_integer(0, type);
    exprt first_value=typecast_exprt(minus_exprt(chr, zero_char), type);

    for(unsigned j=1; j<size; j++)
    {
      mult_exprt ten_sum(sum, ten);
      if(j>=9)
      {
        // We have to be careful about overflows
        div_exprt div(sum, ten);
        equal_exprt no_overflow(div, sum);
        axioms.push_back(no_overflow);
      }

      sum=plus_exprt_with_overflow_check(
        ten_sum,
        typecast_exprt(minus_exprt(str[j], zero_char), type));

      mult_exprt first(first_value, ten);
      if(j>=9)
      {
        // We have to be careful about overflows
        div_exprt div_first(first, ten);
        implies_exprt no_overflow_first(
          starts_with_digit, equal_exprt(div_first, first_value));
        axioms.push_back(no_overflow_first);
      }
      first_value=first;
    }

    // If the length is `size`, we add axioms:
    // a1 : starts_with_digit => i=sum+first_value
    // a2 : starts_with_plus => i=sum
    // a3 : starts_with_minus => i=-sum

    equal_exprt premise=str.axiom_for_has_length(size);
    implies_exprt a1(
      and_exprt(premise, starts_with_digit),
      equal_exprt(i, plus_exprt(sum, first_value)));
    axioms.push_back(a1);

    implies_exprt a2(and_exprt(premise, starts_with_plus), equal_exprt(i, sum));
    axioms.push_back(a2);

    implies_exprt a3(
      and_exprt(premise, starts_with_minus),
      equal_exprt(i, unary_minus_exprt(sum)));
    axioms.push_back(a3);
  }
  return i;
}
