/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java Character
        library are replaced by simple expressions.

Author: Romain Brenguier

Date:   March 2017

\*******************************************************************/

#include <util/arith_tools.h>
#include "character_refine_preprocess.h"

/*******************************************************************\

Function: character_refine_preprocesst::in_interval_expr

  Inputs: an expression, a integer lower bound and upper bound

 Outputs: an expression

 Purpose: the returned expression is true when the first argument is in the
          interval defined by the lower and upper bounds (included)

\*******************************************************************/

exprt character_refine_preprocesst::in_interval_expr(
  exprt arg, mp_integer lower_bound, mp_integer upper_bound)
{
  and_exprt res(
    binary_relation_exprt(arg, ID_ge, from_integer(lower_bound, arg.type())),
    binary_relation_exprt(arg, ID_le, from_integer(upper_bound, arg.type())));
  return res;
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_function

  Inputs: a function on expression and a position in a goto program

 Purpose: converts based on a function on expressions

\*******************************************************************/
void character_refine_preprocesst::convert_char_function(
  exprt (*expr_function)(exprt expr, typet type), conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  assert(function_call.arguments().size()==1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  typet type=result.type();
  code_assignt code(result, expr_function(arg, type));
  target->code=code;
}


void character_refine_preprocesst::convert_constructor(conversion_input &target)
{  }

exprt character_refine_preprocesst::expr_of_char_count(exprt expr, typet type)
{
  exprt u010000=from_integer(0x010000, type);
  binary_relation_exprt small(expr, ID_lt, u010000);
  return if_exprt(small, from_integer(1, type), from_integer(2, type));
}

void character_refine_preprocesst::convert_char_count(conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_char_count, target);
}

exprt character_refine_preprocesst::expr_of_char_value(exprt expr, typet type)
{
  return typecast_exprt(expr, type);
}

void character_refine_preprocesst::convert_char_value(conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_char_value, target);
}

void character_refine_preprocesst::convert_code_point_at(
  conversion_input &target)
{
  // TODO: unimplemented
}

void character_refine_preprocesst::convert_code_point_before(conversion_input &target){  }
void character_refine_preprocesst::convert_code_point_count_char(conversion_input &target){  }
void character_refine_preprocesst::convert_code_point_count_int(conversion_input &target){  }
void character_refine_preprocesst::convert_compare(conversion_input &target){  }
void character_refine_preprocesst::convert_compare_to(conversion_input &target){  }

void character_refine_preprocesst::convert_digit_char(conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  assert(function_call.arguments().size()==2);
  exprt arg=function_call.arguments()[0];
  exprt radix=function_call.arguments()[1];
  exprt result=function_call.lhs();
  target->make_assignment();
  typet type=result.type();

  // TODO: If the radix is not in the range MIN_RADIX <= radix <= MAX_RADIX or
  // if the value of ch is not a valid digit in the specified radix,
  // -1 is returned.

  // Case 1: The method isDigit is true of the character and the Unicode
  // decimal digit value of the character (or its single-character
  // decomposition) is less than the specified radix.
  exprt invalid=from_integer(-1, arg.type());
  exprt c0=from_integer('0', arg.type());
  exprt latin_digit=in_interval_expr(arg, '0', '9');
  minus_exprt value1(arg, c0);
  // TODO: this is only valid for latin digits
  if_exprt case1(
    binary_relation_exprt(value1, ID_lt, radix), value1, invalid);

  // Case 2: The character is one of the uppercase Latin letters 'A'
  // through 'Z' and its code is less than radix + 'A' - 10,
  // then ch - 'A' + 10 is returned.
  exprt cA=from_integer('A', arg.type());
  exprt i10=from_integer(10, arg.type());
  exprt upper_case=in_interval_expr(arg, 'A', 'Z');
  plus_exprt value2(minus_exprt(arg, cA), i10);
  if_exprt case2(
    binary_relation_exprt(value2, ID_lt, radix), value2, invalid);

  // The character is one of the lowercase Latin letters 'a' through 'z' and
  // its code is less than radix + 'a' - 10, then ch - 'a' + 10 is returned.
  exprt ca=from_integer('a', arg.type());
  exprt lower_case=in_interval_expr(arg, 'a', 'z');
  plus_exprt value3(minus_exprt(arg, ca), i10);
  if_exprt case3(
    binary_relation_exprt(value3, ID_lt, radix), value3, invalid);


  // The character is one of the fullwidth uppercase Latin letters A ('\uFF21')
  // through Z ('\uFF3A') and its code is less than radix + '\uFF21' - 10.
  // In this case, ch - '\uFF21' + 10 is returned.
  exprt uFF21=from_integer(0xFF21, arg.type());
  exprt fullwidth_upper_case=in_interval_expr(arg, 0xFF21, 0xFF3A);
  plus_exprt value4(minus_exprt(arg, uFF21), i10);
  if_exprt case4(
    binary_relation_exprt(value4, ID_lt, radix), value4, invalid);

  // The character is one of the fullwidth lowercase Latin letters a ('\uFF41')
  // through z ('\uFF5A') and its code is less than radix + '\uFF41' - 10.
  // In this case, ch - '\uFF41' + 10 is returned.
  exprt uFF41=from_integer(0xFF41, arg.type());
  plus_exprt value5(minus_exprt(arg, uFF41), i10);
  if_exprt case5(
    binary_relation_exprt(value5, ID_lt, radix), value5, invalid);

  if_exprt fullwidth_cases(fullwidth_upper_case, case4, case5);
  if_exprt expr(
    latin_digit,
    case1,
    if_exprt(upper_case, case2, if_exprt(lower_case, case3, fullwidth_cases)));
  typecast_exprt tc_expr(expr, type);

  code_assignt code(result, tc_expr);
  target->code=code;
}

void character_refine_preprocesst::convert_digit_int(conversion_input &target)
{
  convert_digit_char(target);
}

void character_refine_preprocesst::convert_equals(conversion_input &target){  }

void character_refine_preprocesst::convert_for_digit(conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()==2);
  exprt digit=function_call.arguments()[0];
  exprt radix=function_call.arguments()[1];
  exprt result=function_call.lhs();
  target->make_assignment();
  typet type=result.type();

  exprt d10=from_integer(10, digit.type());
  binary_relation_exprt small(digit, ID_le, d10);
  plus_exprt value1(digit, from_integer('0', digit.type()));
  minus_exprt value2(plus_exprt(digit, from_integer('a', digit.type())), d10);
  code_assignt code(result, if_exprt(small, value1, value2));
  target->code=code;
}

void character_refine_preprocesst::convert_get_directionality_char(conversion_input &target){  }
void character_refine_preprocesst::convert_get_directionality_int(conversion_input &target){  }
void character_refine_preprocesst::convert_get_name(conversion_input &target){  }

void character_refine_preprocesst::convert_get_numeric_value_char(
  conversion_input &target)
{
  // TODO: this is only for ASCII characters
  convert_digit_char(target);
}

void character_refine_preprocesst::convert_get_numeric_value_int(
  conversion_input &target)
{
  // TODO: this is only for ASCII characters
  convert_digit_int(target);
}

void character_refine_preprocesst::convert_get_type_char(conversion_input &target){  }
void character_refine_preprocesst::convert_get_type_int(conversion_input &target){  }

void character_refine_preprocesst::convert_hash_code(conversion_input &target)
{
  convert_char_value(target);
}

exprt character_refine_preprocesst::expr_of_high_surrogate(
  exprt expr, typet type)
{
  exprt u10000=from_integer(0x010000, type);
  exprt uD800=from_integer(0xD800, type);
  exprt u400=from_integer(0x0400, type);

  plus_exprt high_surrogate(uD800, div_exprt(minus_exprt(expr, u10000), u400));
  return high_surrogate;
}

void character_refine_preprocesst::convert_high_surrogate(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_high_surrogate, target);
}

exprt character_refine_preprocesst::expr_of_is_lower_case(exprt chr, typet type)
{
  return typecast_exprt(in_interval_expr(chr, 'a', 'z'), type);
}

exprt character_refine_preprocesst::expr_of_is_upper_case(exprt chr, typet type)
{
  return typecast_exprt(in_interval_expr(chr, 'A', 'Z'), type);
}

// TODO: this is only for ASCII characters, the following are not yet
// considered: TITLECASE_LETTER MODIFIER_LETTER OTHER_LETTER LETTER_NUMBER
exprt character_refine_preprocesst::expr_of_is_letter(exprt chr, typet type)
{
  return or_exprt(
    expr_of_is_upper_case(chr, type), expr_of_is_lower_case(chr, type));
}

exprt character_refine_preprocesst::expr_of_is_alphabetic(
  exprt expr, typet type)
{
  return expr_of_is_letter(expr, type);
}

void character_refine_preprocesst::convert_is_alphabetic(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_alphabetic, target);
}

exprt character_refine_preprocesst::expr_of_is_bmp_code_point(
  exprt expr, typet type)
{
  binary_relation_exprt is_bmp(expr, ID_le, from_integer(0xFFFF, expr.type()));
  return typecast_exprt(is_bmp, type);
}

void character_refine_preprocesst::convert_is_bmp_code_point(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_bmp_code_point, target);
}

void character_refine_preprocesst::convert_is_defined_char(
  conversion_input &target)
{
  // TODO: unimplemented
}

void character_refine_preprocesst::convert_is_defined_int(
  conversion_input &target)
{
  // TODO: unimplemented
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_is_digit_char

  Inputs: a position in a goto program

 Purpose: Determines if a character is a digit.
Some Unicode character ranges that contain digits:
'\u0030' through '\u0039', ISO-LATIN-1 digits ('0' through '9')
'\u0660' through '\u0669', Arabic-Indic digits
'\u06F0' through '\u06F9', Extended Arabic-Indic digits
'\u0966' through '\u096F', Devanagari digits
'\uFF10' through '\uFF19', Fullwidth digits

Many other character ranges contain digits as well.
TODO: for no we only support these ranges of digits

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_digit(exprt chr, typet type)
{
  exprt latin_digit=in_interval_expr(chr, '0', '9');
  exprt arabic_indic_digit=in_interval_expr(chr, 0x660, 0x669);
  exprt extended_digit=in_interval_expr(chr, 0x6F0, 0x6F9);
  exprt devanagari_digit=in_interval_expr(chr, 0x966, 0x96F);
  exprt fullwidth_digit=in_interval_expr(chr, 0xFF10, 0xFF19);
  or_exprt digit(
    or_exprt(latin_digit, or_exprt(arabic_indic_digit, extended_digit)),
    or_exprt(devanagari_digit, fullwidth_digit));
  return digit;
}

void character_refine_preprocesst::convert_is_digit_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_digit, target);
}

void character_refine_preprocesst::convert_is_digit_int(
  conversion_input &target)
{
  convert_is_digit_char(target);
}

exprt character_refine_preprocesst::expr_of_is_high_surrogate(
  exprt expr, typet type)
{
  return typecast_exprt(in_interval_expr(expr, 0xD800, 0xDBFF), type);
}

void character_refine_preprocesst::convert_is_high_surrogate(
    conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_high_surrogate, target);
}

void character_refine_preprocesst::convert_is_identifier_ignorable_char(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  or_exprt ignorable(
    in_interval_expr(arg, 0x0000, 0x0008),
    or_exprt(
      in_interval_expr(arg, 0x000E, 0x001B),
      in_interval_expr(arg, 0x007F, 0x009F)));

  // TODO: we ignore  the FORMAT general category value for now
  code_assignt code(result, ignorable);
  target->code=code;
}

void character_refine_preprocesst::convert_is_identifier_ignorable_int(
  conversion_input &target)
{
  convert_is_identifier_ignorable_char(target);
}

void character_refine_preprocesst::convert_is_ideographic(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()==1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  exprt is_ideograph=in_interval_expr(arg, 0x4E00, 0x9FFF);
  code_assignt code(result, is_ideograph);
}

void character_refine_preprocesst::convert_is_ISO_control_char(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()==1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  or_exprt iso(
    in_interval_expr(arg, 0x00, 0x1F), in_interval_expr(arg, 0x7F, 0x9F));

  code_assignt code(result, iso);
  target->code=code;
}

void character_refine_preprocesst::convert_is_ISO_control_int(
  conversion_input &target)
{
  convert_is_ISO_control_char(target);
}

void character_refine_preprocesst::convert_is_java_identifier_part_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_identifier_part_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_identifier_start_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_identifier_start_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_letter(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_letter_or_digit(conversion_input &target){  }

void character_refine_preprocesst::convert_is_letter_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_letter, target);
}

void character_refine_preprocesst::convert_is_letter_int(
  conversion_input &target)
{
  convert_is_letter_char(target);
}

exprt character_refine_preprocesst::expr_of_is_letter_or_digit(
  exprt chr, typet type)
{
  return or_exprt(expr_of_is_letter(chr, type), expr_of_is_digit(chr, type));
}

void character_refine_preprocesst::convert_is_letter_or_digit_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_digit, target);
}

void character_refine_preprocesst::convert_is_letter_or_digit_int(
  conversion_input &target)
{
  convert_is_letter_or_digit_char(target);
}

void character_refine_preprocesst::convert_is_lower_case_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_lower_case, target);
}

void character_refine_preprocesst::convert_is_lower_case_int(
  conversion_input &target)
{
  convert_is_lower_case_char(target);
}

void character_refine_preprocesst::convert_is_low_surrogate(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  exprt is_low_surrogate=in_interval_expr(arg, 0xDC00, 0xDFFF);
  code_assignt code(result, is_low_surrogate);
  target->code=code;
}

exprt character_refine_preprocesst::in_list_expr(
  exprt chr, std::list<mp_integer> list)
{
  exprt res=false_exprt();
  for(auto i : list)
    res=or_exprt(res, equal_exprt(chr, from_integer(i, chr.type())));
  return res;
}

exprt character_refine_preprocesst::expr_of_is_mirrored(exprt chr, typet type)
{
  return in_list_expr(chr, {0x28, 0x29, 0x3C, 0x3E, 0x5B, 0x5D, 0x7B, 0x7D});
  /* TODO : intervals:
  2045, 2046,
    207D, 207E,
      208D, 208E,
  2201, 220D,
  2211,
  2215, 2224,
  2226
  222B, 2233,
  2239,
  223B, 224C
  2252, 2255
  225F,2262
  2264, 226B*/
  // TODO : mirrored characters after 226B
}

void character_refine_preprocesst::convert_is_mirrored_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_mirrored, target);
}

void character_refine_preprocesst::convert_is_mirrored_int(
  conversion_input &target)
{
  convert_is_mirrored_char(target);
}

void character_refine_preprocesst::convert_is_space(conversion_input &target)
{
  convert_is_whitespace_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_whitespace

 Purpose: Determines if the specified character is white space according
          to Unicode (SPACE_SEPARATOR, LINE_SEPARATOR, or
            PARAGRAPH_SEPARATOR)

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_space_char(
  exprt expr, typet type)
{
  std::list<mp_integer> space_characters=
    {0x20, 0x00A0, 0x1680, 0x202F, 0x205F, 0x3000, 0x2028, 0x2029};
  exprt condition0=in_list_expr(expr, space_characters);
  exprt condition1=in_interval_expr(expr, 0x2000, 0x200A);
  return or_exprt(condition0, condition1);
}

void character_refine_preprocesst::convert_is_space_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_space_char, target);
}

void character_refine_preprocesst::convert_is_space_char_int(
  conversion_input &target)
{
  convert_is_space_char(target);
}

void character_refine_preprocesst::convert_is_supplementary_code_point(conversion_input &target){  }

exprt character_refine_preprocesst::expr_of_is_surrogate(exprt expr, typet type)
{
  return in_interval_expr(expr, 0xD800, 0xDFFF);
}

void character_refine_preprocesst::convert_is_surrogate(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_surrogate, target);
}

void character_refine_preprocesst::convert_is_surrogate_pair(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()==2);
  exprt arg0=function_call.arguments()[0];
  exprt arg1=function_call.arguments()[1];
  exprt result=function_call.lhs();
  target->make_assignment();
  exprt is_low_surrogate=in_interval_expr(arg1, 0xDC00, 0xDFFF);
  exprt is_high_surrogate=in_interval_expr(arg0, 0xD800, 0xDBFF);
  code_assignt code(result, and_exprt(is_high_surrogate, is_low_surrogate));
  target->code=code;
}

void character_refine_preprocesst::convert_is_title_case_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_title_case_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_unicode_identifier_part_char(
  conversion_input &target){  }
void character_refine_preprocesst::convert_is_unicode_identifier_part_int(
  conversion_input &target){  }
void character_refine_preprocesst::convert_is_unicode_identifier_start_char(
  conversion_input &target){  }
void character_refine_preprocesst::convert_is_unicode_identifier_start_int(
  conversion_input &target){  }

void character_refine_preprocesst::convert_is_upper_case_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_upper_case, target);
}

void character_refine_preprocesst::convert_is_upper_case_int(
  conversion_input &target)
{
  convert_is_upper_case_char(target);
}

void character_refine_preprocesst::convert_is_valid_code_point(conversion_input &target){  }

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_whitespace

 Purpose: Determines if the specified character is white space according
          to Java. It is the case when it one of the following:
          * a Unicode space character (SPACE_SEPARATOR, LINE_SEPARATOR, or
            PARAGRAPH_SEPARATOR) but is not also a non-breaking space
            ('\u00A0', '\u2007', '\u202F').
          * it is one of these U+0009  U+000A U+000B U+000C U+000D
            U+001C U+001D U+001E U+001F

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_whitespace(
  exprt expr, typet type)
{
  std::list<mp_integer> space_characters=
    {0x20, 0x1680, 0x205F, 0x3000, 0x2028, 0x2029};
  exprt condition0=in_list_expr(expr, space_characters);
  exprt condition1=in_interval_expr(expr, 0x2000, 0x2006);
  exprt condition2=in_interval_expr(expr, 0x2008, 0x200A);
  exprt condition3=in_interval_expr(expr, 0x09, 0x0D);
  exprt condition4=in_interval_expr(expr, 0x1C, 0x1F);
  return or_exprt(
    or_exprt(condition0, condition1),
    or_exprt(condition2, or_exprt(condition3, condition4)));
}

void character_refine_preprocesst::convert_is_whitespace_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_whitespace, target);
}

void character_refine_preprocesst::convert_is_whitespace_int(
  conversion_input &target)
{
  convert_is_whitespace_char(target);
}

exprt character_refine_preprocesst::expr_of_low_surrogate(
  exprt expr, typet type)
{
  exprt uDC00=from_integer(0xDC00, type);
  exprt u0400=from_integer(0x0400, type);
  return plus_exprt(uDC00, mod_exprt(expr, u0400));
}

void character_refine_preprocesst::convert_low_surrogate(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_low_surrogate, target);
}

void character_refine_preprocesst::convert_offset_by_code_points_char(conversion_input &target){  }
void character_refine_preprocesst::convert_offset_by_code_points_int(conversion_input &target){  }

exprt character_refine_preprocesst::expr_of_reverse_bytes(
  exprt expr, typet type)
{
  shl_exprt first_byte(expr, from_integer(8, type));
  lshr_exprt second_byte(expr, from_integer(8, type));
  return plus_exprt(first_byte, second_byte);
}

void character_refine_preprocesst::convert_reverse_bytes(
    conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_reverse_bytes, target);
}

void character_refine_preprocesst::convert_to_chars_char(conversion_input &target){  }
void character_refine_preprocesst::convert_to_chars_int(conversion_input &target){  }

void character_refine_preprocesst::convert_to_code_point(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()==2);
  exprt arg0=function_call.arguments()[0];
  exprt arg1=function_call.arguments()[1];
  exprt result=function_call.lhs();
  target->make_assignment();
  typet type=result.type();

  // TODO: factorize with string_constraint_generator
  exprt u010000=from_integer(0x010000, type);
  exprt u0800=from_integer(0x0800, type);
  exprt u0400=from_integer(0x0400, type);
  mult_exprt m1(mod_exprt(arg0, u0800), u0400);
  mod_exprt m2(arg1, u0400);
  plus_exprt pair_value(u010000, plus_exprt(m1, m2));
  code_assignt code(result, pair_value);
  target->code=code;
}

void character_refine_preprocesst::convert_to_lower_case_char(conversion_input &target){  }
void character_refine_preprocesst::convert_to_lower_case_int(conversion_input &target){  }
void character_refine_preprocesst::convert_to_string_char(conversion_input &target){  }
void character_refine_preprocesst::convert_to_string_static(conversion_input &target){  }
void character_refine_preprocesst::convert_to_title_case_char(conversion_input &target){  }
void character_refine_preprocesst::convert_to_title_case_int(conversion_input &target){  }
void character_refine_preprocesst::convert_to_upper_case_char(conversion_input &target){  }
void character_refine_preprocesst::convert_to_upper_case_int(conversion_input &target){  }
void character_refine_preprocesst::convert_value_of(conversion_input &target){  }

/*******************************************************************\

Function: character_refine_preprocesst::replace_character_calls

  Inputs: a function in a goto_program

 Purpose: goes through the instructions, replace function calls to character
          function by equivalent instructions

\*******************************************************************/

void character_refine_preprocesst::replace_character_calls(
  goto_functionst::function_mapt::iterator f_it)
{
  goto_programt &goto_program=f_it->second.body;

  Forall_goto_program_instructions(target, goto_program)
  {
    if(target->is_function_call())
    {
      code_function_callt &function_call=to_code_function_call(target->code);

      if(function_call.function().id()==ID_symbol)
      {
        const irep_idt &function_id=
          to_symbol_expr(function_call.function()).get_identifier();

        debug() << "function id = " << function_id << eom;
        auto it=conversion_table.find(function_id);
        if(it!=conversion_table.end())
          (it->second)(target);
      }
    }
  }
  return;
}

/*******************************************************************\

Function: character_refine_preprocesst::initialize_conversion_table

 Purpose: fill maps with correspondance from java method names to conversion
          functions

\*******************************************************************/

void character_refine_preprocesst::initialize_conversion_table()
{
  conversion_table["java::java.lang.Character.<init>()"]=
      &character_refine_preprocesst::convert_constructor;
  conversion_table["java::java.lang.Character.charCount:(I)I"]=
      &character_refine_preprocesst::convert_char_count;
  conversion_table["java::java.lang.Character.charValue:()C"]=
      &character_refine_preprocesst::convert_char_value;
  conversion_table["java::java.lang.Character.codePointAt:([CI)I"]=
      &character_refine_preprocesst::convert_code_point_at;
  conversion_table["java::java.lang.Character.codePointAt:([CII)I"]=
      &character_refine_preprocesst::convert_code_point_at;
  conversion_table["java::java.lang.Character.codePointAt:(Ljava.lang.CharSequence;I)I"]=
      &character_refine_preprocesst::convert_code_point_at;
  conversion_table["java::java.lang.Character.codePointBefore:([CI)I"]=
      &character_refine_preprocesst::convert_code_point_before;
  conversion_table["java::java.lang.Character.codePointBefore:([CII)I"]=
      &character_refine_preprocesst::convert_code_point_before;
  conversion_table["java::java.lang.Character.codePointBefore:(Ljava.lang.CharSequence;I)I"]=
      &character_refine_preprocesst::convert_code_point_before;
  conversion_table["java::java.lang.Character.codePointCount:([CII)I"]=
      &character_refine_preprocesst::convert_code_point_count_char;
  conversion_table["java::java.lang.Character.codePointCount:(Ljava.lang.CharSequence;I)I"]=
      &character_refine_preprocesst::convert_code_point_count_int;
  conversion_table["java::java.lang.Character.compare:(C)Z"]=
      &character_refine_preprocesst::convert_compare;
  conversion_table["java::java.lang.Character.compareTo:(C)Z"]=
      &character_refine_preprocesst::convert_compare_to;
  conversion_table["java::java.lang.Character.digit:(C)Z"]=
      &character_refine_preprocesst::convert_digit_char;
  conversion_table["java::java.lang.Character.digit:(C)Z"]=
      &character_refine_preprocesst::convert_digit_int;
  conversion_table["java::java.lang.Character.equals:(C)Z"]=
      &character_refine_preprocesst::convert_equals;
  conversion_table["java::java.lang.Character.forDigit:(C)Z"]=
      &character_refine_preprocesst::convert_for_digit;
  conversion_table["java::java.lang.Character.getDirectionality:(C)Z"]=
      &character_refine_preprocesst::convert_get_directionality_char;
  conversion_table["java::java.lang.Character.getDirectionality:(C)Z"]=
      &character_refine_preprocesst::convert_get_directionality_int;
  conversion_table["java::java.lang.Character.getName:(C)Z"]=
      &character_refine_preprocesst::convert_get_name;
  conversion_table["java::java.lang.Character.getNumericValue:(C)Z"]=
      &character_refine_preprocesst::convert_get_numeric_value_char;
  conversion_table["java::java.lang.Character.getNumericValue:(C)Z"]=
      &character_refine_preprocesst::convert_get_numeric_value_int;
  conversion_table["java::java.lang.Character.getType:(C)Z"]=
      &character_refine_preprocesst::convert_get_type_char;
  conversion_table["java::java.lang.Character.getType:(C)Z"]=
      &character_refine_preprocesst::convert_get_type_int;
  conversion_table["java::java.lang.Character.hashCode:(C)Z"]=
      &character_refine_preprocesst::convert_hash_code;
  conversion_table["java::java.lang.Character.highSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_high_surrogate;
  conversion_table["java::java.lang.Character.isAlphabetic:(C)Z"]=
      &character_refine_preprocesst::convert_is_alphabetic;
  conversion_table["java::java.lang.Character.isBmpCodePoint:(C)Z"]=
      &character_refine_preprocesst::convert_is_bmp_code_point;
  conversion_table["java::java.lang.Character.isDefined:(C)Z"]=
      &character_refine_preprocesst::convert_is_defined_char;
  conversion_table["java::java.lang.Character.isDefined:(C)Z"]=
      &character_refine_preprocesst::convert_is_defined_int;
  conversion_table["java::java.lang.Character.isDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_digit_char;
  conversion_table["java::java.lang.Character.isDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_digit_int;
  conversion_table["java::java.lang.Character.isHighSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_high_surrogate;
  conversion_table["java::java.lang.Character.isIdentifierIgnorable:(C)Z"]=
      &character_refine_preprocesst::convert_is_identifier_ignorable_char;
  conversion_table["java::java.lang.Character.isIdentifierIgnorable:(C)Z"]=
      &character_refine_preprocesst::convert_is_identifier_ignorable_int;
  conversion_table["java::java.lang.Character.isIdeographic:(C)Z"]=
      &character_refine_preprocesst::convert_is_ideographic;
  conversion_table["java::java.lang.Character.isISOControl:(C)Z"]=
      &character_refine_preprocesst::convert_is_ISO_control_char;
  conversion_table["java::java.lang.Character.isISOControl:(C)Z"]=
      &character_refine_preprocesst::convert_is_ISO_control_int;
  conversion_table["java::java.lang.Character.isJavaIdentifierPart:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_part_char;
  conversion_table["java::java.lang.Character.isJavaIdentifierPart:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_part_int;
  conversion_table["java::java.lang.Character.isJavaIdentifierStart:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_start_char;
  conversion_table["java::java.lang.Character.isJavaIdentifierStart:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_start_int;
  conversion_table["java::java.lang.Character.isJavaLetter:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_letter;
  conversion_table["java::java.lang.Character.isJavaLetterOrDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_letter_or_digit;
  conversion_table["java::java.lang.Character.isLetter:(C)Z"]=
      &character_refine_preprocesst::convert_is_letter_char;
  conversion_table["java::java.lang.Character.isLetter:(C)Z"]=
      &character_refine_preprocesst::convert_is_letter_int;
  conversion_table["java::java.lang.Character.isLetterOrDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_letter_or_digit_char;
  conversion_table["java::java.lang.Character.isLetterOrDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_letter_or_digit_int;
  conversion_table["java::java.lang.Character.isLowerCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_lower_case_char;
  conversion_table["java::java.lang.Character.isLowerCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_lower_case_int;
  conversion_table["java::java.lang.Character.isLowSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_low_surrogate;
  conversion_table["java::java.lang.Character.isMirrored:(C)Z"]=
      &character_refine_preprocesst::convert_is_mirrored_char;
  conversion_table["java::java.lang.Character.isMirrored:(C)Z"]=
      &character_refine_preprocesst::convert_is_mirrored_int;
  conversion_table["java::java.lang.Character.isSpace:(C)Z"]=
      &character_refine_preprocesst::convert_is_space;
  conversion_table["java::java.lang.Character.isSpaceChar:(C)Z"]=
      &character_refine_preprocesst::convert_is_space_char;
  conversion_table["java::java.lang.Character.isSpaceChar:(C)Z"]=
      &character_refine_preprocesst::convert_is_space_char_int;
  conversion_table["java::java.lang.Character.isSupplementaryCodePoint:(C)Z"]=
      &character_refine_preprocesst::convert_is_supplementary_code_point;
  conversion_table["java::java.lang.Character.isSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_surrogate;
  conversion_table["java::java.lang.Character.isSurrogatePair:(C)Z"]=
      &character_refine_preprocesst::convert_is_surrogate_pair;
  conversion_table["java::java.lang.Character.isTitleCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_title_case_char;
  conversion_table["java::java.lang.Character.isTitleCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_title_case_int;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierPart:(C)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_part_char;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierPart:(C)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_part_int;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierStart:(C)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_start_char;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierStart:(C)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_start_int;
  conversion_table["java::java.lang.Character.isUpperCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_upper_case_char;
  conversion_table["java::java.lang.Character.isUpperCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_upper_case_int;
  conversion_table["java::java.lang.Character.isValidCodePoint:(C)Z"]=
      &character_refine_preprocesst::convert_is_valid_code_point;
  conversion_table["java::java.lang.Character.isWhitespace:(C)Z"]=
      &character_refine_preprocesst::convert_is_whitespace_char;
  conversion_table["java::java.lang.Character.isWhitespace:(C)Z"]=
      &character_refine_preprocesst::convert_is_whitespace_int;
  conversion_table["java::java.lang.Character.lowSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_low_surrogate;
  conversion_table["java::java.lang.Character.offsetByCodePoints:(C)Z"]=
      &character_refine_preprocesst::convert_offset_by_code_points_char;
  conversion_table["java::java.lang.Character.offsetByCodePoints:(C)Z"]=
      &character_refine_preprocesst::convert_offset_by_code_points_int;
  conversion_table["java::java.lang.Character.reverseBytes:(C)Z"]=
      &character_refine_preprocesst::convert_reverse_bytes;
  conversion_table["java::java.lang.Character.toChars:(C)Z"]=
      &character_refine_preprocesst::convert_to_chars_char;
  conversion_table["java::java.lang.Character.toChars:(C)Z"]=
      &character_refine_preprocesst::convert_to_chars_int;
  conversion_table["java::java.lang.Character.toCodePoint:(C)Z"]=
      &character_refine_preprocesst::convert_to_code_point;
  conversion_table["java::java.lang.Character.toLowerCase:(C)Z"]=
      &character_refine_preprocesst::convert_to_lower_case_char;
  conversion_table["java::java.lang.Character.toLowerCase:(C)Z"]=
      &character_refine_preprocesst::convert_to_lower_case_int;
  conversion_table["java::java.lang.Character.toString:(C)Z"]=
      &character_refine_preprocesst::convert_to_string_char;
  conversion_table["java::java.lang.Character.toString:(C)Z"]=
      &character_refine_preprocesst::convert_to_string_static;
  conversion_table["java::java.lang.Character.toTitleCase:(C)Z"]=
      &character_refine_preprocesst::convert_to_title_case_char;
  conversion_table["java::java.lang.Character.toTitleCase:(C)Z"]=
      &character_refine_preprocesst::convert_to_title_case_int;
  conversion_table["java::java.lang.Character.toUpperCase:(C)Z"]=
      &character_refine_preprocesst::convert_to_upper_case_char;
  conversion_table["java::java.lang.Character.toUpperCase:(C)Z"]=
      &character_refine_preprocesst::convert_to_upper_case_int;
  conversion_table["java::java.lang.Character.valueOf:(C)Z"]=
      &character_refine_preprocesst::convert_value_of;
}

/*******************************************************************\

Constructor: character_refine_preprocesst::string_refine_preprocesst

     Inputs: a symbol table, goto functions, a message handler

    Purpose: process the goto function by replacing calls to string functions

\*******************************************************************/

character_refine_preprocesst::character_refine_preprocesst(
  symbol_tablet &_symbol_table,
  goto_functionst &_goto_functions,
  message_handlert &_message_handler):
    messaget(_message_handler),
    ns(_symbol_table),
    goto_functions(_goto_functions)
{
  initialize_conversion_table();
  Forall_goto_functions(it, goto_functions)
    replace_character_calls(it);
}
