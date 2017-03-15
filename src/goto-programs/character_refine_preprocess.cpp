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

  Inputs:
    arg - Expression we want to bound
    lower_bound - Integer lower bound
    upper_bound - Integer upper bound

 Outputs: A Boolean expression

 Purpose: The returned expression is true when the first argument is in the
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

  Inputs:
    expr_function - A reference to a function on expressions
    target - A position in a goto program

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

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_function

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A integer expression of the given type

 Purpose: Determines the number of char values needed to represent
          the specified character (Unicode code point).

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_char_count(exprt expr, typet type)
{
  exprt u010000=from_integer(0x010000, type);
  binary_relation_exprt small(expr, ID_lt, u010000);
  return if_exprt(small, from_integer(1, type), from_integer(2, type));
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_is_digit_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.charCount:(I)I

\*******************************************************************/

void character_refine_preprocesst::convert_char_count(conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_char_count, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_char_value
  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Casts the given expression to the given type

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_char_value(exprt expr, typet type)
{
  return typecast_exprt(expr, type);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_value

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.charValue:()C

\*******************************************************************/

void character_refine_preprocesst::convert_char_value(conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_char_value, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_compare

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.compare:(CC)I

\*******************************************************************/

void character_refine_preprocesst::convert_compare(conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  assert(function_call.arguments().size()==2);
  exprt char1=function_call.arguments()[0];
  exprt char2=function_call.arguments()[1];
  exprt result=function_call.lhs();
  target->make_assignment();
  typet type=result.type();
  binary_relation_exprt smaller(char1, ID_lt, char2);
  binary_relation_exprt greater(char1, ID_gt, char2);
  if_exprt expr(
    smaller,
    from_integer(-1, type),
    if_exprt(greater, from_integer(1, type), from_integer(0, type)));

  code_assignt code(result, expr);
  target->code=code;
}


/*******************************************************************\

Function: character_refine_preprocesst::convert_digit_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.digit:(CI)I

\*******************************************************************/

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

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_is_digit_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.digit:(II)I

\*******************************************************************/

void character_refine_preprocesst::convert_digit_int(conversion_input &target)
{
  convert_digit_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_for_digit

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.forDigit:(II)I

\*******************************************************************/

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

/*******************************************************************\

Function: character_refine_preprocesst::convert_get_directionality_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.getDirectionality:(C)I

\*******************************************************************/

void character_refine_preprocesst::convert_get_directionality_char(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_is_digit_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.getDirectionality:(I)I

\*******************************************************************/

void character_refine_preprocesst::convert_get_directionality_int(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_get_name

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method
          Character.getName:(I)Ljava.lang.String;

\*******************************************************************/

void character_refine_preprocesst::convert_get_name(conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_get_numeric_value_char
  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.getNumericValue:(C)I

    TODO: For now this is only for ASCII characters

\*******************************************************************/

void character_refine_preprocesst::convert_get_numeric_value_char(
  conversion_input &target)
{
  convert_digit_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_get_numeric_value_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.getNumericValue:(C)I

    TODO: For now this is only for ASCII characters

\*******************************************************************/

void character_refine_preprocesst::convert_get_numeric_value_int(
  conversion_input &target)
{
  convert_digit_int(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_get_type_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.getType:(C)I

\*******************************************************************/

void character_refine_preprocesst::convert_get_type_char(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_get_type_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.getType:(I)I

\*******************************************************************/

void character_refine_preprocesst::convert_get_type_int(
  conversion_input &target)
{
  convert_get_type_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_hash_code

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.hasCode:()I

\*******************************************************************/

void character_refine_preprocesst::convert_hash_code(conversion_input &target)
{
  convert_char_value(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_high_surrogate

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Returns the leading surrogate (a high surrogate code unit)
          of the surrogate pair representing the specified
          supplementary character (Unicode code point) in the UTF-16
          encoding.

\*******************************************************************/

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

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_ascii_lower_case

  Inputs:
    chr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines if the specified character is an ASCII lowercase
          character.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_ascii_lower_case(
  exprt chr, typet type)
{
  return typecast_exprt(in_interval_expr(chr, 'a', 'z'), type);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_ascii_upper_case

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines if the specified character is an ASCII uppercase
          character.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_ascii_upper_case(
  exprt chr, typet type)
{
  return typecast_exprt(in_interval_expr(chr, 'A', 'Z'), type);
}


/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_letter

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines if the specified character is a letter.

    TODO: for now this is only for ASCII characters, the
          following unicode categories are not yet considered:
          TITLECASE_LETTER MODIFIER_LETTER OTHER_LETTER LETTER_NUMBER

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_letter(exprt chr, typet type)
{
  return or_exprt(
    expr_of_is_ascii_upper_case(chr, type),
    expr_of_is_ascii_lower_case(chr, type));
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_alphabetic

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines if the specified character (Unicode code point)
          is alphabetic.

    TODO: for now this is only for ASCII characters, the
          following unicode categorise are not yet considered:
          TITLECASE_LETTER MODIFIER_LETTER OTHER_LETTER LETTER_NUMBER
          and contributory property Other_Alphabetic as defined by the
          Unicode Standard.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_alphabetic(
  exprt expr, typet type)
{
  return expr_of_is_letter(expr, type);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_alphabetic

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isAlphabetic:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_alphabetic(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_alphabetic, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_bmp_code_point

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines whether the specified character (Unicode code
          point) is in the Basic Multilingual Plane (BMP). Such code
          points can be represented using a single char.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_bmp_code_point(
  exprt expr, typet type)
{
  binary_relation_exprt is_bmp(expr, ID_le, from_integer(0xFFFF, expr.type()));
  return typecast_exprt(is_bmp, type);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_bmp_code_point

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isBmpCodePoint:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_bmp_code_point(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_bmp_code_point, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_defined_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isDefined:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_defined_char(
  conversion_input &target)
{
  // TODO: unimplemented
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_is_digit_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isDefined:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_defined_int(
  conversion_input &target)
{
  convert_is_defined_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_digit

  Inputs:
    chr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines if the specified character is a digit.
          A character is a digit if its general category type,
          provided by Character.getType(ch), is DECIMAL_DIGIT_NUMBER.

   TODO: for now we only support these ranges of digits:
         '\u0030' through '\u0039', ISO-LATIN-1 digits ('0' through '9')
         '\u0660' through '\u0669', Arabic-Indic digits
         '\u06F0' through '\u06F9', Extended Arabic-Indic digits
         '\u0966' through '\u096F', Devanagari digits
         '\uFF10' through '\uFF19', Fullwidth digits
         Many other character ranges contain digits as well.

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

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_digit_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isDigit:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_digit_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_digit, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_digit_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.digit:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_digit_int(
  conversion_input &target)
{
  convert_is_digit_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_high_surrogate

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines if the given char value is a Unicode
          high-surrogate code unit (also known as leading-surrogate
          code unit).

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_high_surrogate(
  exprt expr, typet type)
{
  return typecast_exprt(in_interval_expr(expr, 0xD800, 0xDBFF), type);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_high_surrogate

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isHighSurrogate:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_high_surrogate(
    conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_high_surrogate, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_identifier_ignorable_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method
          Character.isIdentifierIgnorable:(C)Z

    TODO: For now, we ignore  the FORMAT general category value

\*******************************************************************/

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

  code_assignt code(result, ignorable);
  target->code=code;
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_identifier_ignorable_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method
          Character.isIdentifierIgnorable:(I)Z

    TODO: For now, we ignore  the FORMAT general category value

\*******************************************************************/

void character_refine_preprocesst::convert_is_identifier_ignorable_int(
  conversion_input &target)
{
  convert_is_identifier_ignorable_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_ideographic

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isIdeographic:(C)Z

\*******************************************************************/

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

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_ISO_control_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isISOControl:(C)Z

\*******************************************************************/

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

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_ISO_control_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isISOControl:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_ISO_control_int(
  conversion_input &target)
{
  convert_is_ISO_control_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_java_identifier_part_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isJavaIdentifierPart:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_java_identifier_part_char(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_is_digit_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method isJavaIdentifierPart:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_java_identifier_part_int(
  conversion_input &target)
{
  convert_is_java_identifier_part_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_java_identifier_start_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method isJavaIdentifierStart:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_java_identifier_start_char(
    conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_char_is_digit_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method isJavaIdentifierStart:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_java_identifier_start_int(
  conversion_input &target)
{
  convert_is_java_identifier_start_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_java_letter

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isJavaLetter:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_java_letter(
    conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_java_letter_or_digit

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method isJavaLetterOrDigit:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_java_letter_or_digit(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_letter_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isLetter:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_letter_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_letter, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_letter_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isLetter:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_letter_int(
  conversion_input &target)
{
  convert_is_letter_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_letter_or_digit

  Inputs:
    chr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines if the specified character is a letter or digit.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_letter_or_digit(
  exprt chr, typet type)
{
  return or_exprt(expr_of_is_letter(chr, type), expr_of_is_digit(chr, type));
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_letter_or_digit_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isLetterOrDigit:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_letter_or_digit_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_digit, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_letter_or_digit_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isLetterOrDigit:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_letter_or_digit_int(
  conversion_input &target)
{
  convert_is_letter_or_digit_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_lower_case_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isLowerCase:(C)Z

    TODO: For now we only consider ASCII characters

\*******************************************************************/

void character_refine_preprocesst::convert_is_lower_case_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_ascii_lower_case, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_lower_case_int()

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isLowerCase:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_lower_case_int(
  conversion_input &target)
{
  convert_is_lower_case_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_low_surrogate

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isLowSurrogate:(I)Z

\*******************************************************************/

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

/*******************************************************************\

Function: character_refine_preprocesst::in_list_expr

  Inputs:
    chr - An expression of type character
    list - A list of integer representing unicode characters

 Outputs: A Boolean expression

 Purpose: The returned expression is true when the given character
          is equal to one of the element in the list

\*******************************************************************/

exprt character_refine_preprocesst::in_list_expr(
  exprt chr, std::list<mp_integer> list)
{
  exprt res=false_exprt();
  for(auto i : list)
    res=or_exprt(res, equal_exprt(chr, from_integer(i, chr.type())));
  return res;
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_mirrored

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: An expression of the given type

 Purpose: Determines whether the character is mirrored according to
          the Unicode specification.

    TODO: For now only ASCII characters are considered

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_mirrored(exprt chr, typet type)
{
  return in_list_expr(chr, {0x28, 0x29, 0x3C, 0x3E, 0x5B, 0x5D, 0x7B, 0x7D});
 }

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_mirrored_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isMirrored:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_mirrored_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_mirrored, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_mirrored_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isMirrored:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_mirrored_int(
  conversion_input &target)
{
  convert_is_mirrored_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_space

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isSpace:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_space(conversion_input &target)
{
  convert_is_whitespace_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_space_char

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A Boolean expression

 Purpose: Determines if the specified character is white space
          according to Unicode (SPACE_SEPARATOR, LINE_SEPARATOR, or
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

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_space_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isSpaceChar:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_space_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_space_char, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_space_char_int()

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isSpaceChar:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_space_char_int(
  conversion_input &target)
{
  convert_is_space_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_supplementary_code_point

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A Boolean expression

 Purpose: Determines whether the specified character (Unicode code
          point) is in the supplementary character range.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_supplementary_code_point(
  exprt expr, typet type)
{
  return binary_relation_exprt(expr, ID_gt, from_integer(0xFFFF, expr.type()));
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_supplementary_code_point

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method
          Character.isSupplementaryCodePoint:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_supplementary_code_point(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_supplementary_code_point, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_surrogate

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A Boolean expression

 Purpose: Determines if the given char value is a Unicode surrogate
          code unit.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_surrogate(exprt expr, typet type)
{
  return in_interval_expr(expr, 0xD800, 0xDFFF);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_surrogate

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isSurrogate:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_surrogate(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_surrogate, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_surrogate_pair

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isSurrogatePair:(CC)Z

\*******************************************************************/

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

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_title_case

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A Boolean expression

 Purpose: Determines if the specified character is a titlecase character.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_title_case(exprt expr, typet type)
{
  std::list<mp_integer>title_case_chars=
    {0x01C5, 0x01C8, 0x01CB, 0x01F2, 0x1FBC, 0x1FCC, 0x1FFC};

  exprt condition0=in_list_expr(expr, title_case_chars);
  exprt condition1=in_interval_expr(expr, 0x1F88, 0x1F8F);
  exprt condition2=in_interval_expr(expr, 0x1F98, 0x1F9F);
  exprt condition3=in_interval_expr(expr, 0x1FA8, 0x1FAF);
  return or_exprt(
    or_exprt(condition0, condition1), or_exprt(condition2, condition3));
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_title_case_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isTitleCase:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_title_case_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_title_case, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_title_case_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isTitleCase:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_title_case_int(
  conversion_input &target)
{
  convert_is_title_case_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_letter_number

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A Boolean expression

 Purpose: Determines if the specified character is in the LETTER_NUMBER
          category of Unicode

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_letter_number(
  exprt expr, typet type)
{

  // The following set of characters is the general category "Nl" in the
  // Unicode specification.
  exprt cond0=in_interval_expr(expr, 0x16EE, 0x16F0);
  exprt cond1=in_interval_expr(expr, 0x2160, 0x2188);
  exprt cond2=in_interval_expr(expr, 0x3021, 0x3029);
  exprt cond3=in_interval_expr(expr, 0x3038, 0x303A);
  exprt cond4=in_interval_expr(expr, 0xA6E6, 0xA6EF);
  exprt cond5=in_interval_expr(expr, 0x10140, 0x10174);
  exprt cond6=in_interval_expr(expr, 0x103D1, 0x103D5);
  exprt cond7=in_interval_expr(expr, 0x12400, 0x1246E);
  exprt cond8=in_list_expr(expr, {0x3007, 0x10341, 0x1034A});
  return or_exprt(
    or_exprt(or_exprt(cond0, cond1), or_exprt(cond2, cond3)),
    or_exprt(or_exprt(cond4, cond5), or_exprt(cond6, or_exprt(cond7, cond8))));
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_unicode_identifier_part_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method
          Character.isUnicodeIdentifierPart:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_unicode_identifier_part_char(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_unicode_identifier_part_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method
          Character.isUnicodeIdentifierPart:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_unicode_identifier_part_int(
  conversion_input &target)
{
  convert_is_unicode_identifier_part_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_unicode_identifier_start

  Inputs:
    chr - An expression of type character
    type - A type for the output

 Outputs: A Boolean expression

 Purpose: Determines if the specified character is permissible as the
          first character in a Unicode identifier.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_is_unicode_identifier_start(
  exprt chr, typet type)
{
  return or_exprt(
    expr_of_is_letter(chr, type), expr_of_is_letter_number(chr, type));
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_unicode_identifier_start_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method
          Character.isUnicodeIdentifierStart:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_unicode_identifier_start_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_unicode_identifier_start, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_unicode_identifier_start_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method
          Character.isUnicodeIdentifierStart:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_unicode_identifier_start_int(
  conversion_input &target)
{
  convert_is_unicode_identifier_start_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_upper_case_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isUpperCase:(C)Z

    TODO: For now we only consider ASCII characters

\*******************************************************************/

void character_refine_preprocesst::convert_is_upper_case_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_ascii_upper_case, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_upper_case_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isUpperCase:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_upper_case_int(
  conversion_input &target)
{
  convert_is_upper_case_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_valid_code_point

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isValidCodePoint:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_valid_code_point(
    conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_is_whitespace

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A Boolean expression

 Purpose: Determines if the specified character is white space according
          to Java. It is the case when it one of the following:
          * a Unicode space character (SPACE_SEPARATOR, LINE_SEPARATOR, or
            PARAGRAPH_SEPARATOR) but is not also a non-breaking space
            ('\u00A0', '\u2007', '\u202F').
          * it is one of these: U+0009  U+000A U+000B U+000C U+000D
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

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_whitespace_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isWhitespace:(C)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_whitespace_char(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_is_whitespace, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_is_whitespace_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.isWhitespace:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_is_whitespace_int(
  conversion_input &target)
{
  convert_is_whitespace_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_low_surrogate

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A integer expression of the given type

 Purpose: Returns the trailing surrogate (a low surrogate code unit)
          of the surrogate pair representing the specified
          supplementary character (Unicode code point) in the UTF-16
          encoding.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_low_surrogate(
  exprt expr, typet type)
{
  exprt uDC00=from_integer(0xDC00, type);
  exprt u0400=from_integer(0x0400, type);
  return plus_exprt(uDC00, mod_exprt(expr, u0400));
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_low_surrogate

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.lowSurrogate:(I)Z

\*******************************************************************/

void character_refine_preprocesst::convert_low_surrogate(
  conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_low_surrogate, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::expr_of_reverse_bytes

  Inputs:
    expr - An expression of type character
    type - A type for the output

 Outputs: A character expression of the given type

 Purpose: Returns the value obtained by reversing the order of the
          bytes in the specified char value.

\*******************************************************************/

exprt character_refine_preprocesst::expr_of_reverse_bytes(
  exprt expr, typet type)
{
  shl_exprt first_byte(expr, from_integer(8, type));
  lshr_exprt second_byte(expr, from_integer(8, type));
  return plus_exprt(first_byte, second_byte);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_reverse_bytes

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.reverseBytes:(C)C

\*******************************************************************/

void character_refine_preprocesst::convert_reverse_bytes(
    conversion_input &target)
{
  convert_char_function(
    &character_refine_preprocesst::expr_of_reverse_bytes, target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_to_chars

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.toChars:(I)[C

\*******************************************************************/

void character_refine_preprocesst::convert_to_chars(conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_to_code_point

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.toCodePoint:(CC)I

\*******************************************************************/

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

/*******************************************************************\

Function: character_refine_preprocesst::convert_to_lower_case_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.toLowerCase:(C)C

\*******************************************************************/

void character_refine_preprocesst::convert_to_lower_case_char(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_to_lower_case_int()

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.toLowerCase:(I)I

\*******************************************************************/

void character_refine_preprocesst::convert_to_lower_case_int(
  conversion_input &target)
{
  convert_to_lower_case_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_to_title_case_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.toTitleCase:(C)C

\*******************************************************************/

void character_refine_preprocesst::convert_to_title_case_char(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_to_title_case_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.toTitleCase:(I)I

\*******************************************************************/

void character_refine_preprocesst::convert_to_title_case_int(
  conversion_input &target)
{
  convert_to_title_case_char(target);
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_to_upper_case_char

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.toUpperCase:(C)C

\*******************************************************************/

void character_refine_preprocesst::convert_to_upper_case_char(
  conversion_input &target)
{
  // TODO
}

/*******************************************************************\

Function: character_refine_preprocesst::convert_to_upper_case_int

  Inputs:
    target - a position in a goto program

 Purpose: Converts function call to an assignement of an expression
          corresponding to the java method Character.toUpperCase:(I)I

\*******************************************************************/

void character_refine_preprocesst::convert_to_upper_case_int(
  conversion_input &target)
{
  convert_to_upper_case_char(target);
}

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

 Purpose: fill maps with correspondance from java method names to
          conversion functions

\*******************************************************************/

void character_refine_preprocesst::initialize_conversion_table()
{
  // All methods are listed here in alphabetic order
  // The ones that are not supported by this module (though they may be
  // supported by the string solver) have no entry in the conversion
  // table and are marked in this way:
  // Not supported "java::java.lang.Character.<init>()"

  conversion_table["java::java.lang.Character.charCount:(I)I"]=
      &character_refine_preprocesst::convert_char_count;
  conversion_table["java::java.lang.Character.charValue:()C"]=
      &character_refine_preprocesst::convert_char_value;

  // Not supported "java::java.lang.Character.codePointAt:([CI)I
  // Not supported "java::java.lang.Character.codePointAt:([CII)I"
  // Not supported "java::java.lang.Character.codePointAt:"
  //   "(Ljava.lang.CharSequence;I)I"
  // Not supported "java::java.lang.Character.codePointBefore:([CI)I"
  // Not supported "java::java.lang.Character.codePointBefore:([CII)I"
  // Not supported "java::java.lang.Character.codePointBefore:"
  //   "(Ljava.lang.CharSequence;I)I"
  // Not supported "java::java.lang.Character.codePointCount:([CII)I"
  // Not supported "java::java.lang.Character.codePointCount:"
  //   "(Ljava.lang.CharSequence;I)I"
  // Not supported "java::java.lang.Character.compareTo:"
  //   "(Ljava.lang.Character;)I"

  conversion_table["java::java.lang.Character.compare:(CC)I"]=
      &character_refine_preprocesst::convert_compare;
  conversion_table["java::java.lang.Character.digit:(CI)I"]=
      &character_refine_preprocesst::convert_digit_char;
  conversion_table["java::java.lang.Character.digit:(II)I"]=
      &character_refine_preprocesst::convert_digit_int;

 // Not supported "java::java.lang.Character.equals:(Ljava.lang.Object;)Z"

  conversion_table["java::java.lang.Character.forDigit:(II)C"]=
      &character_refine_preprocesst::convert_for_digit;
  // TODO: check signature
  conversion_table["java::java.lang.Character.getDirectionality:(C)I"]=
      &character_refine_preprocesst::convert_get_directionality_char;
  conversion_table["java::java.lang.Character.getDirectionality:(I)I"]=
      &character_refine_preprocesst::convert_get_directionality_int;
  conversion_table["java::java.lang.Character.getName:(I)Ljava.lang.String;"]=
      &character_refine_preprocesst::convert_get_name;
  conversion_table["java::java.lang.Character.getNumericValue:(C)I"]=
      &character_refine_preprocesst::convert_get_numeric_value_char;
  conversion_table["java::java.lang.Character.getNumericValue:(I)I"]=
      &character_refine_preprocesst::convert_get_numeric_value_int;
  conversion_table["java::java.lang.Character.getType:(C)I"]=
      &character_refine_preprocesst::convert_get_type_char;
  conversion_table["java::java.lang.Character.getType:(I)Z"]=
      &character_refine_preprocesst::convert_get_type_int;
  conversion_table["java::java.lang.Character.hashCode:()I"]=
      &character_refine_preprocesst::convert_hash_code;
  conversion_table["java::java.lang.Character.highSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_high_surrogate;
  conversion_table["java::java.lang.Character.isAlphabetic:(I)Z"]=
      &character_refine_preprocesst::convert_is_alphabetic;
  conversion_table["java::java.lang.Character.isBmpCodePoint:(I)Z"]=
      &character_refine_preprocesst::convert_is_bmp_code_point;
  conversion_table["java::java.lang.Character.isDefined:(C)Z"]=
      &character_refine_preprocesst::convert_is_defined_char;
  conversion_table["java::java.lang.Character.isDefined:(I)Z"]=
      &character_refine_preprocesst::convert_is_defined_int;
  conversion_table["java::java.lang.Character.isDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_digit_char;
  conversion_table["java::java.lang.Character.isDigit:(I)Z"]=
      &character_refine_preprocesst::convert_is_digit_int;
  conversion_table["java::java.lang.Character.isHighSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_high_surrogate;
  conversion_table["java::java.lang.Character.isIdentifierIgnorable:(C)Z"]=
      &character_refine_preprocesst::convert_is_identifier_ignorable_char;
  conversion_table["java::java.lang.Character.isIdentifierIgnorable:(I)Z"]=
      &character_refine_preprocesst::convert_is_identifier_ignorable_int;
  conversion_table["java::java.lang.Character.isIdeographic:(C)Z"]=
      &character_refine_preprocesst::convert_is_ideographic;
  conversion_table["java::java.lang.Character.isISOControl:(C)Z"]=
      &character_refine_preprocesst::convert_is_ISO_control_char;
  conversion_table["java::java.lang.Character.isISOControl:(I)Z"]=
      &character_refine_preprocesst::convert_is_ISO_control_int;
  conversion_table["java::java.lang.Character.isJavaIdentifierPart:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_part_char;
  conversion_table["java::java.lang.Character.isJavaIdentifierPart:(I)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_part_int;
  conversion_table["java::java.lang.Character.isJavaIdentifierStart:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_start_char;
  conversion_table["java::java.lang.Character.isJavaIdentifierStart:(I)Z"]=
      &character_refine_preprocesst::convert_is_java_identifier_start_int;
  conversion_table["java::java.lang.Character.isJavaLetter:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_letter;
  conversion_table["java::java.lang.Character.isJavaLetterOrDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_java_letter_or_digit;
  conversion_table["java::java.lang.Character.isLetter:(C)Z"]=
      &character_refine_preprocesst::convert_is_letter_char;
  conversion_table["java::java.lang.Character.isLetter:(I)Z"]=
      &character_refine_preprocesst::convert_is_letter_int;
  conversion_table["java::java.lang.Character.isLetterOrDigit:(C)Z"]=
      &character_refine_preprocesst::convert_is_letter_or_digit_char;
  conversion_table["java::java.lang.Character.isLetterOrDigit:(I)Z"]=
      &character_refine_preprocesst::convert_is_letter_or_digit_int;
  conversion_table["java::java.lang.Character.isLowerCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_lower_case_char;
  conversion_table["java::java.lang.Character.isLowerCase:(I)Z"]=
      &character_refine_preprocesst::convert_is_lower_case_int;
  conversion_table["java::java.lang.Character.isLowSurrogate:(I)Z"]=
      &character_refine_preprocesst::convert_is_low_surrogate;
  conversion_table["java::java.lang.Character.isMirrored:(C)Z"]=
      &character_refine_preprocesst::convert_is_mirrored_char;
  conversion_table["java::java.lang.Character.isMirrored:(I)Z"]=
      &character_refine_preprocesst::convert_is_mirrored_int;
  conversion_table["java::java.lang.Character.isSpace:(C)Z"]=
      &character_refine_preprocesst::convert_is_space;
  conversion_table["java::java.lang.Character.isSpaceChar:(C)Z"]=
      &character_refine_preprocesst::convert_is_space_char;
  conversion_table["java::java.lang.Character.isSpaceChar:(I)Z"]=
      &character_refine_preprocesst::convert_is_space_char_int;
  conversion_table["java::java.lang.Character.isSupplementaryCodePoint:(I)Z"]=
      &character_refine_preprocesst::convert_is_supplementary_code_point;
  conversion_table["java::java.lang.Character.isSurrogate:(C)Z"]=
      &character_refine_preprocesst::convert_is_surrogate;
  conversion_table["java::java.lang.Character.isSurrogatePair:(CC)Z"]=
      &character_refine_preprocesst::convert_is_surrogate_pair;
  conversion_table["java::java.lang.Character.isTitleCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_title_case_char;
  conversion_table["java::java.lang.Character.isTitleCase:(I)Z"]=
      &character_refine_preprocesst::convert_is_title_case_int;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierPart:(C)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_part_char;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierPart:(I)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_part_int;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierStart:(C)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_start_char;
  conversion_table["java::java.lang.Character.isUnicodeIdentifierStart:(I)Z"]=
      &character_refine_preprocesst::convert_is_unicode_identifier_start_int;
  conversion_table["java::java.lang.Character.isUpperCase:(C)Z"]=
      &character_refine_preprocesst::convert_is_upper_case_char;
  conversion_table["java::java.lang.Character.isUpperCase:(I)Z"]=
      &character_refine_preprocesst::convert_is_upper_case_int;
  conversion_table["java::java.lang.Character.isValidCodePoint:(I)Z"]=
      &character_refine_preprocesst::convert_is_valid_code_point;
  conversion_table["java::java.lang.Character.isWhitespace:(C)Z"]=
      &character_refine_preprocesst::convert_is_whitespace_char;
  conversion_table["java::java.lang.Character.isWhitespace:(I)Z"]=
      &character_refine_preprocesst::convert_is_whitespace_int;
  conversion_table["java::java.lang.Character.lowSurrogate:(I)Z"]=
      &character_refine_preprocesst::convert_is_low_surrogate;

  // Not supported "java::java.lang.Character.offsetByCodePoints:([CIIII)I"
  // Not supported "java::java.lang.Character.offsetByCodePoints:"
  //   "(Ljava.lang.CharacterSequence;II)I"

  conversion_table["java::java.lang.Character.reverseBytes:(C)C"]=
      &character_refine_preprocesst::convert_reverse_bytes;
  conversion_table["java::java.lang.Character.toChars:(I)[C"]=
      &character_refine_preprocesst::convert_to_chars;

  // Not supported "java::java.lang.Character.toChars:(I[CI])I"

  conversion_table["java::java.lang.Character.toCodePoint:(CC)I"]=
      &character_refine_preprocesst::convert_to_code_point;
  conversion_table["java::java.lang.Character.toLowerCase:(C)C"]=
      &character_refine_preprocesst::convert_to_lower_case_char;
  conversion_table["java::java.lang.Character.toLowerCase:(I)I"]=
      &character_refine_preprocesst::convert_to_lower_case_int;

  // Not supported "java::java.lang.Character.toString:()Ljava.lang.String;"
  // Not supported "java::java.lang.Character.toString:(C)Ljava.lang.String;"

  conversion_table["java::java.lang.Character.toTitleCase:(C)C"]=
      &character_refine_preprocesst::convert_to_title_case_char;
  conversion_table["java::java.lang.Character.toTitleCase:(I)I"]=
      &character_refine_preprocesst::convert_to_title_case_int;
  conversion_table["java::java.lang.Character.toUpperCase:(C)C"]=
      &character_refine_preprocesst::convert_to_upper_case_char;
  conversion_table["java::java.lang.Character.toUpperCase:(I)I"]=
      &character_refine_preprocesst::convert_to_upper_case_int;

  // Not supported "java::java.lang.Character.valueOf:(C)Ljava.lang.Character;"
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
