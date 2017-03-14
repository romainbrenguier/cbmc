/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java Character
        library are replaced by simple expressions.

Author: Romain Brenguier

Date:   March 2017

\*******************************************************************/

#include "character_refine_preprocess.h"
#include <util/arith_tools.h>


void character_refine_preprocesst::convert_constructor(conversion_input &target)
{  }

void character_refine_preprocesst::convert_char_count(conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  assert(function_call.arguments().size()==1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  typet type=result.type();
  exprt u010000=from_integer(0x010000, type);
  binary_relation_exprt small(arg, ID_lt, u010000);
  if_exprt expr(small, from_integer(1, type), from_integer(2, type));
  code_assignt code(result, expr);
  target->code=code;
}

void character_refine_preprocesst::convert_char_value(conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  assert(function_call.arguments().size()==1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  typet type=result.type();
  typecast_exprt expr(arg, type);
  code_assignt code(result, expr);
  target->code=code;
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
  exprt c9=from_integer('9', arg.type());
  and_exprt latin_digit(
    binary_relation_exprt(arg, ID_ge, c0),
    binary_relation_exprt(arg, ID_le, c9));
  minus_exprt value1(arg, c0);
  // TODO: this is only valid for latin digits
  if_exprt case1(
    binary_relation_exprt(value1, ID_lt, radix), value1, invalid);

  // Case 2: The character is one of the uppercase Latin letters 'A'
  // through 'Z' and its code is less than radix + 'A' - 10,
  // then ch - 'A' + 10 is returned.
  exprt cA=from_integer('A', arg.type());
  exprt cZ=from_integer('Z', arg.type());
  exprt i10=from_integer(10, arg.type());
  and_exprt upper_case(
    binary_relation_exprt(arg, ID_ge, cA),
    binary_relation_exprt(arg, ID_le, cZ));
  plus_exprt value2(minus_exprt(arg, cA), i10);
  if_exprt case2(
    binary_relation_exprt(value2, ID_lt, radix), value2, invalid);

  // The character is one of the lowercase Latin letters 'a' through 'z' and
  // its code is less than radix + 'a' - 10, then ch - 'a' + 10 is returned.
  exprt ca=from_integer('a', arg.type());
  exprt cz=from_integer('z', arg.type());
  and_exprt lower_case(
    binary_relation_exprt(arg, ID_ge, ca),
    binary_relation_exprt(arg, ID_le, cz));
  plus_exprt value3(minus_exprt(arg, ca), i10);
  if_exprt case3(
    binary_relation_exprt(value3, ID_lt, radix), value3, invalid);


  // The character is one of the fullwidth uppercase Latin letters A ('\uFF21')
  // through Z ('\uFF3A') and its code is less than radix + '\uFF21' - 10.
  // In this case, ch - '\uFF21' + 10 is returned.
  exprt uFF21=from_integer(0xFF21, arg.type());
  exprt uFF3A=from_integer(0xFF3A, arg.type());
  and_exprt fullwidth_upper_case(
    binary_relation_exprt(arg, ID_ge, uFF21),
    binary_relation_exprt(arg, ID_le, uFF3A));
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

void character_refine_preprocesst::convert_high_surrogate(conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  typet type=result.type();

  exprt u010000=from_integer(0x010000, type);
  exprt uD800=from_integer(0xD800, type);
  exprt u0400=from_integer(0x0400, type);

  plus_exprt high_surrogate(
    uD800, div_exprt(minus_exprt(arg, u010000), u0400));
  exprt expr;
  code_assignt code(result, high_surrogate);
  target->code=code;
}

void character_refine_preprocesst::convert_is_alphabetic(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();

  // TODO: this is only for ASCII characters, the following are not yet
  // considered: TITLECASE_LETTER MODIFIER_LETTER OTHER_LETTER LETTER_NUMBER
  exprt cA=from_integer('A', arg.type());
  exprt cZ=from_integer('Z', arg.type());
  exprt i10=from_integer(10, arg.type());
  and_exprt upper_case(
    binary_relation_exprt(arg, ID_ge, cA),
    binary_relation_exprt(arg, ID_le, cZ));

  exprt ca=from_integer('a', arg.type());
  exprt cz=from_integer('z', arg.type());
  and_exprt lower_case(
    binary_relation_exprt(arg, ID_ge, ca),
    binary_relation_exprt(arg, ID_le, cz));

  or_exprt expr(upper_case, lower_case);
  typecast_exprt tc_expr(expr, result.type());
  code_assignt code(result, tc_expr);
  target->code=code;
}

void character_refine_preprocesst::convert_is_bmp_code_point(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  binary_relation_exprt is_bmp(arg, ID_le, from_integer(0xFFFF, arg.type()));
  code_assignt code(result, typecast_exprt(is_bmp, result.type()));
  target->code=code;
}

void character_refine_preprocesst::convert_is_defined_char(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  // TODO: unimplemented
  exprt expr;
  code_assignt code(result, expr);
  target->code=code;
}

void character_refine_preprocesst::convert_is_defined_int(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  // TODO: unimplemented
  exprt expr;
  code_assignt code(result, expr);
  target->code=code;
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
TODO: for no we only support ISO-LATIN-1 digits

\*******************************************************************/

void character_refine_preprocesst::character_refine_preprocesst::convert_is_digit_char(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  exprt u0030=from_integer(0x0030, arg.type());
  exprt u0039=from_integer(0x0039, arg.type());
  and_exprt latin_digit(
    binary_relation_exprt(arg, ID_ge, u0030),
    binary_relation_exprt(arg, ID_le, u0039));
  code_assignt code(result, latin_digit);
  target->code=code;
}

void character_refine_preprocesst::convert_is_digit_int(conversion_input &target)
{
  convert_is_digit_char(target);
}

exprt character_refine_preprocesst::in_interval_expr(
  exprt arg, mp_integer lower_bound, mp_integer upper_bound)
{
  and_exprt res(
    binary_relation_exprt(arg, ID_ge, from_integer(lower_bound, arg.type())),
    binary_relation_exprt(arg, ID_le, from_integer(upper_bound, arg.type())));
  return res;
}

void character_refine_preprocesst::convert_is_high_surrogate(
    conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  // TODO: factorize with string_constraint_generator
  exprt is_high_surrogate=in_interval_expr(arg, 0xD800, 0xDBFF);
  code_assignt code(result, is_high_surrogate);
  target->code=code;
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
  conversion_input &target){  }

void character_refine_preprocesst::convert_is_ideographic(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  and_exprt is_ideograph(
    binary_relation_exprt(arg, ID_ge, from_integer(0x4E00, arg.type())),
    binary_relation_exprt(arg, ID_le, from_integer(0x9FFF, arg.type())));
  code_assignt code(result, is_ideograph);
}

void character_refine_preprocesst::convert_is_ISO_control_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_ISO_control_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_identifier_part_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_identifier_part_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_identifier_start_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_identifier_start_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_letter(conversion_input &target){  }
void character_refine_preprocesst::convert_is_java_letter_or_digit(conversion_input &target){  }
void character_refine_preprocesst::convert_is_letter_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_letter_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_letter_or_digit_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_letter_or_digit_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_lower_case_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_lower_case_int(conversion_input &target){  }

void character_refine_preprocesst::convert_is_low_surrogate(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  // TODO: factorize with string_constraint_generator
  and_exprt is_low_surrogate(
    binary_relation_exprt(arg, ID_ge, from_integer(0xDC00, arg.type())),
    binary_relation_exprt(arg, ID_le, from_integer(0xDFFF, arg.type())));
  code_assignt code(result, is_low_surrogate);
  target->code=code;
}

void character_refine_preprocesst::convert_is_mirrored_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_mirrored_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_space(conversion_input &target){  }
void character_refine_preprocesst::convert_is_space_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_space_char_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_supplementary_code_point(conversion_input &target){  }
void character_refine_preprocesst::convert_is_surrogate(
  conversion_input &target)
{
  const code_function_callt &function_call=to_code_function_call(target->code);
  source_locationt location=function_call.source_location();
  assert(function_call.arguments().size()>=1);
  exprt arg=function_call.arguments()[0];
  exprt result=function_call.lhs();
  target->make_assignment();
  and_exprt is_surrogate(
    binary_relation_exprt(arg, ID_ge, from_integer(0xD800, arg.type())),
    binary_relation_exprt(arg, ID_le, from_integer(0xDFFF, arg.type())));
  code_assignt code(result, is_surrogate);
  target->code=code;
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
  and_exprt is_low_surrogate(
    binary_relation_exprt(arg1, ID_ge, from_integer(0xDC00, arg1.type())),
    binary_relation_exprt(arg1, ID_le, from_integer(0xDFFF, arg1.type())));
  and_exprt is_high_surrogate(
    binary_relation_exprt(arg0, ID_ge, from_integer(0xD800, arg0.type())),
    binary_relation_exprt(arg0, ID_le, from_integer(0xDBFF, arg0.type())));
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

void character_refine_preprocesst::convert_is_upper_case_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_upper_case_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_valid_code_point(conversion_input &target){  }
void character_refine_preprocesst::convert_is_whitespace_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_whitespace_int(conversion_input &target){  }
void character_refine_preprocesst::convert_low_surrogate(conversion_input &target){  }
void character_refine_preprocesst::convert_offset_by_code_points_char(conversion_input &target){  }
void character_refine_preprocesst::convert_offset_by_code_points_int(conversion_input &target){  }
void character_refine_preprocesst::convert_reverse_bytes(conversion_input &target){  }
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
  conversion_table["java::java.lang.Character.isDefined:(C)Z"]=
    &character_refine_preprocesst::convert_is_defined_char;
  conversion_table["java::java.lang.Character.isDigit:(C)Z"]=
    &character_refine_preprocesst::convert_is_digit_char;
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
