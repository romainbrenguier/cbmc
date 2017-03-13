/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java Character
        library are replaced by simple expressions.

Author: Romain Brenguier

Date:   March 2017

\*******************************************************************/

#include "character_refine_preprocess.h"
#include <util/arith_tools.h>


void character_refine_preprocesst::convert_constructor(conversion_input &target){  }
void character_refine_preprocesst::convert_char_count(conversion_input &target){  }
void character_refine_preprocesst::convert_char_value(conversion_input &target){  }
void character_refine_preprocesst::convert_code_point_at(conversion_input &target){  }
void character_refine_preprocesst::convert_code_point_before(conversion_input &target){  }
void character_refine_preprocesst::convert_code_point_count_char(conversion_input &target){  }
void character_refine_preprocesst::convert_code_point_count_int(conversion_input &target){  }
void character_refine_preprocesst::convert_compare(conversion_input &target){  }
void character_refine_preprocesst::convert_compare_to(conversion_input &target){  }
void character_refine_preprocesst::convert_digit_char(conversion_input &target){  }
void character_refine_preprocesst::convert_digit_int(conversion_input &target){  }
void character_refine_preprocesst::convert_equals(conversion_input &target){  }
void character_refine_preprocesst::convert_for_digit(conversion_input &target){  }
void character_refine_preprocesst::convert_get_directionality_char(conversion_input &target){  }
void character_refine_preprocesst::convert_get_directionality_int(conversion_input &target){  }
void character_refine_preprocesst::convert_get_name(conversion_input &target){  }
void character_refine_preprocesst::convert_get_numeric_value_char(conversion_input &target){  }
void character_refine_preprocesst::convert_get_numeric_value_int(conversion_input &target){  }
void character_refine_preprocesst::convert_get_type_char(conversion_input &target){  }
void character_refine_preprocesst::convert_get_type_int(conversion_input &target){  }
void character_refine_preprocesst::convert_hash_code(conversion_input &target){  }
void character_refine_preprocesst::convert_high_surrogate(conversion_input &target){  }
void character_refine_preprocesst::convert_is_alphabetic(conversion_input &target){  }
void character_refine_preprocesst::convert_is_bmp_code_point(conversion_input &target){  }
void character_refine_preprocesst::convert_is_defined_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_defined_int(conversion_input &target){  }

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


void character_refine_preprocesst::convert_is_digit_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_high_surrogate(conversion_input &target){  }
void character_refine_preprocesst::convert_is_identifier_ignorable_char(
  conversion_input &target){  }
void character_refine_preprocesst::convert_is_identifier_ignorable_int(
  conversion_input &target){  }
void character_refine_preprocesst::convert_is_ideographic(conversion_input &target){  }
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
void character_refine_preprocesst::convert_is_low_surrogate(conversion_input &target){  }
void character_refine_preprocesst::convert_is_mirrored_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_mirrored_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_space(conversion_input &target){  }
void character_refine_preprocesst::convert_is_space_char(conversion_input &target){  }
void character_refine_preprocesst::convert_is_space_char_int(conversion_input &target){  }
void character_refine_preprocesst::convert_is_supplementary_code_point(conversion_input &target){  }
void character_refine_preprocesst::convert_is_surrogate(conversion_input &target){  }
void character_refine_preprocesst::convert_is_surrogate_pair(conversion_input &target){  }
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
void character_refine_preprocesst::convert_to_code_point(conversion_input &target){  }
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
    symbol_table(_symbol_table),
    goto_functions(_goto_functions)
{
  initialize_conversion_table();
  Forall_goto_functions(it, goto_functions)
    replace_character_calls(it);
}
