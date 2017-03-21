/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java Character
        library are replaced by simple expressions.
        For now support is limited to character in the ASCII range,
        some methods may have incorrect specifications outside of this range.

Author: Romain Brenguier

Date:   March 2017

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_CHARACTER_REFINE_PREPROCESS_H
#define CPROVER_GOTO_PROGRAMS_CHARACTER_REFINE_PREPROCESS_H

#include <goto-programs/goto_model.h>
#include <util/ui_message.h>

class character_refine_preprocesst:public messaget
{
public:
  character_refine_preprocesst(
    symbol_tablet &, goto_functionst &, message_handlert &);

private:
  namespacet ns;
  goto_functionst &goto_functions;

  void replace_character_calls(goto_functionst::function_mapt::iterator f_it);

  // A table tells us what method to call for each java method signature
  typedef goto_programt::targett conversion_input;
  typedef void (*conversion_functiont)(conversion_input &target);
  std::unordered_map<irep_idt, conversion_functiont, irep_id_hash>
    conversion_table;
  void initialize_conversion_table();

  // Conversion functions
  static exprt expr_of_char_count(const exprt &chr, const typet &type);
  static void convert_char_count(conversion_input &target);
  static exprt expr_of_char_value(const exprt &chr, const typet &type);
  static void convert_char_value(conversion_input &target);
  static void convert_compare(conversion_input &target);
  static void convert_digit_char(conversion_input &target);
  static void convert_digit_int(conversion_input &target);
  static void convert_for_digit(conversion_input &target);
  static void convert_get_directionality_char(conversion_input &target);
  static void convert_get_directionality_int(conversion_input &target);
  static void convert_get_numeric_value_char(conversion_input &target);
  static void convert_get_numeric_value_int(conversion_input &target);
  static void convert_get_type_char(conversion_input &target);
  static void convert_get_type_int(conversion_input &target);
  static void convert_hash_code(conversion_input &target);
  static exprt expr_of_high_surrogate(const exprt &chr, const typet &type);
  static void convert_high_surrogate(conversion_input &target);
  static exprt expr_of_is_alphabetic(const exprt &chr, const typet &type);
  static void convert_is_alphabetic(conversion_input &target);
  static exprt expr_of_is_bmp_code_point(const exprt &chr, const typet &type);
  static void convert_is_bmp_code_point(conversion_input &target);
  static exprt expr_of_is_defined(const exprt &chr, const typet &type);
  static void convert_is_defined_char(conversion_input &target);
  static void convert_is_defined_int(conversion_input &target);
  static exprt expr_of_is_digit(const exprt &chr, const typet &type);
  static void convert_is_digit_char(conversion_input &target);
  static void convert_is_digit_int(conversion_input &target);
  static exprt expr_of_is_high_surrogate(const exprt &chr, const typet &type);
  static void convert_is_high_surrogate(conversion_input &target);
  static exprt expr_of_is_identifier_ignorable(
    const exprt &chr, const typet &type);
  static void convert_is_identifier_ignorable_char(conversion_input &target);
  static void convert_is_identifier_ignorable_int(conversion_input &target);
  static void convert_is_ideographic(conversion_input &target);
  static void convert_is_ISO_control_char(conversion_input &target);
  static void convert_is_ISO_control_int(conversion_input &target);
  static void convert_is_java_identifier_part_char(conversion_input &target);
  static void convert_is_java_identifier_part_int(conversion_input &target);
  static void convert_is_java_identifier_start_char(conversion_input &target);
  static void convert_is_java_identifier_start_int(conversion_input &target);
  static void convert_is_java_letter(conversion_input &target);
  static void convert_is_java_letter_or_digit(conversion_input &target);
  static exprt expr_of_is_letter(const exprt &chr, const typet &type);
  static void convert_is_letter_char(conversion_input &target);
  static void convert_is_letter_int(conversion_input &target);
  static exprt expr_of_is_letter_or_digit(const exprt &chr, const typet &type);
  static void convert_is_letter_or_digit_char(conversion_input &target);
  static void convert_is_letter_or_digit_int(conversion_input &target);
  static exprt expr_of_is_ascii_lower_case(const exprt &chr, const typet &type);
  static void convert_is_lower_case_char(conversion_input &target);
  static void convert_is_lower_case_int(conversion_input &target);
  static void convert_is_low_surrogate(conversion_input &target);
  static exprt expr_of_is_mirrored(const exprt &chr, const typet &type);
  static void convert_is_mirrored_char(conversion_input &target);
  static void convert_is_mirrored_int(conversion_input &target);
  static void convert_is_space(conversion_input &target);
  static exprt expr_of_is_space_char(const exprt &chr, const typet &type);
  static void convert_is_space_char(conversion_input &target);
  static void convert_is_space_char_int(conversion_input &target);
  static exprt expr_of_is_supplementary_code_point(
    const exprt &chr, const typet &type);
  static void convert_is_supplementary_code_point(conversion_input &target);
  static exprt expr_of_is_surrogate(const exprt &chr, const typet &type);
  static void convert_is_surrogate(conversion_input &target);
  static void convert_is_surrogate_pair(conversion_input &target);
  static exprt expr_of_is_title_case(const exprt &chr, const typet &type);
  static void convert_is_title_case_char(conversion_input &target);
  static void convert_is_title_case_int(conversion_input &target);
  static exprt expr_of_is_letter_number(const exprt &chr, const typet &type);
  static exprt expr_of_is_unicode_identifier_part(
    const exprt &chr, const typet &type);
  static void convert_is_unicode_identifier_part_char(conversion_input &target);
  static void convert_is_unicode_identifier_part_int(conversion_input &target);
  static exprt expr_of_is_unicode_identifier_start(
    const exprt &chr, const typet &type);
  static void convert_is_unicode_identifier_start_char(
    conversion_input &target);
  static void convert_is_unicode_identifier_start_int(conversion_input &target);
  static exprt expr_of_is_ascii_upper_case(const exprt &chr, const typet &type);
  static void convert_is_upper_case_char(conversion_input &target);
  static void convert_is_upper_case_int(conversion_input &target);
  static exprt expr_of_is_valid_code_point(const exprt &chr, const typet &type);
  static void convert_is_valid_code_point(conversion_input &target);
  static exprt expr_of_is_whitespace(const exprt &chr, const typet &type);
  static void convert_is_whitespace_char(conversion_input &target);
  static void convert_is_whitespace_int(conversion_input &target);
  static exprt expr_of_low_surrogate(const exprt &chr, const typet &type);
  static void convert_low_surrogate(conversion_input &target);
  static exprt expr_of_reverse_bytes(const exprt &chr, const typet &type);
  static void convert_reverse_bytes(conversion_input &target);
  static exprt expr_of_to_chars(const exprt &chr, const typet &type);
  static void convert_to_chars(conversion_input &target);
  static void convert_to_code_point(conversion_input &target);
  static exprt expr_of_to_lower_case(const exprt &chr, const typet &type);
  static void convert_to_lower_case_char(conversion_input &target);
  static void convert_to_lower_case_int(conversion_input &target);
  static exprt expr_of_to_title_case(const exprt &chr, const typet &type);
  static void convert_to_title_case_char(conversion_input &target);
  static void convert_to_title_case_int(conversion_input &target);
  static exprt expr_of_to_upper_case(const exprt &chr, const typet &type);
  static void convert_to_upper_case_char(conversion_input &target);
  static void convert_to_upper_case_int(conversion_input &target);

  // Helper functions
  static void convert_char_function(
      exprt (*expr_function)(const exprt &chr, const typet &type),
      conversion_input &target);
  static exprt in_interval_expr(
    const exprt &chr, mp_integer lower_bound, mp_integer upper_bound);
  static exprt in_list_expr(
    const exprt &chr, const std::list<mp_integer> &list);
};

#endif // CPROVER_GOTO_PROGRAMS_CHARACTER_REFINE_PREPROCESS_H
