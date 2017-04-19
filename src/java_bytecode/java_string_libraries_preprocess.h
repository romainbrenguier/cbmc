/*******************************************************************\

Module: Preprocess a goto-programs so that calls to the java Character
        library are replaced by simple expressions.
        For now support is limited to character in the ASCII range,
        some methods may have incorrect specifications outside of this range.

Author: Romain Brenguier

Date:   March 2017

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARIES_PREPROCESS_H
#define CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARIES_PREPROCESS_H

#include <util/ui_message.h>
#include <util/std_code.h>
#include <util/symbol_table.h>
#include <util/refined_string_type.h>
#include <util/string_expr.h>

class java_string_libraries_preprocesst:public messaget
{
public:

  java_string_libraries_preprocesst(symbol_tablet _symbol_table);
  void initialize_conversion_table();

  exprt code_of_function(
    const irep_idt &function_id,
    const code_typet &type,
    const source_locationt &loc);

  static exprt::operandst process_arguments(
    const code_typet::parameterst &params, symbol_tablet &symbol_table);

  // Should these functions go to: java_types
  static bool check_java_type(const typet &type, const std::string &tag);
  static bool is_java_string_pointer_type(const typet &type);
  static bool is_java_string_type(const typet &type);
  static bool is_java_string_builder_type(const typet &type);
  static bool is_java_string_builder_pointer_type(const typet &type);
  static bool is_java_string_buffer_type(const typet &type);
  static bool is_java_string_buffer_pointer_type(const typet &type);
  static bool is_java_char_sequence_type(const typet &type);
  static bool is_java_char_sequence_pointer_type(const typet &type);
  static bool is_java_char_array_type(const typet &type);
  static bool is_java_char_array_pointer_type(const typet &type);
  static bool implements_java_char_sequence(const typet &type)
  {
      return
        is_java_char_sequence_pointer_type(type) ||
        is_java_string_builder_pointer_type(type) ||
        is_java_string_buffer_pointer_type(type) ||
        is_java_string_pointer_type(type);
  }

private:
  symbol_tablet symbol_table;

  typedef codet (*conversion_functiont)(
    const code_typet &, const source_locationt &, symbol_tablet &);

  // A table tells us what method to call for each java method signature
  std::unordered_map<irep_idt, conversion_functiont, irep_id_hash> conversion_table;

  // Conversion functions
  static codet make_string_builder_append_object_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  // Helper functions
  static void declare_function(
    irep_idt function_name, const typet &type, symbol_tablet &symbol_table);

  static symbol_exprt fresh_string(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static symbol_exprt fresh_array(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static string_exprt fresh_string_expr(
    const refined_string_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static codet code_assign_function_to_string_expr(
      const string_exprt &str,
      const irep_idt &function_name,
      const code_typet &function_type,
      const exprt::operandst &arguments,
      symbol_tablet &symbol_table);

  static codet code_assign_string_expr_to_java_string(
    const exprt &lhs, const string_exprt &rhs, symbol_tablet &symbol_table);
  static codet code_assign_java_string_to_string_expr(
    const string_exprt &lhs, const exprt &rhs, symbol_tablet &symbol_table);
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARIES_PREPROCESS_H
