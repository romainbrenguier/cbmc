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

class java_string_libraries_preprocesst:public messaget
{
public:

  java_string_libraries_preprocesst(symbol_tablet _symbol_table);
  void initialize_conversion_table();

  exprt code_of_function(
    const irep_idt &function_id,
    const code_typet &type,
    const source_locationt &loc);

  codet make_string_assign(
    const code_typet &function_type,
    const irep_idt &function_name,
    const source_locationt &location);

  exprt::operandst process_arguments(code_typet::parameterst params);

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

  // A table tells us what method to call for each java method signature
  std::unordered_map<irep_idt, unsigned, irep_id_hash> conversion_table;

  // Conversion functions
  codet make_string_builder_append_object_code(
    const code_typet &type, const source_locationt &loc);

  // Helper functions
  void declare_function(irep_idt function_name, const typet &type);
  symbol_exprt fresh_string(const typet &type, const source_locationt &loc);
  symbol_exprt fresh_array(const typet &type, const source_locationt &loc);
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARIES_PREPROCESS_H
