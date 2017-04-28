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

#include <util/ieee_float.h> // should get rid of this

#include <unordered_set>
#include "character_refine_preprocess.h"

class java_string_library_preprocesst:public messaget
{
public:
  void initialize_conversion_table();

  exprt code_of_function(
    const irep_idt &function_id,
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  codet replace_character_call(code_function_callt call)
  {
    return character_preprocess.replace_character_call(call);
  }

  bool add_string_type_success(
    irep_idt class_name, symbol_tablet &symbol_table);

  // TODO: these functions should go to java_types
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

  character_refine_preprocesst character_preprocess;

  typedef codet (*conversion_functiont)(
    const code_typet &, const source_locationt &, symbol_tablet &);

  typedef std::unordered_map<irep_idt, irep_idt, irep_id_hash> id_mapt;

  // A table tells us what method to call for each java method signature
  std::unordered_map<irep_idt, conversion_functiont, irep_id_hash>
    conversion_table;

  // Some Java functions have an equivalent in the solver that we will
  // call with the same argument and will return the same result
  id_mapt cprover_equivalent_to_java_function;

  // Some Java functions have an equivalent except that they should
  // return Java Strings instead of string_exprt
  id_mapt cprover_equivalent_to_java_string_returning_function;

  // Some Java initialization function initialize strings with the
  // same result as some function of the solver
  id_mapt cprover_equivalent_to_java_initialization_function;

  // Some Java functions have an equivalent in the solver except that
  // in addition they assign the result to the object on which it is called
  id_mapt cprover_equivalent_to_java_assign_and_return_function;

  // Some Java functions have an equivalent in the solver except that
  // they assign the result to the object on which it is called instead
  // of returning it
  id_mapt cprover_equivalent_to_java_assign_function;

  // A set tells us what java types should be considered as string objects
  std::unordered_set<irep_idt, irep_id_hash> string_types;

  // Conversion functions
  static codet make_string_builder_append_object_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static codet make_string_builder_append_float_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static codet make_float_to_string_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static codet make_init_code(
    const code_typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static codet make_char_at_code(
      const code_typet &type,
      const source_locationt &loc,
      symbol_tablet &symbol_table);

  static codet make_string_to_char_array_code(
      const code_typet &type,
      const source_locationt &loc,
      symbol_tablet &symbol_table);

  // Auxiliary functions
  static codet code_for_scientific_notation(
    const exprt &arg,
    const ieee_float_spect &float_spec,
    const string_exprt &string_expr,
    const exprt &tmp_string,
    const refined_string_typet &refined_string_type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  // Helper functions
  static exprt::operandst process_parameters(
    const code_typet::parameterst &params,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &init_code);

  static exprt::operandst process_operands(
    const exprt::operandst &operands,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &init_code);

  static string_exprt process_char_array(
    const exprt &array_pointer,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code);

  static void declare_function(
    irep_idt function_name, const typet &type, symbol_tablet &symbol_table);

  static typet get_data_type(
    const typet &type, const symbol_tablet &symbol_table);
  static typet get_length_type(
    const typet &type, const symbol_tablet &symbol_table);
  static exprt get_data(const exprt &expr, const symbol_tablet &symbol_table);
  static exprt get_length(const exprt &expr, const symbol_tablet &symbol_table);

  static refined_string_typet refined_string_type();

  static symbol_exprt fresh_string(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static symbol_exprt fresh_array(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static string_exprt fresh_string_expr(
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static exprt fresh_string_expr_symbol(
    const source_locationt &loc,
    symbol_tablet &symbol_table);

  static exprt allocate_fresh_string(
    const typet &type,
    const source_locationt &loc,
    symbol_tablet &symbol_table,
    code_blockt &code);

  static exprt make_function_application(
      const irep_idt &function_name,
      const exprt::operandst &arguments,
      const typet &type,
      symbol_tablet &symbol_table);

  static codet code_assign_function_application(
      const exprt &lhs,
      const irep_idt &function_name,
      const exprt::operandst &arguments,
      symbol_tablet &symbol_table);

  static codet code_return_function_application(
      const irep_idt &function_name,
      const exprt::operandst &arguments,
      const typet &type,
      symbol_tablet &symbol_table);

  static codet code_assign_function_to_string_expr(
      const string_exprt &string_expr,
      const irep_idt &function_name,
      const exprt::operandst &arguments,
      symbol_tablet &symbol_table);

  static codet code_assign_string_expr_to_java_string(
    const exprt &lhs, const string_exprt &rhs, symbol_tablet &symbol_table);

  static codet code_assign_java_string_to_string_expr(
    const string_exprt &lhs, const exprt &rhs, symbol_tablet &symbol_table);

  static codet code_assign_string_literal_to_string_expr(
    const string_exprt &lhs,
    const exprt &tmp_string,
    const std::string &s,
    symbol_tablet &symbol_table);

  void add_string_type(const irep_idt &class_name, symbol_tablet &symbol_table);

  static exprt string_literal(const std::string &s);

  static codet make_function_from_call(
      const irep_idt &function_name,
      const code_typet &type,
      const source_locationt &loc,
      symbol_tablet &symbol_table);

  static codet make_init_function_from_call(
      const irep_idt &function_name,
      const code_typet &type,
      const source_locationt &loc,
      symbol_tablet &symbol_table,
      bool ignore_first_arg=true);

  static codet make_assign_and_return_function_from_call(
      const irep_idt &function_name,
      const code_typet &type,
      const source_locationt &loc,
      symbol_tablet &symbol_table);

  static codet make_assign_function_from_call(
      const irep_idt &function_name,
      const code_typet &type,
      const source_locationt &loc,
      symbol_tablet &symbol_table);

  static codet make_string_returning_function_from_call(
      const irep_idt &function_name,
      const code_typet &type,
      const source_locationt &loc,
      symbol_tablet &symbol_table);

};

#endif // CPROVER_JAVA_BYTECODE_JAVA_STRING_LIBRARIES_PREPROCESS_H
