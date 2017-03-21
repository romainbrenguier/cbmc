/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H

#include <util/symbol_table.h>
#include <util/message.h>
#include <util/safe_pointer.h>
#include "character_refine_preprocess.h"

#include "java_bytecode_parse_tree.h"

class class_hierarchyt;

void java_bytecode_convert_method(
  const symbolt &class_symbol,
  const java_bytecode_parse_treet::methodt &,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  safe_pointer<std::vector<irep_idt> > needed_methods,
  safe_pointer<std::set<irep_idt> > needed_classes,
  const character_refine_preprocesst &character_refine);

// Must provide both the optional parameters or neither.
inline void java_bytecode_convert_method(
  const symbolt &class_symbol,
  const java_bytecode_parse_treet::methodt &method,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  size_t max_array_length,
  const character_refine_preprocesst &character_preprocess)
{
  java_bytecode_convert_method(
    class_symbol,
    method,
    symbol_table,
    message_handler,
    max_array_length,
    safe_pointer<std::vector<irep_idt> >::create_null(),
    safe_pointer<std::set<irep_idt> >::create_null(),
    character_preprocess);
}

void java_bytecode_convert_method_lazy(
  const symbolt &class_symbol,
  const irep_idt &method_identifier,
  const java_bytecode_parse_treet::methodt &,
  symbol_tablet &symbol_table);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_H
