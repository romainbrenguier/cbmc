/*******************************************************************\

Module: Goto Programs with Functions

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

/// \file
/// Goto Programs with Functions

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_FUNCTIONS_H
#define CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_FUNCTIONS_H

#include "goto_model.h"
#include "goto_convert_class.h"
#include "goto_functions.h"

// convert it all!
void goto_convert(
  symbol_table_baset &symbol_table,
  goto_functionst &functions,
  message_handlert &,
  guard_managert &guard_manager);

// convert it all!
void
goto_convert(goto_modelt &, message_handlert &, guard_managert &guard_manager);

// just convert a specific function
void goto_convert(
  const irep_idt &identifier,
  symbol_table_baset &symbol_table,
  goto_functionst &functions,
  message_handlert &,
  guard_managert &guard_manager);

class goto_convert_functionst:public goto_convertt
{
public:
  void goto_convert(
    goto_functionst &functions,
    guard_managert &guard_manager);
  void convert_function(
    const irep_idt &identifier,
    goto_functionst::goto_functiont &result);

  goto_convert_functionst(
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler);

  virtual ~goto_convert_functionst();

protected:
  static bool hide(const goto_programt &);

  //
  // function calls
  //
  void add_return(
    goto_functionst::goto_functiont &,
    const source_locationt &);
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_CONVERT_FUNCTIONS_H
