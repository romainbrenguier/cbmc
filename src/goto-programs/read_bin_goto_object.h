/*******************************************************************\

Module: Read goto object files.

Author: CM Wintersteiger

Date: May 2007

\*******************************************************************/

/// \file
/// Read goto object files.

#ifndef CPROVER_GOTO_PROGRAMS_READ_BIN_GOTO_OBJECT_H
#define CPROVER_GOTO_PROGRAMS_READ_BIN_GOTO_OBJECT_H

#include <iosfwd>
#include <string>
#include <util/guard.h>

class symbol_tablet;
class goto_functionst;
class message_handlert;

bool read_bin_goto_object(
  std::istream &in,
  const std::string &filename,
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  guard_managert &guard_manager,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_READ_BIN_GOTO_OBJECT_H
