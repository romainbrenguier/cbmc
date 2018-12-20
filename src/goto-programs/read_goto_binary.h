/*******************************************************************\

Module: Read Goto Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Read Goto Programs

#ifndef CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H
#define CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H

#include <string>

#include <util/deprecate.h>
#include <util/optional.h>

class goto_functionst;
class goto_modelt;
class guard_managert;
class message_handlert;
class symbol_tablet;

bool read_goto_binary(
  const std::string &filename,
  symbol_tablet &,
  goto_functionst &,
  guard_managert &guard_manager,
  message_handlert &);

DEPRECATED("use two-parameter variant instead")
bool read_goto_binary(
  const std::string &filename,
  goto_modelt &dest,
  guard_managert &guard_manager,
  message_handlert &);

optionalt<goto_modelt>
read_goto_binary(
  const std::string &filename,
  guard_managert &guard_manager,
  message_handlert &);

bool is_goto_binary(const std::string &filename);

bool read_object_and_link(
  const std::string &file_name,
  symbol_tablet &,
  goto_functionst &,
  guard_managert &guard_manager,
  message_handlert &);

bool read_object_and_link(
  const std::string &file_name,
  goto_modelt &,
  guard_managert &guard_manager,
  message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_READ_GOTO_BINARY_H
