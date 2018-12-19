/*******************************************************************\

Module: Generate Equation using Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Generate Equation using Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_PRECONDITION_H
#define CPROVER_GOTO_SYMEX_PRECONDITION_H

#include <pointer-analysis/value_sets.h>
#include <util/guard.h>

#include "symex_target_equation.h"
#include "goto_symex_state.h"

void precondition(
  const namespacet &ns,
  value_setst &value_sets,
  const goto_programt::const_targett target,
  const symex_target_equationt &equation,
  const goto_symex_statet &s,
  exprt &dest,
  guard_managert &guard_manager);

#endif // CPROVER_GOTO_SYMEX_PRECONDITION_H
