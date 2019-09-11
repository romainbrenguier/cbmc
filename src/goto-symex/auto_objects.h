/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_SYMEX_AUTO_OBJECTS_H
#define CPROVER_GOTO_SYMEX_AUTO_OBJECTS_H

exprt make_auto_object(const typet &, goto_symex_statet &, unsigned);

void trigger_auto_object(
  const exprt &expr,
  goto_symex_statet &state,
  const namespacet &ns,
  const symex_configt &symex_config,
  symex_targett &target,
  unsigned &dynamic_counter);

void initialize_auto_object(
  const exprt &expr,
  goto_symex_statet &state,
  const namespacet &ns,
  const symex_configt &symex_config,
  symex_targett &target,
  unsigned &dynamic_counter);

#endif // CPROVER_GOTO_SYMEX_AUTO_OBJECTS_H
