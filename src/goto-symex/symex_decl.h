/*******************************************************************\

Module: Symbolic Execution

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Symbolic Execution of declarations

#ifndef CPROVER_GOTO_SYMEX_SYMEX_DECL_H
#define CPROVER_GOTO_SYMEX_SYMEX_DECL_H

class goto_symex_statet;
class namespacet;
class path_storaget;
class symbol_exprt;
class symex_target_equationt;

/// Symbolically execute a DECL instruction for the given symbol or simulate
/// such an execution for a synthetic symbol
/// \param state: Symbolic execution state for current instruction
/// \param expr: The symbol being declared
void symex_decl(
  goto_symex_statet &state,
  const symbol_exprt &expr,
  path_storaget &path_storage,
  const namespacet &ns,
  symex_target_equationt &target);

#endif // CPROVER_GOTO_SYMEX_SYMEX_DECL_H
