/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex.h"

#include <cassert>

#include <util/std_expr.h>

#include <pointer-analysis/add_failed_symbols.h>

void goto_symext::symex_dead(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const code_deadt &code = to_code_dead(instruction.code);

  // We increase the L2 renaming to make these non-deterministic.
  // We also prevent propagation of old values.

  level1t<ssa_exprt> ssa =
    state.rename_level1_ssa(ssa_exprt{code.symbol()}, ns);

  // in case of pointers, put something into the value set
  if(code.symbol().type().id() == ID_pointer)
  {
    exprt rhs = [&]() -> exprt {
      if(auto failed = get_failed_symbol(to_symbol_expr(code.symbol()), ns))
        return address_of_exprt(*failed, to_pointer_type(code.symbol().type()));
      return exprt(ID_invalid);
    }();

    level1t<exprt> l1_rhs = state.rename_level1(std::move(rhs), ns);
    state.value_set.assign(ssa.expr, l1_rhs.expr, ns, true, false);
  }

  const irep_idt &l1_identifier=ssa.expr.get_identifier();

  // prevent propagation
  state.propagation.erase(l1_identifier);

  // L2 renaming
  auto level2_it = state.level2.current_names.find(l1_identifier);
  if(level2_it != state.level2.current_names.end())
    symex_renaming_levelt::increase_counter(level2_it);
}
