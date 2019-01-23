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

#include <analyses/dirty.h>

void goto_symext::symex_decl(statet &state)
{
  const goto_programt::instructiont &instruction=*state.source.pc;

  const codet &code = instruction.code;

  // two-operand decl not supported here
  // we handle the decl with only one operand
  PRECONDITION(code.operands().size() == 1);

  symex_decl(state, to_code_decl(code).symbol());
}

void goto_symext::symex_decl(statet &state, const symbol_exprt &expr)
{
  // We increase the L2 renaming to make these non-deterministic.
  // We also prevent propagation of old values.

  level1t<ssa_exprt> ssa = state.rename_level1_ssa(ssa_exprt{expr}, ns);
  const irep_idt &l1_identifier = ssa.expr.get_identifier();

  // rename type to L2
  state.rename(ssa.expr.type(), l1_identifier, ns);
  ssa.expr.update_type();

  // in case of pointers, put something into the value set
  if(expr.type().id() == ID_pointer)
  {
    exprt rhs = [&]() -> exprt {
      if(auto failed = get_failed_symbol(expr, ns))
        return address_of_exprt(*failed, to_pointer_type(expr.type()));
      return exprt(ID_invalid);
    }();

    level1t<exprt> l1_rhs = state.rename_level1(std::move(rhs), ns);
    state.value_set.assign(ssa, l1_rhs, ns, true, false);
  }

  // prevent propagation
  state.propagation.erase(l1_identifier);

  // L2 renaming
  // inlining may yield multiple declarations of the same identifier
  // within the same L1 context
  const auto level2_it = state.level2.current_names
                           .emplace(l1_identifier, std::make_pair(ssa.expr, 0))
                           .first;
  symex_renaming_levelt::increase_counter(level2_it);
  const bool record_events=state.record_events;
  state.record_events=false;
  level2t<ssa_exprt> l2_expr = state.rename_level2(ssa.expr, ns);
  state.record_events=record_events;

  // we hide the declaration of auxiliary variables
  // and if the statement itself is hidden
  bool hidden=
    ns.lookup(expr.get_identifier()).is_auxiliary ||
    state.top().hidden_function ||
    state.source.pc->source_location.get_hide();

  target.decl(
    state.guard.as_expr(),
    l2_expr.expr,
    state.source,
    hidden ? symex_targett::assignment_typet::HIDDEN
           : symex_targett::assignment_typet::STATE);

  if(
    state.dirty(l2_expr.expr.get_object_name()) && state.atomic_section_id == 0)
    // TODO: make shared write take a level2 exprt
    target.shared_write(
      state.guard.as_expr(),
      l2_expr.expr,
      state.atomic_section_id,
      state.source);
}
