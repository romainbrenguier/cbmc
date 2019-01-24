/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "precondition.h"
#include "goto_symex_state.h"

#include <util/find_symbols.h>

#include <pointer-analysis/goto_program_dereference.h>

#include <goto-programs/goto_model.h>

class preconditiont
{
public:
  preconditiont(
    const namespacet &_ns,
    value_setst &_value_sets,
    const goto_programt::const_targett _target,
    const symex_target_equationt::SSA_stept &_SSA_step,
    const goto_symex_statet &_s):
    ns(_ns),
    value_sets(_value_sets),
    target(_target),
    SSA_step(_SSA_step),
    s(_s)
  {
  }

protected:
  const namespacet &ns;
  value_setst &value_sets;
  const goto_programt::const_targett target;
  const symex_target_equationt::SSA_stept &SSA_step;
  const goto_symex_statet &s;
  void compute_rec(exprt &dest, guard_managert &guard_manager);

public:
  void compute(exprt &dest, guard_managert &guard_manager);

protected:
  void compute_address_of(exprt &dest, guard_managert &guard_manager);
};

void precondition(
  const namespacet &ns,
  value_setst &value_sets,
  const goto_programt::const_targett target,
  const symex_target_equationt &equation,
  const goto_symex_statet &s,
  exprt &dest,
  guard_managert &guard_manager)
{
  for(symex_target_equationt::SSA_stepst::const_reverse_iterator
      it=equation.SSA_steps.rbegin();
      it!=equation.SSA_steps.rend();
      it++)
  {
    preconditiont precondition(ns, value_sets, target, *it, s);
    precondition.compute(dest, guard_manager);
    if(dest.is_false())
      return;
  }
}

void preconditiont::compute_address_of(
  exprt &dest,
  guard_managert &guard_manager)
{
  if(dest.id()==ID_symbol)
  {
    // leave alone
  }
  else if(dest.id()==ID_index)
  {
    auto &index_expr = to_index_expr(dest);
    compute_address_of(index_expr.array(), guard_manager);
    compute(index_expr.index(), guard_manager);
  }
  else if(dest.id()==ID_member)
  {
    compute_address_of(to_member_expr(dest).compound(), guard_manager);
  }
  else if(dest.id()==ID_dereference)
  {
    compute(to_dereference_expr(dest).pointer(), guard_manager);
  }
}

void preconditiont::compute(exprt &dest, guard_managert &guard_manager)
{
  compute_rec(dest, guard_manager);
}

void preconditiont::compute_rec(exprt &dest, guard_managert &guard_manager)
{
  if(dest.id()==ID_address_of)
  {
    // only do index!
    compute_address_of(to_address_of_expr(dest).object(), guard_manager);
  }
  else if(dest.id()==ID_dereference)
  {
    auto &deref_expr = to_dereference_expr(dest);

    const irep_idt &lhs_identifier=SSA_step.ssa_lhs.get_object_name();

    // aliasing may happen here

    value_setst::valuest expr_set;
    value_sets.get_values(target, deref_expr.pointer(), expr_set);
    std::unordered_set<irep_idt> symbols;

    for(value_setst::valuest::const_iterator
        it=expr_set.begin();
        it!=expr_set.end();
        it++)
      find_symbols(*it, symbols);

    if(symbols.find(lhs_identifier)!=symbols.end())
    {
      // may alias!
      exprt tmp;
      tmp.swap(deref_expr.pointer());
      dereference(target, tmp, ns, value_sets, guard_manager);
      deref_expr.swap(tmp);
      compute_rec(deref_expr, guard_manager);
    }
    else
    {
      // nah, ok
      compute_rec(deref_expr.pointer(), guard_manager);
    }
  }
  else if(dest==SSA_step.ssa_lhs.get_original_expr())
  {
    dest=SSA_step.ssa_rhs;
    s.get_original_name(dest);
  }
  else
    Forall_operands(it, dest)
      compute_rec(*it, guard_manager);
}
