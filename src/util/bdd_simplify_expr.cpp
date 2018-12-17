/*******************************************************************\

Module: Conversion between exprt and Cudd BDDS

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Conversion between exprt and BDDs

#include "bdd_simplify_expr.h"

#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/std_expr.h>

/// Warning: global variable
Cudd bdd_manager = Cudd();

bdd_expr_convertert::bdd_expr_convertert()
{
  bdd_manager.AutodynEnable();
}

BDD bdd_expr_convertert::from_expr(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);
  if(expr.is_constant())
    return expr.is_false() ? bdd_manager.bddZero() : bdd_manager.bddOne();
  if(expr.id()==ID_not)
    return !from_expr(to_not_expr(expr).op());
  if(expr.id()==ID_and || expr.id()==ID_or || expr.id()==ID_xor)
  {
    DATA_INVARIANT(
      expr.operands().size() >= 2,
      "logical and, or, and xor expressions have at least two operands");
    const exprt bin_expr = make_binary(expr);

    BDD op0 = from_expr(bin_expr.op0());
    BDD op1 = from_expr(bin_expr.op1());

    if(expr.id() == ID_and)
    {
      if(op0.IsZero() || op1.IsZero())
        return bdd_manager.bddZero();
      // Is this necessary?
      if(op0.IsOne())
        return op1;
      if(op1.IsOne())
        return op0;
      return op0.And(op1);
    }
    if(expr.id() == ID_or)
    {
      if(op0.IsOne() || op1.IsOne())
        return bdd_manager.bddOne();
      if(op0.IsZero())
        return op1;
      if(op1.IsZero())
        return op0;
      return op0.Or(op1);
    }
    return op0.Xor(op1);
  }

  if(expr.id()==ID_implies)
  {
    const implies_exprt &imp_expr=to_implies_expr(expr);
    const BDD op0 = from_expr(imp_expr.op0());
    const BDD op1 = from_expr(imp_expr.op1());
    return op1.Or(!op0);
  }
  if(expr.id()==ID_equal &&
     expr.operands().size()==2 &&
     expr.op0().type().id()==ID_bool)
  {
    const equal_exprt &eq_expr=to_equal_expr(expr);
    const BDD op0=from_expr(eq_expr.op0());
    const BDD op1=from_expr(eq_expr.op1());
    return !(op0.Xor(op1));
  }
  if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);
    const BDD i = from_expr(if_expr.cond());
    const BDD t = from_expr(if_expr.true_case());
    const BDD e = from_expr(if_expr.false_case());

    // This case seems to cause segfault in Cudd_bddIte
    if(t.IsOne() && e.IsZero())
      return i;

    return i.Ite(t, e);
  }
  auto entry = expr_map.insert(std::make_pair(expr, 0));

  if(entry.second)
  {
    const BDD result = bdd_manager.bddVar();
    const unsigned int index = result.NodeReadIndex();
    entry.first->second = index;
    node_map.emplace(index, expr);
    return result;
  }
  return bdd_manager.bddVar(entry.first->second);
}

static exprt make_not(const exprt &e)
{
  if(e.id() == ID_not)
    return e.op0();
  return e;
}

exprt bdd_expr_convertert::as_expr(BDD bdd) const
{
  return as_expr(bdd.getNode());
}

exprt bdd_expr_convertert::as_expr(DdNode *r) const
{
  if(Cudd_IsConstant(r))
  {
    if(Cudd_IsComplement(r))
      return false_exprt();
    else
      return true_exprt();
  }
  const int var_index = Cudd_NodeReadIndex(r);
  auto entry=node_map.find(var_index);
  CHECK_RETURN(entry != node_map.end());
  const exprt &cond = entry->second;
  const exprt result_ignoring_complement = [&]() -> exprt {
    const exprt high = as_expr(Cudd_T(r));
    const exprt low = as_expr(Cudd_E(r));
    if(low.is_false())
    {
      if(high.is_true())
        return cond;
      return and_exprt(cond, high);
    }
    if(high.is_false())
    {
      if(low.is_true())
        return make_not(cond);
      return and_exprt(make_not(cond), low);
    }
    if(low.is_true())
      return or_exprt(make_not(cond), high);
    if(high.is_true())
      return or_exprt(cond, low);
    return if_exprt(cond, high, low);
  }();
  if(Cudd_IsComplement(r))
    return make_not(result_ignoring_complement);
  return result_ignoring_complement;
}
