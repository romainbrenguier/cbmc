/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "guard.h"

#include <ostream>

#include "namespace.h"
#include "expr_util.h"
#include "invariant.h"
#include "simplify_utils.h"
#include "std_expr.h"
#include "symbol_table.h"

void guardt::guard_expr(exprt &dest) const
{
  if(is_true(*this))
  {
    // do nothing
  }
  else
  {
    if(dest.is_false())
    {
      dest = boolean_negate(as_expr());
    }
    else
    {
      implies_exprt tmp;
      tmp.op0()=as_expr();
      tmp.op1().swap(dest);
      dest.swap(tmp);
    }
  }
}

void guardt::add(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);

  if(is_false(*this) || expr.is_true())
    return;
  else if(is_true(*this) || expr.is_false())
  {
    this->expr=expr;

    return;
  }
  else if(this->expr.id()!=ID_and)
  {
    and_exprt a;
    a.add_to_operands(as_expr());
    this->expr=a;
  }

  exprt::operandst &op=this->expr.operands();

  if(expr.id()==ID_and)
    op.insert(op.end(),
              expr.operands().begin(),
              expr.operands().end());
  else
    op.push_back(expr);
}

guardt &operator -= (guardt &g1, const guardt &g2)
{
  if(g1.expr.id()!=ID_and || g2.expr.id()!=ID_and)
    return g1;

  sort_and_join(g1.expr);
  exprt g2_sorted = g2.as_expr();
  sort_and_join(g2_sorted);

  exprt::operandst &op1=g1.expr.operands();
  const exprt::operandst &op2=g2_sorted.operands();

  exprt::operandst::iterator it1=op1.begin();
  for(exprt::operandst::const_iterator
      it2=op2.begin();
      it2!=op2.end();
      ++it2)
  {
    while(it1!=op1.end() && *it1<*it2)
      ++it1;
    if(it1!=op1.end() && *it1==*it2)
      it1=op1.erase(it1);
  }

  g1.expr=conjunction(op1);

  return g1;
}

guardt &operator |= (guardt &g1, const guardt &g2)
{
  if(is_false(g2) || is_true(g1))
    return g1;
  if(is_false(g1) || is_true(g2))
  {
    g1=g2;
    return g1;
  }

  if(g1.expr.id()!=ID_and || g2.expr.id()!=ID_and)
  {
    exprt tmp(boolean_negate(g2.as_expr()));

    if(tmp==g1.as_expr())
      g1.expr = true_exprt();
    else
      g1.expr = or_exprt(g1.as_expr(), g2.as_expr());

    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    bdd_exprt t(ns);
    t.from_expr(g1.as_expr());
    g1.expr=t.as_expr();

    return g1;
  }

  // find common prefix
  sort_and_join(g1.expr);
  exprt g2_sorted=g2.as_expr();
  sort_and_join(g2_sorted);

  exprt::operandst &op1=g1.expr.operands();
  const exprt::operandst &op2=g2_sorted.operands();

  exprt::operandst n_op1, n_op2;
  n_op1.reserve(op1.size());
  n_op2.reserve(op2.size());

  exprt::operandst::iterator it1=op1.begin();
  for(exprt::operandst::const_iterator
      it2=op2.begin();
      it2!=op2.end();
      ++it2)
  {
    while(it1!=op1.end() && *it1<*it2)
    {
      n_op1.push_back(*it1);
      it1=op1.erase(it1);
    }
    if(it1!=op1.end() && *it1==*it2)
      ++it1;
    else
      n_op2.push_back(*it2);
  }
  while(it1!=op1.end())
  {
    n_op1.push_back(*it1);
    it1=op1.erase(it1);
  }

  if(n_op2.empty())
    return g1;

  // end of common prefix
  exprt and_expr1=conjunction(n_op1);
  exprt and_expr2=conjunction(n_op2);

  g1.expr=conjunction(op1);

  exprt tmp(boolean_negate(and_expr2));

  if(tmp!=and_expr1)
  {
    if(and_expr1.is_true() || and_expr2.is_true())
    {
    }
    else
    {
      g1.add(or_exprt(and_expr1, and_expr2));

      symbol_tablet symbol_table;
      namespacet ns(symbol_table);
      bdd_exprt t(ns);
      t.from_expr(g1);
      g1.expr=t.as_expr();
    }
  }

  return g1;
}
