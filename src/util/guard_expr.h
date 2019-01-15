/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Guard Data Structure

#ifndef CPROVER_UTIL_GUARD_EXPR_H
#define CPROVER_UTIL_GUARD_EXPR_H

#include <iosfwd>

#include "std_expr.h"

/// This is unused by this implementation of guards, but can be used by other
/// implementations of the same interface.
struct guard_expr_managert
{
};

class guard_exprt
{
public:
  explicit guard_exprt(const exprt &e, guard_expr_managert &manager)
    : manager(manager), expr(e)
  {
  }

  guard_exprt &operator=(const guard_exprt &other)
  {
    expr = other.expr;
    manager = other.manager;
    return *this;
  }

  void add(const exprt &expr);

  void append(const guard_exprt &guard)
  {
    add(guard.as_expr());
  }

  exprt as_expr() const
  {
    return expr;
  }

  void guard_expr(exprt &dest) const;

  bool is_true() const
  {
    return expr.is_true();
  }

  bool is_false() const
  {
    return expr.is_false();
  }

  friend guard_exprt &operator-=(guard_exprt &g1, const guard_exprt &g2);
  friend guard_exprt &operator|=(guard_exprt &g1, const guard_exprt &g2);

  guard_exprt operator!() const;

  guard_expr_managert &manager;

private:
  exprt expr;
};

#endif // CPROVER_UTIL_GUARD_EXPR_H
