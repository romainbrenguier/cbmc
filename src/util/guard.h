/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Guard Data Structure

#ifndef CPROVER_UTIL_GUARD_H
#define CPROVER_UTIL_GUARD_H

#include <iosfwd>

#include "std_expr.h"

class guardt
{
public:
  guardt() : expr(true_exprt())
  {
  }

  void add(const exprt &expr);

  void append(const guardt &guard)
  {
    add(guard.as_expr());
  }

  exprt as_expr() const
  {
    return expr;
  }

  void guard_expr(exprt &dest) const;

  friend guardt &operator -= (guardt &g1, const guardt &g2);
  friend guardt &operator |= (guardt &g1, const guardt &g2);

private:
  exprt expr;
};

inline bool is_true(const guardt &g)
{
  return g.as_expr().is_true();
}

inline bool is_false(const guardt &g)
{
  return g.as_expr().is_false();
}

#endif // CPROVER_UTIL_GUARD_H
