/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_FORMAT_EXPR_H
#define CPROVER_UTIL_FORMAT_EXPR_H

#include "expr.h"
#include "format.h"

//! Formats an expression in a generic syntax
//! that is inspired by C/C++/Java, and is meant for debugging
std::ostream &format_rec(std::ostream &, const exprt &);

static inline std::string as_string(const exprt &e)
{
  std::ostringstream stream;
  format_rec(stream, e);
  return stream.str();
}

#endif // CPROVER_UTIL_FORMAT_EXPR_H
