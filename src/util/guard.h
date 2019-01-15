/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Guard Data Structure

#ifndef CPROVER_UTIL_GUARD_H
#define CPROVER_UTIL_GUARD_H

#ifdef HAS_CUDD

#include "guard_bdd.h"

using guard_managert = guard_bdd_managert;
using guardt = guard_bddt;

#else

#include "guard_expr.h"

using guard_managert = guard_expr_managert;
using guardt = guard_exprt;

#endif // HAS_CUDD

#endif // CPROVER_UTIL_GUARD_H
