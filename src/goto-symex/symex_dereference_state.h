/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#ifndef CPROVER_GOTO_SYMEX_SYMEX_DEREFERENCE_STATE_H
#define CPROVER_GOTO_SYMEX_SYMEX_DEREFERENCE_STATE_H

#include <pointer-analysis/dereference_callback.h>

#include "goto_symex.h"

class symex_dereference_statet:
  public dereference_callbackt
{
public:
  symex_dereference_statet(
    namespacet &ns,
    goto_symext::statet &_state):
    ns(ns),
    state(_state)
  {
  }

protected:
  namespacet &ns;
  goto_symext::statet &state;

  void get_value_set(
    const exprt &expr,
    value_setst::valuest &value_set) override;

  bool has_failed_symbol(
    const exprt &expr,
    const symbolt *&symbol) override;
};

#endif // CPROVER_GOTO_SYMEX_SYMEX_DEREFERENCE_STATE_H
