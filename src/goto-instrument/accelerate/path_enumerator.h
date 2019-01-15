/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#ifndef CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_ENUMERATOR_H
#define CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_ENUMERATOR_H

#include <goto-programs/goto_program.h>

#include <analyses/natural_loops.h>
#include <util/guard.h>

#include "path.h"

class path_enumeratort
{
 public:
  virtual ~path_enumeratort()
  {
  }

  virtual bool next(patht &path, guard_managert &guard_manager) = 0;
};

#endif // CPROVER_GOTO_INSTRUMENT_ACCELERATE_PATH_ENUMERATOR_H
