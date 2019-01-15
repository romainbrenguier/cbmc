/*******************************************************************\

Module: Memory-mapped I/O Instrumentation for Goto Programs

Author: Daniel Kroening

Date: September 2011

\*******************************************************************/

/// \file
/// Memory-mapped I/O Instrumentation for Goto Programs

#ifndef CPROVER_GOTO_INSTRUMENT_MMIO_H
#define CPROVER_GOTO_INSTRUMENT_MMIO_H

class value_setst;
class goto_modelt;
class guard_managert;

void mmio(value_setst &, goto_modelt &, guard_managert &guard_manager);

#endif // CPROVER_GOTO_INSTRUMENT_MMIO_H
