/*******************************************************************\

Module: Java trace verification

Author: Jeannie Moulton

\*******************************************************************/

#ifndef CPROVER_JAVA_TRACE_VERIFICATION_JAVA_TRACE_VERIFICATION_H
#define CPROVER_JAVA_TRACE_VERIFICATION_JAVA_TRACE_VERIFICATION_H

bool valid_lvalue(const exprt &expr);

void check_trace_assumptions(const goto_tracet &trace);

#endif // CPROVER_JAVA_TRACE_VERIFICATION_JAVA_TRACE_VERIFICATION_H
