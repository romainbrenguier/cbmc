#ifndef CPROVER_TAINT_FAST_GOTO_ANALYSER_H
#define CPROVER_TAINT_FAST_GOTO_ANALYSER_H

#include <goto-programs/goto_model.h>
#include <goto-programs/goto_program.h>
#include <goto-analyzer/taint_trace_recogniser.h>
#include <analyses/call_graph.h>
#include <util/irep.h>
#include <string>


void  taint_fast_analyser(
    std::vector<taint_tracet>&  output_traces,
    goto_modelt const&  goto_model,
    call_grapht const&  call_graph,
    std::string const&  root_function_name,
    taint_sources_mapt const&  taint_sources,
    taint_sinks_mapt const&  taint_sinks
    );


#endif
