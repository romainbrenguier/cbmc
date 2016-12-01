#include <goto-analyzer/taint_fast_analyser.h>
#include <goto-analyzer/taint_statistics.h>
#include <vector>
#include <tuple>
#include <deque>
#include <algorithm>
#include <iterator>
#include <iostream>


static bool  find_shortest_path(
    call_grapht const&  call_graph,
    call_grapht const&  inverted_call_graph,
    std::string const&  source_function_name,
    std::string const&  target_function_name,
    std::vector< std::pair<std::string,bool> >& path
    )
{
  std::size_t const  start_len = path.size();
  std::unordered_set<std::string>  visited;
  std::unordered_map<std::string, std::pair<std::string,bool> >  predecessors;
  std::deque<std::string>  work_list{source_function_name};
  do
  {
    std::string const  fn_name = work_list.front();
    work_list.pop_front();

    if (visited.count(fn_name) != 0ULL)
      continue;
    visited.insert(fn_name);

    if (fn_name == target_function_name)
    {
      std::string fn = target_function_name;
      path.push_back({fn,true});
      do
      {
        path.push_back(predecessors.at(fn));
        fn = predecessors.at(fn).first;
      }
      while (fn != source_function_name);
      std::reverse(std::next(path.begin(),start_len),path.end());
      return true;
    }

    {
      call_grapht::call_edges_ranget const  range =
          call_graph.out_edges(fn_name);
      for (auto  it = range.first; it != range.second; ++it)
      {
          std::string const  other_fn_name = as_string(it->second);
          if (visited.count(other_fn_name) == 0ULL)
          {
            predecessors[other_fn_name] = { fn_name, true };
            work_list.push_back(other_fn_name);
          }
      }
    }
    {
      call_grapht::call_edges_ranget const  range =
          inverted_call_graph.out_edges(fn_name);
      for (auto  it = range.first; it != range.second; ++it)
      {
        std::string const  other_fn_name = as_string(it->second);
        std::cout << "other_fn_name [false]: " << other_fn_name << "\n";
        if (visited.count(other_fn_name) == 0ULL)
        {
          predecessors[other_fn_name] = { fn_name, false };
          work_list.push_back(other_fn_name);
        }
      }
    }
  }
  while (!work_list.empty());
  return false;
}


static void  refine_path_to_error_traces(
    goto_modelt const&  goto_model,
    std::vector< std::pair<std::string,bool> > const& path,
    std::vector<taint_tracet>&  output_traces
    )
{
  // TODO!
}


static void  taint_fast_analyser(
    std::vector<taint_tracet>&  output_traces,
    goto_modelt const&  goto_model,
    call_grapht const&  call_graph,
    call_grapht const&  inverted_call_graph,
    std::string const&  root_function_name,
    taint_svaluet::taint_symbolt const&  taint_name,
    std::string const&  source_function_name,
    goto_programt::const_targett const source_instruction,
    std::string const&  sink_function_name,
    goto_programt::const_targett const sink_instruction
    )
{
  std::vector< std::pair<std::string,bool> > path;
  if (!find_shortest_path(
          call_graph,
          inverted_call_graph,
          root_function_name,
          source_function_name,
          path
          ))
    return;
  if (!path.empty())
    path.pop_back();
  if (!find_shortest_path(
          call_graph,
          inverted_call_graph,
          source_function_name,
          sink_function_name,
          path
          ))
    return;
  refine_path_to_error_traces(goto_model,path,output_traces);
}


void  taint_fast_analyser(
    std::vector<taint_tracet>&  output_traces,
    goto_modelt const&  goto_model,
    call_grapht const&  call_graph,
    std::string const&  root_function_name,
    taint_sources_mapt const&  taint_sources,
    taint_sinks_mapt const&  taint_sinks
    )
{
  call_grapht  inverted_call_graph;
  compute_inverted_call_graph(call_graph,inverted_call_graph);

  taint_statisticst::instance().begin_error_traces_recognition();

  for (auto const  tid_locs : taint_sinks)
    for (auto const  fn_locs : tid_locs.second)
      for (auto const  loc : fn_locs.second)
      {
        auto const  src_it = taint_sources.find(tid_locs.first);
        if (src_it != taint_sources.cend())
          for (auto const  src_fn_locs : src_it->second)
            for (auto const  src_loc : src_fn_locs.second)
              taint_fast_analyser(
                    output_traces,
                    goto_model,
                    call_graph,
                    inverted_call_graph,
                    root_function_name,
                    tid_locs.first,
                    src_fn_locs.first,
                    src_loc,
                    fn_locs.first,
                    loc
                    );
      }

  taint_statisticst::instance().end_error_traces_recognition();
}
