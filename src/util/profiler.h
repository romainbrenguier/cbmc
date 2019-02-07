//
// Created by romain on 14/12/18.
//

#ifndef CPROVER_UTIL_PROFILER_H
#define CPROVER_UTIL_PROFILER_H

#include <chrono>
#include <iostream>
#include <memory>
#include <execinfo.h>
#include <cxxabi.h>
#include "freer.h"

// #define NO_PROFILING

#ifdef NO_PROFILING
#define PROFILER_BREAKPOINT
#else
#define PROFILER_BREAKPOINT profiler_breakpoint(__FILE__, __LINE__)
#define PROFILER_BREAKPOINT_NOBACKTRACE profiler_breakpoint(__FILE__, __LINE__, true)
#endif

#define BACKTRACE_SIZE 1

inline std::string get_backtrace_string()
{
  std::ostringstream out;
  void * stack[BACKTRACE_SIZE + 2] = {};

  int entries=backtrace(stack, sizeof(stack) / sizeof(void *));
  std::unique_ptr<char*, freert> description(
    backtrace_symbols(stack, entries));

  for(int i=2; i<entries; i++)
  {
    out << '<' << std::flush;
    std::string working = description.get()[i];
    std::string::size_type start=working.rfind('(');  // Path may contain '(' !
    std::string::size_type plus_pos=working.find('+', start);
    if(start != std::string::npos && plus_pos != std::string::npos)
    {

      std::string::size_type length=plus_pos-(start+1);
      std::string mangled(working.substr(start+1, length));
      int demangle_success=1;
      std::unique_ptr<char, freert> demangled(
        abi::__cxa_demangle(
          mangled.c_str(), nullptr, nullptr, &demangle_success));
      if(demangle_success==0)
      {
        std::string function = demangled.get();
        std::string::size_type name_end = function.find('(');
        out << function.substr(0, name_end);
      }
    }
  }
  return out.str();
}

static std::chrono::time_point<std::chrono::steady_clock>
  profiler_last_time_point = std::chrono::steady_clock::now();

inline void reset_profiler_time()
{
  profiler_last_time_point = std::chrono::steady_clock::now();
}

inline void profiler_breakpoint(
  const std::string &file, unsigned line, bool no_backtrace = false)
{
  auto now = std::chrono::steady_clock::now();
  auto diff = std::chrono::duration<double>(now - profiler_last_time_point);
  auto start = file.find_last_of('/');

  const std::string backtrace = no_backtrace ? "" : get_backtrace_string();
  std::string id =
    start != std::string::npos
    ? file.substr(start+1) + ":" + std::to_string(line) + backtrace
    : file + ":" + std::to_string(line) + backtrace;
  if(id.length() < 120)
    std::cout << id;
  else
    std::cout << id.substr(0, 117) << "...";
  std::cout << " " << diff.count() << std::endl;
  profiler_last_time_point = std::chrono::steady_clock::now();
}

#endif //CPROVER_UTIL_PROFILER_H
