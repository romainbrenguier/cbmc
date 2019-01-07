//
// Created by romain on 14/12/18.
//

#ifndef CPROVER_UTIL_PROFILER_H
#define CPROVER_UTIL_PROFILER_H

#include <chrono>
#include <iostream>
#include <memory>
#include <execinfo.h>
#include "freer.h"

// #define NO_PROFILING

#ifdef NO_PROFILING
#define PROFILER_BREAKPOINT
#else
#define PROFILER_BREAKPOINT profiler_breakpoint(__FILE__, __LINE__)
#endif

inline std::string get_backtrace_string()
{
  std::ostringstream out;
  void * stack[5] = {};

  std::size_t entries=backtrace(stack, sizeof(stack) / sizeof(void *));
  std::unique_ptr<char*, freert> description(
    backtrace_symbols(stack, entries));

  for(std::size_t i=2; i<entries; i++)
  {
    std::string working = description.get()[i];
    std::string::size_type start=working.rfind('(');  // Path may contain '(' !
    std::string::size_type plus_pos=working.find('+', start);
    if(start != std::string::npos && plus_pos != std::string::npos)
      out << working.substr(start + 1, plus_pos - start - 1);
    out << '_' << std::flush;
  }
  return out.str();
}

static std::chrono::time_point<std::chrono::steady_clock>
  profiler_last_time_point = std::chrono::steady_clock::now();

inline void profiler_breakpoint(const std::string &file, unsigned line)
{
  auto now = std::chrono::steady_clock::now();
  auto diff = std::chrono::duration<double>(now - profiler_last_time_point);
  auto start = file.find_last_of('/');

  std::string id =
    start != std::string::npos
    ? file.substr(start+1) + "_" + get_backtrace_string()
    : file + "_" + get_backtrace_string();
  if(id.length() < 120)
    std::cout << id;
  else
    std::cout << id.substr(0, 117) << "...";
  std::cout << ":" << line << " " << diff.count() << std::endl;
  profiler_last_time_point = std::chrono::steady_clock::now();
}

#endif //CPROVER_UTIL_PROFILER_H
