//
// Created by romain on 14/12/18.
//

#ifndef CPROVER_UTIL_PROFILER_H
#define CPROVER_UTIL_PROFILER_H

#include <chrono>
#include <iostream>

#define NO_PROFILING

#ifdef NO_PROFILING
#define PROFILER_BREAKPOINT
#else
#define PROFILER_BREAKPOINT profiler_breakpoint(__FILE__, __LINE__)
#endif

static std::chrono::time_point<std::chrono::steady_clock>
  profiler_last_time_point = std::chrono::steady_clock::now();

inline void profiler_breakpoint(const std::string &file, unsigned line)
{
  auto now = std::chrono::steady_clock::now();
  auto diff = std::chrono::duration<double>(now - profiler_last_time_point);
  if(file.length() < 30)
    std::cout << file;
  else
    std::cout << "..." << file.substr(file.length() - 27);
  std::cout << ":" << line << " " << diff.count() << std::endl;
  profiler_last_time_point = std::chrono::steady_clock::now();
}

#endif //CPROVER_UTIL_PROFILER_H
