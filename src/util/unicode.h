/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UNICODE_H
#define CPROVER_UNICODE_H

#include <string>

// we follow the ideas suggested at
// http://www.utf8everywhere.org/

std::string narrow(const wchar_t *s);
std::wstring widen(const char *s);
std::string narrow(const std::wstring &s);
std::wstring widen(const std::string &s);

std::string utf32_to_utf8(const std::basic_string<unsigned int> &s);
std::string utf16_to_utf8(const std::basic_string<unsigned short int> &s);
std::string utf16le_to_ascii(const std::wstring&);

std::wstring utf8_to_utf16be(const std::string&);
std::wstring utf8_to_utf16le(const std::string&);

const char **narrow_argv(int argc, const wchar_t **argv_wide);

#endif
