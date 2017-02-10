/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstring>
#include <cassert>
#include <vector>

#include "unicode.h"

#ifdef _WIN32
#include <windows.h>
#endif

/*******************************************************************\

Function: narrow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#define BUFSIZE 100

std::string narrow(const wchar_t *s)
{
  #ifdef _WIN32

  size_t slength=wcslen(s);
  int rlength=WideCharToMultiByte(CP_UTF8, 0, s, slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, s, (int)slength, &r[0], rlength, NULL, NULL);
  return r;

  #else
  // dummy conversion
  std::string r;
  r.reserve(wcslen(s));
  while(*s!=0)
  {
    r+=char(*s);
    s++;
  }

  return r;
  #endif
}

/*******************************************************************\

Function: widen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::wstring widen(const char *s)
{
  #ifdef _WIN32

  size_t slength=strlen(s);
  int rlength=MultiByteToWideChar(CP_UTF8, 0, s, (int)slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, s, (int)slength, &r[0], rlength);
  return r;

  #else
  // dummy conversion
  std::wstring r;
  r.reserve(strlen(s));
  while(*s!=0)
  {
    r+=wchar_t(*s);
    s++;
  }

  return r;
  #endif
}

/*******************************************************************\

Function: narrow

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string narrow(const std::wstring &s)
{
  #ifdef _WIN32

  size_t slength=s.size();
  int rlength=WideCharToMultiByte(CP_UTF8, 0, &s[0], (int)slength, NULL, 0, NULL, NULL);
  std::string r(rlength, 0);
  WideCharToMultiByte(CP_UTF8, 0, &s[0], (int)slength, &r[0], rlength, NULL, NULL);
  return r;

  #else
  // dummy conversion
  return std::string(s.begin(), s.end());
  #endif
}

/*******************************************************************\

Function: widen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::wstring widen(const std::string &s)
{
  #ifdef _WIN32

  size_t slength=s.size();
  int rlength=MultiByteToWideChar(CP_UTF8, 0, &s[0], (int)slength, NULL, 0);
  std::wstring r(rlength, 0);
  MultiByteToWideChar(CP_UTF8, 0, &s[0], slength, &r[0], rlength);
  return r;

  #else
  // dummy conversion
  return std::wstring(s.begin(), s.end());
  #endif
}

/*******************************************************************\

Function: utf32_to_utf8

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void utf32_to_utf8(unsigned int c, std::string &result)
{
  if(c<=0x7f)
    result+=char(c);
  else if(c<=0x7ff)
  {
    result+=char((c >> 6)   | 0xc0);
    result+=char((c & 0x3f) | 0x80);
  }
  else if(c<=0xffff)
  {
    result+=char((c >> 12)         | 0xe0);
    result+=char(((c >> 6) & 0x3f) | 0x80);
    result+=char((c & 0x3f)        | 0x80);
  }
  else
  {
    result+=char((c >> 18)         | 0xf0);
    result+=char(((c >> 12) & 0x3f)| 0x80);
    result+=char(((c >> 6) & 0x3f) | 0x80);
    result+=char((c & 0x3f)        | 0x80);
  }
}

/*******************************************************************\

Function: utf32_to_utf8

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string utf32_to_utf8(const std::basic_string<unsigned int> &s)
{
  std::string result;

  result.reserve(s.size()); // at least that long

  for(const auto c : s)
    utf32_to_utf8(c, result);

  return result;
}

/*******************************************************************\

Function: utf16_to_utf8

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string utf16_to_utf8(const std::basic_string<unsigned short int> &s)
{
  std::string result;

  result.reserve(s.size()); // at least that long

  for(const auto c : s)
    utf32_to_utf8(c, result);

  return result;
}

/*******************************************************************\

Function: narrow_argv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char **narrow_argv(int argc, const wchar_t **argv_wide)
{
  if(argv_wide==NULL) return NULL;

  // the following never gets deleted
  const char **argv_narrow=new const char *[argc+1];
  argv_narrow[argc]=0;

  for(int i=0; i<argc; i++)
    argv_narrow[i]=strdup(narrow(argv_wide[i]).c_str());

  return argv_narrow;
}


/*******************************************************************\

Function: utf8_to_utf16_little_endian

  Inputs: a utf8 string

 Outputs: a utf16 u16string

 Purpose: converts between utf8 and utf16 strings encoded in little endian

\*******************************************************************/

std::u16string utf8_to_utf16_little_endian(const std::string& utf8)
{
  std::vector<unsigned long> unicode;
  size_t i=0;
  while(i<utf8.size())
  {
    unsigned long unicode_char;
    size_t size;
    unsigned char ch=utf8[i++];

    if(ch<=0x7F)
    {
      unicode_char=ch;
      size=1;
    }
    else if(ch<=0xDF)
    {
      unicode_char=ch&0x1F;
      size=2;
    }
    else if(ch<=0xEF)
    {
      unicode_char=ch&0x0F;
      size=3;
    }
    else if(ch<=0xF7)
    {
      unicode_char=ch&0x07;
      size=4;
    }
    else
      assert(false);

    for(size_t j=1; j<size; ++j)
    {
      assert(i<utf8.size());
      unsigned char ch=utf8[i++];
      assert(ch>=0x80 && ch<=0xBF);
      unicode_char<<=6;
      unicode_char+=ch&0x3F;
    }
    assert(unicode_char<0xD800 || unicode_char>0xDFFF);
    assert(unicode_char<=0x10FFFF);
    unicode.push_back(unicode_char);
  }

  std::u16string utf16;
  for(size_t i=0; i<unicode.size(); ++i)
  {
    unsigned long uchar=unicode[i];
    if(uchar<=0xFFFF)
      utf16+=(char16_t)uchar;
    else
    {
      // We have to take care of endianness
      uchar-=0x10000;
      utf16+=(char16_t)((uchar&0x3FF)+0xDC00);
      utf16+=(char16_t)((uchar >> 10)+0xD800);
    }
  }
  return utf16;
}
