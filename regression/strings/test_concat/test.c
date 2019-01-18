#include <assert.h>

typedef struct __attribute__((__packed__)) __CPROVER_refined_string_type // NOLINT
  { int length; char *content; } __CPROVER_refined_string_type;

extern int __CPROVER_uninterpreted_string_concat_func(
  int result_length, char *result_data,
  __CPROVER_refined_string_type str1, __CPROVER_refined_string_type str2);

extern char __CPROVER_uninterpreted_string_char_at_func(
  __CPROVER_refined_string_type str1, int position);

int main()
{
  __CPROVER_refined_string_type s,t,u;
  int return_code =
    __CPROVER_uninterpreted_string_concat_func(u.length, u.content, s, t);
  char c = __CPROVER_uninterpreted_string_char_at_func(u, 2);

  assert(c  == 'p');
  assert(__CPROVER_uninterpreted_string_char_at_func(u,2)  == 'p');
  return 0;
}
