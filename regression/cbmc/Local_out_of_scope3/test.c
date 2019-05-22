void f(int index)
{
  unsigned int *pointer[1];
  unsigned int actual=0u;
  pointer[0] = &actual;

  if(index==0)
    *pointer[index] = 1u;

  __CPROVER_assert(1u != actual, "");
}

