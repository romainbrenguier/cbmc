/*******************************************************************\

Module: Streams

Author: Romain Brenguier

\*******************************************************************/

#ifndef CPROVER_UTIL_STREAM_H
#define CPROVER_UTIL_STREAM_H

#include <functional>
#include <vector>
#include <util/optional.h>
#include <util/make_unique.h>

/// Information required to construct a stream
template<typename T>
class stream_infot
{
public:
  /// Optional reference to the next token. Should be nullptr to signal the end.
  /// The pointed object should not be deleted until the next junk or the
  /// stream_infot object is deleted.
  virtual const T * peek() const = 0;

  /// Advance to the next token.
  virtual void junk() = 0;
};

template<typename T>
class streamt
{
public:
  explicit streamt(std::shared_ptr<stream_infot<T>> info)
    : data(std::move(info))
  {
  }

  const T * peek() const
  {
    return data->peek();
  }

  void junk()
  {
    data->junk();
  }

  streamt<T> filter(std::function<bool(const T &)> f);

  /// Template argument type `A` has to be specified when f is given as a lambda
  template<typename A>
  streamt<A> map(std::function<A(const T &)> f);

  void for_each(const std::function<void(const T &)> &f);

protected:
  /// Underlying data
  std::shared_ptr<stream_infot<T>> data;
};

/// Same as peek but advance the stream first.
template<typename T>
T* next(streamt<T> &stream)
{
  stream.junk();
  return stream.peek();
}

template<typename T>
bool is_empty(const streamt<T> &stream)
{
  return stream.peek() == nullptr;
}

template<typename ContainerType, typename T = typename ContainerType::value_type>
class container_stream_infot : public stream_infot<T>
{
public:
  explicit container_stream_infot(std::shared_ptr<ContainerType> container)
    : container(std::move(container)),
      it(this->container->begin()),
      end(this->container->end())
  {
  }

  const T* peek() const override
  {
    return (it == end) ? nullptr : &(*it);
  }

  void junk() override
  {
    if(it != end)
      ++it;
  }
private:
  std::shared_ptr<ContainerType> container;
  decltype(container->begin()) it;
  decltype(container->end()) end;

};

/// Create a stream using a shared pointer to a container
template<typename ContainerType, typename T = typename ContainerType::value_type>
streamt<T> stream(std::shared_ptr<ContainerType> container)
{
  std::shared_ptr<stream_infot<T>> stream_info =
    std::make_shared<container_stream_infot<ContainerType, T>>(
      std::move(container));
  return streamt<T>(stream_info);
}

/// Create a stream by moving a container
template<typename ContainerType, typename T = typename ContainerType::value_type>
streamt<T> make_stream(ContainerType container)
{
  return stream(std::make_shared<ContainerType>(std::move(container)));
}

template<typename IteratorType, typename T = typename IteratorType::value_type>
class iterator_stream_infot : public stream_infot<T>
{
public:
  explicit iterator_stream_infot(IteratorType _begin, IteratorType _end)
    : it(_begin), end(_end)
  {
  }

  const T* peek() const override
  {
    return (it == end) ? nullptr : &(*it);
  }

  void junk() override
  {
    if(it != end)
      ++it;
  }

private:
  IteratorType it;
  IteratorType end;
};

/// Create a stream using a reference to a container
/// Warning: this is not safe to use if the container can be destroied while
/// the stream object still exists
template<typename IteratorType, typename T = typename IteratorType::value_type>
streamt<T> stream(IteratorType begin, IteratorType end)
{
  std::shared_ptr<stream_infot<T>> stream_info =
    std::make_shared<iterator_stream_infot<IteratorType, T>>(
      begin, end);
  return streamt<T>(stream_info);
}

template<typename T>
class filter_stream_infot : public stream_infot<T>
{
public:
  explicit filter_stream_infot(
    std::shared_ptr<stream_infot<T>> info, std::function<bool(const T &)> f)
    : underlying(std::move(info)), f(std::move(f))
  {
    advance_to_first_to_peek();
  }

  const T* peek() const override
  {
    return underlying->peek();
  }

  void junk() override
  {
    underlying->junk();
    advance_to_first_to_peek();
  }

private:
  std::shared_ptr<stream_infot<T>> underlying;
  std::function<bool(const T &)> f;

  /// Ensure that the underlying stream is always at positionned on an element
  /// for which `f` is true.
  void advance_to_first_to_peek()
  {
    auto next_token = underlying->peek();
    while(next_token != nullptr && !f(*next_token))
    {
      underlying->junk();
      next_token = underlying->peek();
    }
  }
};

template<typename T>
streamt<T> streamt<T>::filter(std::function<bool(const T &)> f)
{
  std::shared_ptr<stream_infot<T>> stream_info =
    std::make_shared<filter_stream_infot<T>>(data, std::move(f));
  return streamt<T>(std::move(stream_info));
}

template<typename T>
void streamt<T>::for_each(const std::function<void(const T &)> &f)
{
  for(auto next_token = peek(); next_token != nullptr; next_token = next(*this))
    f(*next_token);
}

template<typename Input, typename Output>
class map_stream_infot : public stream_infot<Output>
{
public:
  explicit map_stream_infot(
    std::shared_ptr<stream_infot<Input>> info, std::function<Output (const Input &)> f)
  : underlying(std::move(info)), f(std::move(f))
  {
    update_current();
  }

  const Output* peek() const override
  {
    return current ? current.get() : nullptr;
  }

  void junk() override
  {
    underlying->junk();
    update_current();
  }

private:
  std::unique_ptr<Output> current;
  std::shared_ptr<stream_infot<Input>> underlying;
  std::function<Output (const Input &)> f;

  void update_current()
  {
    auto current_underlying = underlying->peek();
    current = current_underlying == nullptr
      ? nullptr
      : util_make_unique<Output>(f(*current_underlying));
  }
};

template<typename T>
template<typename A>
streamt<A> streamt<T>::map(std::function<A(const T &)> f)
{
  std::shared_ptr<stream_infot<A>> stream_info =
    std::make_shared<map_stream_infot<T, A>>(data, std::move(f));
  return streamt<A>(stream_info);
}

template<typename T>
struct concat_stream_infot : public stream_infot<T>
{
private:
  std::shared_ptr<streamt<T>> first_stream;
  std::shared_ptr<streamt<T>> second_stream;
  bool at_first = true;

public:
  concat_stream_infot(
    std::shared_ptr<streamt<T>> first,
    std::shared_ptr<streamt<T>> second)
    : first_stream(std::move(first)), second_stream(std::move(second))
  {
    if(is_empty(*first_stream))
      at_first = false;
  }

  const T * peek() const override
  {
    return at_first ? first_stream->peek() : second_stream->peek();
  }

  void junk() override
  {
    if(at_first)
    {
      if(next(*first_stream) == nullptr)
        at_first = false;
    }
    else
      second_stream->junk();
  };
};

template <typename T>
streamt<T> concat(
  streamt<T> &&first,
  streamt<T> &&second)
{
  std::shared_ptr<stream_infot<T>> stream_info =
    std::make_shared<concat_stream_infot<T>>(
      std::make_shared<streamt<T>>(std::move(first)),
      std::make_shared<streamt<T>>(std::move(second)));
  return streamt<T>(stream_info);
}
#endif // CPROVER_UTIL_STREAM_H
