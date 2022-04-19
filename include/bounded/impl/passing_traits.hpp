#ifndef BOUNDED_PASSING_TRAITS_HPP
#define BOUNDED_PASSING_TRAITS_HPP

#include <type_traits>
namespace passing_traits {
  template<class T>
  constexpr bool in_reg =
      std::is_trivially_copyable_v<T> and sizeof(T) < 2 * sizeof(void*);
  template<class T>
  using Read = std::conditional_t<in_reg<T>, T const, T const&>;
  template<class T>
  using ReadOut = std::conditional_t<in_reg<T>, T, T const&>;
}

#endif // BOUNDED_PASSING_TRAITS_HPP
