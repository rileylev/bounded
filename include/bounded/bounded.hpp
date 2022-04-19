#ifndef BOUNDED_H_
#define BOUNDED_H_

#include "impl/macros.hpp"
#include "interval.hpp"

#include <concepts>

#define ASSERT(...)
#define ASSERT_NOEXCEPT true

constexpr bool anoexcept_(auto...xs) {return ASSERT_NOEXCEPT && (xs && ...);}
#define ANOEXCEPT(...) noexcept(anoexcept_(__VA_ARGS__))

template<std::three_way_comparable Poset, interval<Poset> bounds_>
class bounded;

struct bounded_friends {
#define BINOP(op)                                                         \
  template<std::three_way_comparable P0,                                  \
           interval<P0>              i0,                                  \
           std::three_way_comparable P1,                                  \
           interval<P1>              i1>                                  \
  friend auto constexpr operator op(bounded<P0, i0> x, bounded<P1, i1> y) \
      ARROW(bounded<decltype(x.get() op y.get()), i0 op i1>{              \
          x.get() op y.get()})

  BINOP(+)
  BINOP(-)
  BINOP(*)
};

template<std::three_way_comparable Poset, interval<Poset> bounds_>
class bounded : bounded_friends {
  Poset x_;

 public:
  static constexpr interval<Poset> bounds = bounds_;
  constexpr bounded(Poset x) ANOEXCEPT() : x_{x} {
    ASSERT(bounds.has(x));
  }

  constexpr ReadOut<Poset> get() {
    HEDLEY_ASSUME(bounds.has(x_));
    return x_;
  }

  constexpr auto operator-() ARROW(bounded<Poset, -bounds>{-get()})
};

#endif // BOUNDED_H_
