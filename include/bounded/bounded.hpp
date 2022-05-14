#ifndef BOUNDED_BOUNDED_HPP_INCLUDE_GUARD
#define BOUNDED_BOUNDED_HPP_INCLUDE_GUARD

#include "impl/macros.hpp"
#include "interval.hpp"

#include <concepts>

#define ASSERT(...)
#define ASSERT_NOEXCEPT true

namespace bounded { namespace impl {
  constexpr bool anoexcept_(auto... xs) {
    return ASSERT_NOEXCEPT && (xs && ...);
  }
}} // namespace bounded::impl
#define ANOEXCEPT(...) noexcept(::bounded::impl::anoexcept_(__VA_ARGS__))

namespace bounded {

template<class S, class X>
concept set_of = requires(S s, X x) {
  { s.has(x) } -> std::convertible_to<bool>;
};

template<std::three_way_comparable Poset, set_of<Poset> auto bounds_>
class bounded;

struct bounded_friends {
#if true
#  define BINOP(op)                                                         \
    template<std::three_way_comparable P0,                                  \
             auto                      i0,                                  \
             std::three_way_comparable P1,                                  \
             auto                      i1>                                  \
    friend auto constexpr operator op(bounded<P0, i0> x, bounded<P1, i1> y) \
        ARROW(bounded<decltype(x.get() op y.get()), i0 op i1>{              \
            x.get() op y.get()})

  BINOP(+)
  BINOP(-)
  BINOP(*)
#endif
};

template<std::three_way_comparable Poset, set_of<Poset> auto bounds_>
class bounded : bounded_friends {
  Poset x_;

 public:
  static constexpr interval<Poset> bounds = bounds_;
  // TODO: is this the right test?
  // should we just let you default construct in an invalid state so you
  // can assign later?
  constexpr bounded() requires(bounds_.has(Poset{})) = default;
  constexpr bounded(Poset x) ANOEXCEPT() : x_{x} { ASSERT(bounds.has(x)); }

  constexpr ReadOut<Poset> get() {
    HEDLEY_ASSUME(bounds.has(x_));
    return x_;
  }

  constexpr auto operator-() ARROW(bounded<Poset, -bounds>{-get()})

  constexpr operator Poset const&() noexcept RET(x_)
};
} // namespace bounded
#endif
