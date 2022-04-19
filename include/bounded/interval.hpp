#ifndef INTERVAL_HPP_INCLUDE_GUARD
#define INTERVAL_HPP_INCLUDE_GUARD

#include "impl/macros.hpp"

#include <assert.h>
#include <concepts>
#include <tuple>
#include <array>
#include <algorithm>

template<class Less = std::less<>>
constexpr auto project_less(auto proj, Less less = {}) {
  return [ proj, less ](auto x, auto y) ARROW(less(proj(x), proj(y)));
}

enum class Clusive : bool {
  in = true,
  ex = false,
};
constexpr Clusive operator*(Clusive x, Clusive y)
    NOEX(static_cast<Clusive>(static_cast<bool>(x) and static_cast<bool>(y)))

template<std::three_way_comparable Poset>
struct end {
  Poset   point;
  Clusive clusive;
};
template<class X>
end(X, Clusive) -> end<X>;

template<std::three_way_comparable P>
constexpr auto operator+(end<P> x) ARROW(end{+x.point, x.clusive})
template<std::three_way_comparable P>
constexpr auto operator-(end<P> x) ARROW(end{-x.point, x.clusive})

template<std::three_way_comparable X, std::three_way_comparable Y>
constexpr auto operator+(end<X> x, end<Y> y)
    ARROW(end{x.point + y.point, x.clusive* y.clusive})

template<std::three_way_comparable X, std::three_way_comparable Y>
constexpr auto operator-(end<X> x, end<Y> y) ARROW(x + (-y))

template<std::three_way_comparable X, std::three_way_comparable Y>
constexpr auto operator*(end<X> x, end<Y> y)
    ARROW(end{x.point * y.point, x.clusive* y.clusive})

using passing_traits::Read;
using passing_traits::ReadOut;
template<std::three_way_comparable Poset>
//
/* To use this as a non-type template parameter, we can't use private.

 https://en.cppreference.com/w/cpp/language/template_parameters:
 "A non-type template parameter must have a structural type, which is one
of the following...

 -  a literal class type with the following properties:

 -  all base classes and non-static data members are public and non-mutable
and the types of all base classes and non-static data members are
structural types or (possibly multi-dimensional) array thereof.
*/

struct interval {
  Poset   btm_             = {};
  Poset   top_             = {};
  Clusive btm_clusive_ : 1 = Clusive::ex;
  Clusive top_clusive_ : 1 = Clusive::ex;

  READER(btm)
  READER(top)
  READER(btm_clusive)
  READER(top_clusive)

  constexpr auto btm_end() ARROW(end{btm(), btm_clusive()})
  constexpr auto top_end() ARROW(end{top(), top_clusive()})

  constexpr interval() = default;

  constexpr bool empty() const NOEX(*this == interval{})

  constexpr interval(Poset btm_in, Poset top_ex)
      NOEX_CONS(interval{end{std::move(btm_in), Clusive::in},
                         end{std::move(top_ex), Clusive::ex}}) {}
  constexpr interval(end<Poset> btm, end<Poset> top) noexcept(
      std::is_nothrow_move_constructible_v<Poset>and noexcept(
          interval{},
          btm() <=> top()))
      : btm_{std::move(btm.point)},
        top_{std::move(top.point)},
        btm_clusive_{btm.clusve},
        top_clusive_{top.clusive} {
    // normalize the degenerate cases
    switch(btm() <=> top()) {
      case std::partial_ordering::greater:
        // unordered ->  interval must be empty by transitivity
      case std::partial_ordering::unordered: *this = interval{}; break;
      case std::partial_ordering::equivalent:
        if((btm_clusive() == Clusive::ex) or (top_clusive() == Clusive::ex))
          *this = interval{};
      case std::partial_ordering::less: return;
    }
  }

  constexpr friend bool operator==(interval, interval) = default;

  constexpr bool
      has(Read<Poset> x) noexcept(noexcept(x <=> btm(), x <=> top())) {
    auto const x_btm = x <=> btm();
    auto const x_top = x <=> top();

    if(x_btm == std::partial_ordering::unordered
       or x_top == std::partial_ordering::unordered)
      return false;
    // no false positives because empty is normamlized
    return ((x_btm == 0) and (btm_clusive() == Clusive::in))
        or ((x_top == 0) and (top_clusive() == Clusive::in))
        or (0 < x_btm and x_top < 0);
  }
};

template<std::three_way_comparable X, std::three_way_comparable Y>
constexpr auto operator==(interval<X> x, interval<Y> y)
    ARROW(x.btm_end() == y.btm_end() and x.top_end() == y.top_end())

template<std::three_way_comparable X, std::three_way_comparable Y>
constexpr std::partial_ordering
    operator<=>(Read<interval<X>> x, Read<interval<Y>> y) {
  if(x.empty())
    return (y.empty()) ? std::partial_ordering::equivalent
                       : std::partial_ordering::less;
  else if(y.empty()) return std::partial_ordering::greater;
  else {
    auto const btms = std::pair{x.btm(), x.clusive() == Clusive::ex}
                  <=> std::pair{y.btm(), y.clusive() == Clusive::ex};
    auto const tops = std::pair{x.top(), x.clusive() == Clusive::in}
                  <=> std::pair{y.top(), y.clusive() == Clusive::in};

    switch(btms) {
      case std::partial_ordering::less:
        switch(tops) {
          case std::partial_ordering::greater:
          case std::partial_ordering::equivalent:
            return std::partial_ordering::greater;
        }
        break;
      case std::partial_ordering::equivalent: return tops;
      case std::partial_ordering::greater:
        switch(tops) {
          case std::partial_ordering::less:
          case std::partial_ordering::equivalent:
            return std::partial_ordering::less;
        }
        break;
    }
    return std::partial_ordering::unordered;
  }
}

template<std::three_way_comparable X, std::three_way_comparable Y>
constexpr auto operator+(Read<interval<X>> x, Read<interval<Y>> y) ARROW(
    (x.empty() or y.empty())
        ? interval<std::invoke_result_t<std::plus<>, X, Y>>{}
        : interval{x.btm_end() + y.btm_end(), x.top_end() + y.top_end()})

template<std::three_way_comparable X>
constexpr auto operator-(Read<interval<X>> x)
    ARROW(interval{-x.top_end(), -x.btm_end()})

template<std::three_way_comparable X>
constexpr auto operator+(Read<interval<X>> x)
    ARROW(interval{+x.btm_end(), +x.top_end()})

template<std::three_way_comparable X, std::three_way_comparable Y>
constexpr auto operator-(Read<interval<X>> x, Read<interval<Y>> y)
    ARROW(x + (-y))

template<std::three_way_comparable X, std::three_way_comparable Y>
constexpr auto operator*(Read<interval<X>> x, Read<interval<Y>> y)
    -> interval<std::invoke_result_t<std::multiplies<>, X, Y>> {
  using prod_t = decltype(std::declval<X>() * std::declval<Y>());

  if(x.empty() or y.empty()) return {};

  std::array<end<prod_t>, 4> prods{
      // clang-format off
                                  /* y.btm_end   ,             y.top_end */
        /*x.btm_end*/  x.btm_end() * y.btm_end() , x.btm_end * y.top_end(),
        /*x.top_end*/  x.top_end() * y.btm_end() , x.top_end * y.top_end()
      // clang-format on
  };
  auto const btm_end =
      *std::min_element(prods.begin(), prods.end(), project_less([
                        ] FN(std::pair{_.point, _.clusive == Clusive::ex})));
  auto const top_end =
      *std::max_element(prods.begin(), prods.end(), project_less([
                        ] FN(std::pair{_.point, _.clusive == Clusive::in})));
  return interval{btm_end, top_end};
}
// tricky cases [-1,1) * [-1,1] = [-1,1]

static_assert(!interval<int>{}.has(0));

#endif // INTERVAL_HPP_INCLUDE_GUARD
