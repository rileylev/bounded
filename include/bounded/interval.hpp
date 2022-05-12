#ifndef BOUNDED_INTERVAL_HPP_INCLUDE_GUARD
#define BOUNDED_INTERVAL_HPP_INCLUDE_GUARD

#include "impl/macros.hpp"

#include <assert.h>
#include <concepts>
#include <tuple>
#include <array>
#include <algorithm>
#include <compare>

#define ASSERT(...) assert(__VA_ARGS__)

namespace bounded {

namespace impl {
  // for switching
  enum class porder : char { lt = -1, eq = 0, gt = 1, un = 2 };

  constexpr porder to_porder(std::partial_ordering x) noexcept {
    if(std::is_lt(x)) return porder::lt;
    else if(std::is_eq(x)) return porder::eq;
    else if(std::is_gt(x)) return porder::gt;
    else return porder::un;
  }

  template<class Less = std::less<>>
  constexpr auto project_less(auto proj, Less less = {}) {
    return [ proj, less ](auto x, auto y) ARROW(less(proj(x), proj(y)));
  }
} // namespace impl

/**
 * Is it inclusive or exclusive?
 */
enum class Clusive : bool {
  in = true,
  ex = false,
};
constexpr Clusive operator*(Clusive x, Clusive y)
    NOEX(static_cast<Clusive>(static_cast<bool>(x) and static_cast<bool>(y)))

template<class Poset>
struct end;
namespace impl {
  struct end_friends {
    friend constexpr bool operator==(end_friends, end_friends) = default;
    template<std::three_way_comparable P>
    friend constexpr auto operator+(end<P> x)
        ARROW(end{+x.point, x.clusive})
    template<std::three_way_comparable P>
    friend constexpr auto operator-(end<P> x)
        ARROW(end{-x.point, x.clusive})

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto operator+(end<X> x, end<Y> y)
        ARROW(end{x.point + y.point, x.clusive* y.clusive})

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto operator-(end<X> x, end<Y> y) ARROW(x + (-y))

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto operator*(end<X> x, end<Y> y)
        ARROW(end{x.point * y.point, x.clusive* y.clusive})
  };
} // namespace impl
/**
 * Represents either end of an interval
 */
template<class Poset>
struct end : impl::end_friends {
  Poset       point;
  Clusive     clusive;
  friend bool operator==(end, end) = default;

  constexpr end() = default;
  constexpr end(Poset point_, Clusive clusive_)
      : point{point_}, clusive{clusive_} {}
};
template<class X>
end(X, Clusive) -> end<X>;

template<class T>
constexpr end<T> ex(T x) RET(end{x, Clusive::ex})
template<class T>
constexpr end<T> in(T x)RET(end{x, Clusive::in})

using passing_traits::Read;

template<std::three_way_comparable Poset>
struct interval;
namespace impl {
  struct interval_friends {
    friend constexpr bool
        operator==(interval_friends, interval_friends) = default;
    // Allow or disallow operators on intervals over different types?
    // Probably should defer to the underlying types in general
    // If it makes sense to add X + Y, it probably makes sense to add
    // interval<X>
    // + interval<Y> I just wish the builtins were stricter. Allowed =/=
    // makes sense.
    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto
        operator==(interval<X> const& x, interval<Y> const& y)
            ARROW(x.btm_end() == y.btm_end() and x.top_end() == y.top_end())

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto
        operator+(interval<X> const& x, interval<Y> const& y)
            ARROW((x.empty() or y.empty())
                      ? interval<std::invoke_result_t<std::plus<>, X, Y>>{}
                      : interval{x.btm_end() + y.btm_end(),
                                 x.top_end() + y.top_end()})

    template<std::three_way_comparable X>
    friend constexpr auto operator-(interval<X> const& x)
        ARROW(interval{-x.top_end(), -x.btm_end()})
    template<std::three_way_comparable X>
    friend constexpr auto operator+(interval<X> const& x)
        ARROW(interval{+x.btm_end(), +x.top_end()})

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto
        operator-(interval<X> const& x, interval<Y> const& y)
            ARROW(x + (-y))

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto
        operator*(interval<X> const& x, interval<Y> const& y)
            -> interval<std::invoke_result_t<std::multiplies<>, X, Y>> {
      using prod_t = decltype(std::declval<X>() * std::declval<Y>());

      if(x.empty() or y.empty()) return {};

      std::array<end<prod_t>, 4> prods{
          // clang-format off
                                  /* y.btm_end   ,             y.top_end */
        /*x.btm_end*/  x.btm_end() * y.btm_end() , x.btm_end() * y.top_end(),
        /*x.top_end*/  x.top_end() * y.btm_end() , x.top_end() * y.top_end()
          // clang-format on
      };
      auto const btm_end = *std::min_element(
          prods.begin(),
          prods.end(),
          impl::project_less(
              [] FN(std::pair{_.point, _.clusive == Clusive::ex})));
      auto const top_end = *std::max_element(
          prods.begin(),
          prods.end(),
          project_less([] FN(std::pair{_.point, _.clusive == Clusive::in})));
      return interval{btm_end, top_end};
    }
    // tricky cases [-1,1) * [-1,1] = [-1,1]

    /**
     * Three-way-compare intervals by set inclusion: A < B iff A ⊂ B
     *
     *  - A <=> B <  0          iff  A ⊂ B
     *  - A <=> B == 0          iff  A = B
     *  - A <=> B >  0          iff  A ⊃ B
     *  - A <=> B == unordered  iff  A ≠ B, A ⊄ B, A ⊅ B
     *
     *  Examples:
     *  [0,1]  <  [0,2]
     *  [0,1) <=> (0,1] = unordered
     */
    // TODO: what does weak equivalence mean for subset inclusion?
    template<class X, class Y>
    friend constexpr std::partial_ordering
        operator<=>(interval<X> const& x_, interval<Y> const& y_) {
      // next best thing to inferring to pass by value (the compiler didn't
      // like that)
      Read<interval<X>> x = x_;
      Read<interval<Y>> y = y_;
      if(x.empty())
        return (y.empty()) ? std::partial_ordering::equivalent
                           : std::partial_ordering::less;
      else if(y.empty()) return std::partial_ordering::greater;
      else {
        // clusivity breaks ties
        // [0,1) vs (0,1) --- the exclusive interval starts a hair higher
        auto const btms =
            std::pair{x.btm(), x.btm_clusive() == Clusive::ex}
            <=> std::pair{y.btm(), y.btm_clusive() == Clusive::ex};
        // [0,1) vs [0,1] --- the inclusive interval ends a hair higher
        auto const tops =
            std::pair{x.top(), x.top_clusive() == Clusive::in}
            <=> std::pair{y.top(), y.top_clusive() == Clusive::in};
        using namespace impl;
        switch(to_porder(btms)) {
          case porder::lt:
            switch(to_porder(tops)) {
              case porder::gt:
              case porder::eq: return std::partial_ordering::greater;
              default: return std::partial_ordering::unordered;
            }
          case porder::eq: return tops;
          case porder::gt:
            switch(to_porder(tops)) {
              case porder::lt:
              case porder::eq: return std::partial_ordering::less;
              default: return std::partial_ordering::unordered; ;
            }
         default: return std::partial_ordering::unordered;
        }
      }
    }
  };
} // namespace impl

/**
 * Represents an interval in any `std::three_way_comparable` Poset.
 *
 * This is a structural type so it can be used as a non-type template
 * parameter. A name ending with a trailing underscore is morally private.
 */
template<std::three_way_comparable Poset>
struct interval : impl::interval_friends {
  /* To use this as a non-type template parameter, we can't use private.

   https://en.cppreference.com/w/cpp/language/template_parameters:
   "A non-type template parameter must have a structural type, which is one
  of the following...

   -  a literal class type with the following properties:

   -  all base classes and non-static data members are public and
  non-mutable and the types of all base classes and non-static data members
  are structural types or (possibly multi-dimensional) array thereof."
  */
  // private:
  Poset   btm_             = {};
  Poset   top_             = {};
  Clusive btm_clusive_ : 1 = Clusive::ex;
  Clusive top_clusive_ : 1 = Clusive::ex;

 public:
  READER(btm)
  READER(top)
  READER(btm_clusive)
  READER(top_clusive)

  constexpr auto btm_end() const ARROW(end{btm(), btm_clusive()})
  constexpr auto top_end() const ARROW(end{top(), top_clusive()})

  /**
   * Default to the empty interval
   */
  constexpr interval() = default;

  constexpr bool empty() const NOEX(*this == interval{})

  /**
   * Construct an interval from its two ends
   */
  constexpr interval(end<Poset> btm, end<Poset> top) noexcept(
      std::is_nothrow_move_constructible_v<Poset>and noexcept(
          interval{},
          this->btm() <=> this->top()))
      : btm_{std::move(btm.point)},
        top_{std::move(top.point)},
        btm_clusive_{btm.clusive},
        top_clusive_{top.clusive} {
    // normalize the degenerate cases
    using namespace impl;
    switch(to_porder(this->btm() <=> this->top())) {
      case porder::gt:
      case porder::un: *this = interval{}; break;
      case porder::eq:
        if((btm_clusive() == Clusive::ex) or (top_clusive() == Clusive::ex))
          *this = interval{};
      case porder::lt: return;
    }
  }

  /**
   * Singleton constructor
   *
   * TODO: implicit? explicit?
   */
  IMPLICIT() constexpr interval(Poset x) : interval(in(x), in(x)) {}

  /**
   * Does this interval contain x? x∈*this?
   */
  constexpr bool
      has(Read<Poset> x) noexcept(noexcept(x <=> btm(), x <=> top())) {
    auto const x_btm = x <=> btm();
    auto const x_top = x <=> top();

    if(x_btm == std::partial_ordering::unordered
       or x_top == std::partial_ordering::unordered)
      return false;
    // no false positives because empty is normalized
    return ((x_btm == 0) and (btm_clusive() == Clusive::in))
        or ((x_top == 0) and (top_clusive() == Clusive::in))
        or (0 < x_btm and x_top < 0);
  }
};

} // namespace bounded
#endif
