#ifndef BOUNDED_INTERVAL_HPP_INCLUDE_GUARD

#define BOUNDED_INTERVAL_HPP_INCLUDE_GUARD

#include "impl/macros.hpp"

#include <concepts>
#include <tuple>
#include <array>
#include <algorithm>
#include <compare>

namespace bounded {

template<class T>
concept additive_group = requires(T x, T y) {
  x + y;
  -x;
  T{};
};

template<class T>
// string, string_view
concept concatenative_monoid = !additive_group<T> && requires(T x, T y) {
  T{};
  x + y;
  x.begin();
};

template<class T>
concept rng = requires(T x, T y) {
  T{};
  -x;
  x + y;
  x* y;
};

template<class T, class Cmp>
concept ordered_rng_with = rng<T> && requires(T x, T y, Cmp cmp) {
  { cmp(x, y) } -> std::convertible_to<std::weak_ordering>;
};

namespace impl {
  // for switching
  enum class porder : char { lt, eq, gt, un };

  constexpr porder to_porder(std::partial_ordering x) noexcept {
    if(std::is_lt(x)) return porder::lt;
    else if(std::is_eq(x)) return porder::eq;
    else if(std::is_gt(x)) return porder::gt;
    else return porder::un;
  }

  template<class Less = std::less<>>
  constexpr auto project_less(auto proj, Less less = {}) {
    return [=](auto x, auto y) ARROW(less(proj(x), proj(y)));
  }
}

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
    friend constexpr auto operator+(end<P> const& x)
        ARROW(end{+x.point, x.clusive})
    template<std::three_way_comparable P>
    friend constexpr auto operator-(end<P> const& x)
        ARROW(end{-x.point, x.clusive})

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto operator+(end<X> const& x, end<Y> const& y)
        ARROW(end{x.point + y.point, x.clusive* y.clusive})

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto operator-(end<X> const& x, end<Y> const& y) ARROW(x + (-y))

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto operator*(end<X> const& x, end<Y> const& y)
        ARROW(end{x.point * y.point, x.clusive* y.clusive})
  };
}

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
constexpr end<T> ex(T x) NOEX(end{x, Clusive::ex})
template<class T>
constexpr end<T> in(T x)NOEX(end{x, Clusive::in})

template<class X, class Y, class Cmp>
concept comparable_by = requires(X x, Y y, Cmp cmp) {
  { cmp(x, y) } -> std::convertible_to<std::partial_ordering>;
};

template<class Btm, class Top = Btm, class Cmp = std::compare_three_way>
requires comparable_by<Btm, Top, Cmp>
struct interval;

namespace impl {
  inline constexpr auto end_cmp = [](Clusive target) //
      RET([=]<class Cmp>(Cmp cmp = {})               //
          RET([=](auto xend, auto yend) {
            auto const ptcmp = cmp(xend.point, yend.point);
            return (ptcmp == 0)
                     ? ((xend.clusive == target)
                        <=> (yend.clusive == target))
                     : ptcmp;
          }));
  inline constexpr auto const btm_cmp = end_cmp(Clusive::ex);
  inline constexpr auto const top_cmp = end_cmp(Clusive::in);

  struct interval_friends {
    friend constexpr bool
        operator==(interval_friends, interval_friends) = default;
    friend constexpr auto operator==(auto const& x, auto const& y)
        ARROW(x.btm_end() == y.btm_end() and x.top_end() == y.top_end())

   private:
    using plus = decltype([](auto... args) RET((args + ...)));

   public:
    template<class Xbtm, class Xtop, class Ybtm, class Ytop, class Cmp>
    requires std::is_empty_v<Cmp> and
        // TODO: is this the correct constraint?
        additive_group<std::invoke_result_t<plus, Xbtm, Xtop, Ybtm, Ytop>>
    friend constexpr auto operator+(interval<Xbtm, Xtop, Cmp> const& x,
                                    interval<Ybtm, Ytop, Cmp> const& y)
        ARROW((x.empty() or y.empty())
                  ? interval<std::invoke_result_t<std::plus<>, Xbtm, Ybtm>,
                             std::invoke_result_t<std::plus<>, Xtop, Ytop>,
                             Cmp>{}
                  : interval{x.btm_end() + y.btm_end(),
                             x.top_end() + y.top_end(),
                             Cmp{}})

    friend constexpr auto operator-(auto const& x)
        ARROW(interval{-x.top_end(), -x.btm_end(), x.cmp()})
    friend constexpr auto operator+(auto const& x)
        ARROW(interval{+x.btm_end(), +x.top_end(), x.cmp()})

    friend constexpr auto operator-(auto const& x, auto const& y)
        ARROW(x + (-y))

   private:
    template<class X, class Y>
    using cross_product_t = decltype([](X x, Y y) {
      // clang-format off
      return x.btm() * y.btm() + x.top() * y.btm()
           + x.btm() * y.top() + x.top() * y.top();
      // clang-format on
    }({}, {}));
    template<class X, class Y, class Cmp>
    using product_interval_t =
        interval<cross_product_t<X, Y>, cross_product_t<X, Y>, Cmp>;

   public:
    template<class Xbtm, class Xtop, class Ybtm, class Ytop, class Cmp>
    friend constexpr auto
        operator*(interval<Xbtm, Xtop, Cmp> const& x,
                  interval<Ybtm, Ytop, Cmp> const& y)
            -> product_interval_t<decltype(x), decltype(y), Cmp>
    requires std::is_empty_v<Cmp> && rng<
        cross_product_t<decltype(x), decltype(y)>> {
      if(x.empty() or y.empty()) return {};
      Cmp cmp{};

      auto const common_array = [](auto... xs)
          RET(std::array{std::common_type_t<decltype(xs)...>{xs}...});

      auto prods = common_array(
          // clang-format off
        x.btm_end() * y.btm_end()   ,   x.btm_end() * y.top_end(),
        x.top_end() * y.btm_end()   ,   x.top_end() * y.top_end()
          // clang-format on
      );

      constexpr auto lt = comp(LIFT(std::is_lt), assume_total);
      // This is what std does if you sort NaNs.
      // TODO: is it better to be stricter?
      auto const btm_end =
          *std::min_element(prods.begin(),
                            prods.end(),
                            comp(lt, btm_cmp(cmp)));
      auto const top_end =
          *std::max_element(prods.begin(),
                            prods.end(),
                            comp(lt, top_cmp(cmp)));
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
    template<class Xbtm, class Xtop, class Ybtm, class Ytop, class Cmp>
    requires std::is_empty_v<Cmp>
    friend constexpr std::partial_ordering
        operator<=>(interval<Xbtm, Xtop, Cmp> const& x,
                    interval<Ybtm, Ytop, Cmp> const& y) {
      switch(x.empty() << 1 | y.empty()) {
        case 0b11: return std::partial_ordering::equivalent;
        case 0b10: return std::partial_ordering::less;
        case 0b01: return std::partial_ordering::greater;
        default:
          Cmp const cmp{};
          auto const btms = btm_cmp(cmp)(x.btm_end(), y.btm_end());
          auto const tops = top_cmp(cmp)(x.top_end(), y.top_end());
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
            case porder::un: return std::partial_ordering::unordered;
          }
      }
    }
  };
}
/**
 * Represents an interval in any `std::three_way_comparable` Poset.
 *
 * This is a structural type so it can be used as a non-type template
 * parameter. A name ending with a trailing underscore is morally private.
 */
template<class Btm, class Top, class Cmp>
requires comparable_by<Btm, Top, Cmp>
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
  Btm                       btm_             = {};
  Top                       top_             = {};
  Clusive                   btm_clusive_ : 1 = Clusive::ex;
  Clusive                   top_clusive_ : 1 = Clusive::ex;
  [[no_unique_address]] Cmp cmp_             = {};

 public:
  READER(btm)
  READER(top)
  READER(btm_clusive)
  READER(top_clusive)
  READER(cmp)

  constexpr auto btm_end() const ARROW(end{btm(), btm_clusive()})
  constexpr auto top_end() const ARROW(end{top(), top_clusive()})

  /**
   * Default to the empty interval
   */
  constexpr interval() = default;

  constexpr bool empty() const ANOEXCEPT(noexcept(*this == interval{})) {
    // what does empty mean if we don't default construct an empty?
    ASSERT(cmp_(Btm{}, Top{}) == 0);
    return *this == interval{};
  }

  /**
   * Construct an interval from its two ends
   */
  constexpr interval(end<Btm> btm, end<Top> top, Cmp cmp = {}) noexcept(
      std::is_nothrow_move_constructible_v<Btm>and
              std::is_nothrow_move_constructible_v<Top>and
              std::is_nothrow_default_constructible_v<interval>and noexcept(
                  cmp_(this->btm(), this->top())))
      : btm_{std::move(btm.point)},
        top_{std::move(top.point)},
        btm_clusive_{btm.clusive},
        top_clusive_{top.clusive},
        cmp_{std::move(cmp)} {
    using namespace impl;
    // normalize the degenerate cases
    switch(to_porder(cmp_(this->btm(), this->top()))) {
      case porder::gt:
      case porder::un: *this = interval{}; break;
      case porder::eq:
        if((btm_clusive() == Clusive::ex) or (top_clusive() == Clusive::ex))
          *this = interval{};
        break;
      case porder::lt: break;
    }
  }

  /**
   * Does this interval contain x? x∈*this?
   */
  constexpr bool
      has(auto const& x) noexcept(noexcept(cmp_(x, btm()), cmp_(x, top()))) {
    auto const x_btm = cmp_(x, btm());
    auto const x_top = cmp_(x, top());

    if(x_btm == std::partial_ordering::unordered
       or x_top == std::partial_ordering::unordered)
      return false;
    // no false positives because empty is normalized
    return ((x_btm == 0) and (btm_clusive() == Clusive::in))
        or ((x_top == 0) and (top_clusive() == Clusive::in))
        or (0 < x_btm and x_top < 0);
  }
};

// for comparing floats
constexpr std::weak_ordering assume_total(std::partial_ordering o)
    ANOEXCEPT() {
  using namespace impl;
  switch(to_porder(o)) {
    case porder::gt: return std::weak_ordering::greater;
    case porder::eq: return std::weak_ordering::equivalent;
    case porder::lt: return std::weak_ordering::less;
    case porder::un: ASSERT(false);
  }
}

template<class Cmp = std::compare_three_way>
inline constexpr auto assume_total_cmp(Cmp cmp = {})
    NOEX([cmp](auto x, auto y) ARROW(assume_total(x, y)))
} // namespace bounded
#endif
