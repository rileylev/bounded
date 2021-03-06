#ifndef INCLUDE_GUARD_bounded_interval_hpp
#define INCLUDE_GUARD_bounded_interval_hpp

#include "impl/macros.hpp"

#include <concepts>
#include <functional>
#include <array>
#include <algorithm>
#include <compare>

namespace bounded {
/**
 * Does a type look like an additive group?
 *
 * In this library, this concept is used to prevent us from trying to add
 * intervals of strings as if they were numbers.
 */
template<class T>
concept additive_group = requires(T x, T y) {
  x + y;
  -x;
  T{};
};

/**
 * Does the type look like a rng (ring without identity)
 */
template<class T>
concept rng = additive_group<T> and requires(T x, T y) {
  x* y;
};

constexpr auto operator-(auto const& x, auto const& y) ARROW(x + (-y))

namespace impl {
  /**
   *  Ands all its arguments together
   *
   *  To appease clang-format
   */
  inline constexpr auto and_(auto... xs) RET((xs && ...))

  inline constexpr auto is_un = [](std::partial_ordering o)
      ARROW(o == std::partial_ordering::unordered);

  constexpr auto compose2 = [](auto f, auto g)
      RET([ f, g ](auto&&... args) ARROW(f(g(FWD(args)...))));
  inline constexpr auto compose_() NOEX([](auto&& x) ARROW(FWD(x)))
  inline constexpr auto compose_(auto&& f) ARROW(FWD(f))
  inline constexpr auto compose_(auto&& f, auto&&... fs)
      ARROW(compose2(FWD(f), compose_(FWD(fs)...)))
  /**
   * Compose functions
   *
   * Rightmost function is applied first. If no arguments are passed,
   * return identity.
   */
  inline constexpr auto compose = LIFT(compose_);

  /**
   *  A partial order enum for use with switch/case
   */
  enum class porder : char { lt, eq, gt, un };

  /**
   * Convert a `std::partial_ordering' to `impl::porder'
   */
  constexpr porder to_porder(std::partial_ordering x)
      NOEX(std::is_lt(x)   ? porder::lt
           : std::is_eq(x) ? porder::eq
           : std::is_gt(x) ? porder::gt
                           : porder::un)

  /**
   * Convert a partial_ordering to a total_ordering with precondition
   * it is only defined on totally-ordered subsets
   */
  inline constexpr auto assume_total =
      [](std::partial_ordering o) ANOEXCEPT() -> std::weak_ordering {
    using namespace impl;
    switch(to_porder(o)) {
      case porder::gt: return std::weak_ordering::greater;
      case porder::eq: return std::weak_ordering::equivalent;
      case porder::lt: return std::weak_ordering::less;
      case porder::un: ASSERT(false);
    };
  };

  using plus  = decltype([](auto... args) RET((args + ...)));
  using times = decltype([](auto... args) RET((args * ...)));
  using minus = decltype([](auto... args) RET((args - ...)));
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

template<class... Ps>
constexpr auto map(auto f, end<Ps> const&... es)
    ARROW(end{f(es.point...), (es.clusive * ...)})

namespace impl {
  struct end_friends {
    friend constexpr bool operator==(end_friends, end_friends) = default;
    template<std::three_way_comparable P>
    friend constexpr auto operator+(end<P> const& x) ARROW(map(plus{}, x))
    template<std::three_way_comparable P>
    friend constexpr auto operator-(end<P> const& x) ARROW(map(minus{}, x))

    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto operator+(end<X> const& x, end<Y> const& y)
        ARROW(map(plus{}, x, y))
    template<std::three_way_comparable X, std::three_way_comparable Y>
    friend constexpr auto operator*(end<X> const& x, end<Y> const& y)
        ARROW(map(times{}, x, y))
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
  constexpr end(Poset point_, Clusive clusive_) //
      noexcept(std::is_nothrow_move_constructible_v<Poset>)
      : point{std::move(point_)}, clusive{clusive_} {}

  template<class P>
  requires std::constructible_from<Poset, P>
      IMPLICIT(std::convertible_to<P, Poset>)
  constexpr end(end<P> x) NOEX_CONS(end(Poset{x.point}, x.clusive)) {}
};

/**
 * Create an EXclusive end
 */
template<class T>
constexpr end<T> ex(T x) NOEX(end{x, Clusive::ex})
/**
 * Create an INclusive end
 */
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
  inline constexpr auto break_tie =
      [](auto o, auto breaker) NOEX(std::is_eq(o) ? breaker : o);
  inline constexpr auto end_cmp =                     //
      [](Clusive target)                              //
      RET([=](auto cmp)                               //
          RET([=](auto const& xend, auto const& yend) //
              ARROW(break_tie(cmp(xend.point, yend.point),
                              ((xend.clusive == target)
                               <=> (yend.clusive == target))))));
  inline constexpr auto btm_cmp = end_cmp(Clusive::ex);
  inline constexpr auto top_cmp = end_cmp(Clusive::in);
}

inline constexpr auto subset_cmp = []<class Cmp>(Cmp cmp) RET(
    [=]<class Xbtm, class Xtop, class XC, class Ybtm, class Ytop, class YC>(
        interval<Xbtm, Xtop, XC> const& x,
        interval<Ybtm, Ytop, YC> const& y) -> std::partial_ordering {
      static_assert(
          comparable_by<Xbtm, Ybtm, Cmp> && comparable_by<Xtop, Ytop, Cmp>);
      using namespace impl;
      switch(x.empty() << 1 | y.empty()) {
        case 0b11: return std::partial_ordering::equivalent;
        case 0b10: return std::partial_ordering::less;
        case 0b01: return std::partial_ordering::greater;
        default:
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
                default: return std::partial_ordering::unordered;
              }
            case porder::un: return std::partial_ordering::unordered;
          }
      }
    });

namespace impl {
  template<class T>
  using cmp_t = std::remove_reference_t<decltype(std::declval<T>().cmp())>;

  template<class... Ts>
  using common_cmp_t = std::common_type_t<cmp_t<Ts>...>;

  template<class T>
  constexpr auto empty_if(bool cond, T x) ARROW(cond ? T{} : x)
}

template<class... Is>
requires std::is_empty_v<impl::common_cmp_t<Is...>>
constexpr auto map_increasing(auto f, Is const&... is) //
    ARROW(impl::empty_if((is.empty() or ...),
                         interval{map(f, is.btm_end()...),
                                  map(f, is.top_end()...),
                                  impl::common_cmp_t<Is...>{}}))
template<class... Is>
requires std::is_empty_v<impl::common_cmp_t<Is...>>
constexpr auto map_decreasing(auto f, Is const&... is) //
    ARROW(impl::empty_if((is.empty() or ...),
                         interval{map(f, is.top_end()...),
                                  map(f, is.btm_end()...),
                                  impl::common_cmp_t<Is...>{}}))

namespace impl {
  template<class xb, class xt, class yb, class yt>
  using cross_product_t =
      std::remove_reference_t<decltype((xb{} * yb{}) + (xb{} * yt{})
                                       + (xt{} * yb{}) + (xt{} * yt{}))>;

  using T = cross_product_t<int, int, int, int>;
  template<class Xb, class Xt, class Yb, class Yt, class Cmp>
  using product_interval_t =
      interval<cross_product_t<Xb, Xt, Yb, Yt>,
               cross_product_t<Xb, Xt, Yb, Yt>,
               Cmp>;

  struct interval_friends {
    friend constexpr bool
        operator==(interval_friends, interval_friends) = default;
    friend constexpr auto operator==(auto const& x, auto const& y)
        ARROW(x.btm_end() == y.btm_end() and x.top_end() == y.top_end())

    template<class Xbtm, class Xtop, class Xc, class Ybtm, class Ytop, class Yc>
    requires additive_group<std::invoke_result_t<plus, Xbtm, Xtop, Ybtm, Ytop>>
    friend constexpr auto
        operator+(interval<Xbtm, Xtop, Xc> const& x,
                  interval<Ybtm, Ytop, Yc> const& y)
            ARROW(map_increasing(plus{}, x, y))

    friend constexpr auto operator-(auto const& x)
        ARROW(map_decreasing(minus{}, x))
    friend constexpr auto operator+(auto const& x)
        ARROW(map_increasing(plus{}, x))

    template<class Xbtm,
             class Xtop,
             class Xc,
             class Ybtm,
             class Ytop,
             class Yc,
             class Cmp = std::common_type_t<Xc, Yc>>
    friend constexpr auto
        operator*(interval<Xbtm, Xtop, Xc> const& x,
                  interval<Ybtm, Ytop, Yc> const& y)
            -> product_interval_t<Xbtm, Xtop, Ybtm, Ytop, Cmp>
    requires std::is_empty_v<Cmp> //
        and rng<cross_product_t<Xbtm, Xtop, Ybtm, Ytop>> {
      if(x.empty() or y.empty()) return {};

      Cmp        cmp{};
      auto const common_array = [](auto... xs) RET(
          std::array{end<cross_product_t<Xbtm, Xtop, Ybtm, Ytop>>{xs}...});
      auto const prods = common_array( // clang-format off
        x.btm_end() * y.btm_end()   ,   x.btm_end() * y.top_end(),
        x.top_end() * y.btm_end()   ,   x.top_end() * y.top_end()
      ); // clang-format on
      constexpr auto lt = compose(LIFT(std::is_lt), assume_total);
      // This is what std does if you sort NaNs.
      // TODO: is it better to be stricter?
      auto const btm_end =
          *std::min_element(prods.begin(),
                            prods.end(),
                            compose(lt, btm_cmp(cmp)));
      auto const top_end =
          *std::max_element(prods.begin(),
                            prods.end(),
                            compose(lt, top_cmp(cmp)));
      return interval{btm_end, top_end};
    }

    /**
     * Three-way-compare intervals by set inclusion: A < B iff A ??? B
     *
     *  - A <=> B <  0          iff  A ??? B
     *  - A <=> B == 0          iff  A = B
     *  - A <=> B >  0          iff  A ??? B
     *  - A <=> B == unordered  iff  A ??? B, A ??? B, A ??? B
     *
     *  Examples:
     *  [0,1]  <  [0,2]
     *  [0,1) <=> (0,1] = unordered
     */
    template<class Xbtm,
             class Xtop,
             class Xc,
             class Ybtm,
             class Ytop,
             class Yc,
             class Cmp = std::common_type_t<Xc, Yc>>
    requires std::is_empty_v<Cmp>          //
        and comparable_by<Xbtm, Ybtm, Cmp> //
        and comparable_by<Xtop, Ytop, Cmp>
    friend constexpr auto
        operator<=>(interval<Xbtm, Xtop, Xc> const& x,
                    interval<Ybtm, Ytop, Yc> const& y)
            ARROW(subset_cmp(Cmp{})(x, y))
  };
}
/**
 * Represents an interval in any `std::three_way_comparable' Poset.
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
    ASSERT(cmp_(Btm{}, Top{}) == 0); // an empty interval has no elements
    return *this == interval{};
  }
  constexpr operator bool() NOEX(empty())

  /**
   * Construct an interval from its two ends
   */
  constexpr interval(end<Btm> btm, end<Top> top, Cmp cmp = {}) //
      noexcept(impl::and_(std::is_nothrow_move_constructible_v<Btm>,
                          std::is_nothrow_move_constructible_v<Top>,
                          std::is_nothrow_default_constructible_v<interval>,
                          noexcept(cmp_(this->btm(), this->top()))))
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

  template<class B, class T, class C>
  requires std::constructible_from<Btm, B> //
      and std::constructible_from<Top, T>  //
      and std::constructible_from<Cmp, C>
      IMPLICIT(impl::and_(std::convertible_to<B, Btm>,
                          std::convertible_to<T, Top>,
                          std::convertible_to<C, Cmp>))
  constexpr interval(interval<B, T, C> const& x)
      NOEX_CONS(interval(Btm{x.btm_end()}, Top{x.top_end()}, Cmp{x.cmp})){};

  /**
   * Does this interval contain x according to cmp? x ???_cmp *this?
   */
  template<class T, class Cmp_>
  requires comparable_by<Btm, T, Cmp_> && comparable_by<T, Top, Cmp_>
  constexpr bool has(T const& x, Cmp_ cmp) //
      noexcept(noexcept(cmp(x, btm()), cmp(x, top()))) {
    auto const x_btm = cmp(x, btm());
    auto const x_top = cmp(x, top());

    // no false positives because empty is normalized
    auto const ordered =
        not(impl::is_un(x_btm)) and not(impl::is_un(x_top));
    return ordered
       and (((x_btm == 0) and (btm_clusive() == Clusive::in))
            or ((x_top == 0) and (top_clusive() == Clusive::in))
            or (0 < x_btm and x_top < 0));
  }
  /**
   * Does this interval contain x? x???*this?
   */
  template<class T>
  constexpr bool has(T const& x) NOEX(has(x, cmp_))
};
}
#endif
