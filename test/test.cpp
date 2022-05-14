#define CATCH_CONFIG_MAIN

#include <catch2/catch.hpp>
#include <bounded/interval.hpp>

using namespace bounded;
using namespace std::literals;

TEST_CASE("All empty intervals (of the same type) are ==") {
  STATIC_REQUIRE(interval{ex(0), ex(0)} == interval<int>{});
  STATIC_REQUIRE(interval{ex(0), ex(0)} == interval{ex(1), ex(-1)});
  STATIC_REQUIRE(interval{ex(2), in(2)} == interval{in(1), in(-1)});

  STATIC_REQUIRE(std::three_way_comparable<interval<int>>);

  STATIC_REQUIRE(interval{ex(interval<int>{}), ex(interval<int>{})}
                 == interval<interval<int>>{});
}

TEST_CASE("If both endpoints are the same and at least one is exclusive, "
          "the interval is empty") {
  STATIC_REQUIRE(interval{ex(0), ex(0)}.empty());
  STATIC_REQUIRE(interval{in(0), ex(0)}.empty());
  STATIC_REQUIRE(interval{ex(0), in(0)}.empty());

  STATIC_REQUIRE(
      interval{ex(interval<int>{}), ex(interval<int>{})}.empty());
  STATIC_REQUIRE(
      interval{in(interval<int>{}), ex(interval<int>{})}.empty());
  STATIC_REQUIRE(
      interval{ex(interval<int>{}), in(interval<int>{})}.empty());

  STATIC_REQUIRE(interval{ex("a"sv), ex("a"sv)}.empty());
  STATIC_REQUIRE(interval{in("a"sv), ex("a"sv)}.empty());
  STATIC_REQUIRE(interval{ex("a"sv), in("a"sv)}.empty());
}

TEST_CASE("An empty interval contains no element") {
  STATIC_REQUIRE(!interval<int>{}.has(0));
  STATIC_REQUIRE(!interval<int>{}.has(1));
}

TEST_CASE("Inclusive endpoints are contained") {
  STATIC_REQUIRE(interval{in(0), in(0)}.has(0));

  STATIC_REQUIRE(interval{in(0), in(1)}.has(0));
  STATIC_REQUIRE(interval{in(0), ex(1)}.has(0));

  STATIC_REQUIRE(interval{in(0), in(1)}.has(1));
  STATIC_REQUIRE(interval{ex(0), in(1)}.has(1));

  STATIC_REQUIRE(interval{in("a"sv), in("b"sv)}.has("a"sv));
  STATIC_REQUIRE(interval{in("a"sv), ex("b"sv)}.has("a"sv));
  STATIC_REQUIRE(interval{in("a"sv), in("b"sv)}.has("b"sv));
  STATIC_REQUIRE(interval{ex("a"sv), in("b"sv)}.has("b"sv));

  STATIC_REQUIRE(
      interval{in(interval<int>{}), in(interval{in(0), in(1)})}.has(
          interval<int>{}));
}

TEST_CASE("Exclusive endpoints are not contained") {
  STATIC_REQUIRE(!interval{ex(0), ex(0)}.has(0));

  STATIC_REQUIRE(!interval{ex(0), ex(1)}.has(0));
  STATIC_REQUIRE(!interval{ex(0), ex(1)}.has(1));

  STATIC_REQUIRE(!interval{ex("a"sv), ex("b"sv)}.has("a"sv));
  STATIC_REQUIRE(!interval{ex("a"sv), ex("b"sv)}.has("b"sv));
}

TEST_CASE("The innards are inside but the outsides are not") {
  STATIC_REQUIRE(interval{ex(-1), ex(1)}.has(0));
  STATIC_REQUIRE(!interval{ex(-1), ex(1)}.has(2));
  STATIC_REQUIRE(!interval{ex(-1), ex(1)}.has(-2));
}

TEST_CASE("The empty interval annihilates under +") {
  STATIC_REQUIRE((interval<int>{} + interval{ex(0), ex(1)}).empty());
}
TEST_CASE("The empty interval annihilates under *") {
  STATIC_REQUIRE((interval<int>{} * interval{ex(0), ex(1)}).empty());
}

TEST_CASE("Interval addition adds respective endpoints") {
  STATIC_REQUIRE(interval{in(0), ex(1)} + interval{in(1), ex(2)}
                 == interval{in(1), ex(3)});
}

TEST_CASE("Interval multiplication looks at all endpoints") {
  STATIC_REQUIRE(interval{in(-1), ex(1)} * interval{in(-1), in(1)}
                 == interval{in(-1), in(1)});
}
