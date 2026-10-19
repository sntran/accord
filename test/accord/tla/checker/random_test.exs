defmodule Accord.TLA.Checker.RandomTest do
  # The expected values come from TLC (with -fp 0 and -seed 15041980).
  use ExUnit.Case, async: true

  alias Accord.TLA.Checker.{Fingerprint, Random, Value}

  defp tlcfp(v) do
    import Bitwise
    fp = Fingerprint.value(Fingerprint.new(), v) &&& 0xFFFFFFFF
    if fp >= 0x80000000, do: fp - 0x100000000, else: fp
  end

  test "the fingerprints of values are the fingerprints of TLC" do
    cases = [
      {true, -767_817_129},
      {false, 119_336_818},
      {0, 231_594_371},
      {1, -1_504_394_061},
      {-1, 1_627_259_383},
      {123_456_789, -266_290_336},
      {"a", -1_022_804_895},
      {"hello", -1_730_004_112},
      {MapSet.new(), 439_769_674},
      {Value.set([1, 2, 3]), 2_005_681_404},
      {Value.tuple([]), 1_056_418_748},
      {Value.tuple([1, 2]), 690_999_242},
      {Value.record([{"a", 1}]), 708_139_487},
      {Value.fun(%{2 => 2, 3 => 3}), -1_446_284_990},
      {Value.interval(1, 5), 1_328_395_697},
      {Value.set([Value.set([1]), Value.set([2, 3])]), -286_534_044},
      {Value.tuple(["x", Value.set([1])]), -410_231_085},
      {Value.fun(%{"p" => "p", "q" => "q"}), 452_650_693}
    ]

    for {v, fp} <- cases, do: assert(tlcfp(v) == fp, Value.show(v))
  end

  test "the random values are the values of TLC for the same seed" do
    Random.setup(15_041_980)

    assert Random.element(Value.interval(1, 1000)) == 64

    assert Random.subset(5, {:interval, 1, 100_000_000}) ==
             Value.set([7_988_211, 11_837_730, 75_938_062, 77_221_235, 79_787_581])

    s = Value.interval(1, 200)

    assert Random.subset(3, {:times, [s, s, s]}) ==
             Value.set([
               Value.tuple([65, 122, 127]),
               Value.tuple([97, 146, 178]),
               Value.tuple([166, 165, 10])
             ])

    b = {:interval, 1, 4000}

    assert Random.subset(3, {:times, [b, b, b]}) ==
             Value.set([
               Value.tuple([1933, 2749, 3155]),
               Value.tuple([2237, 443, 2938]),
               Value.tuple([2540, 2137, 2721])
             ])

    assert Random.subset(2, {:fun_set, Value.set([1, 2, 3]), Value.interval(1, 10)}) ==
             Value.set([Value.tuple([4, 7, 3]), Value.tuple([7, 4, 4])])

    assert Random.element(
             {:record_set, [{"a", Value.interval(1, 10)}, {"b", Value.set(["x", "y"])}]}
           ) ==
             Value.record([{"a", 4}, {"b", "y"}])

    assert Random.element({:subset, Value.interval(1, 4)}) == Value.set([1, 2])

    assert Random.set_of_subsets(3, 2 / 5, Value.interval(1, 5)) ==
             Value.set([Value.set([1, 3]), Value.set([2, 5]), Value.set([3, 4, 5])])
  end
end
