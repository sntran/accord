defmodule Mix.Tasks.Accord.Crosscheck do
  @moduledoc """
  Compares the native explorer with TLC on each protocol.

  TLC is the reference. For each protocol, the task runs `Accord.Explore`
  and TLC on the same finite model, and compares the state spaces and
  the verdict of each safety check. See `Accord.CrossCheck` for the
  comparisons.

  ## Usage

      mix accord.crosscheck                      # all protocols
      mix accord.crosscheck MyApp.Protocol       # one protocol
      mix accord.crosscheck --jobs 4             # protocols in parallel
      mix accord.crosscheck --max-states 50000   # explorer state limit
      mix accord.crosscheck --timeout 60         # TLC time limit (seconds)
      mix accord.crosscheck --keep               # keep the TLC files and output
      mix accord.crosscheck --mutants 5          # also 5 mutants of each protocol
      mix accord.crosscheck --mutants 5 --seed 7 # another set of mutants
      mix accord.crosscheck --random 50          # 50 random protocols
      mix accord.crosscheck --random 50 --seed 9 # 50 other random protocols

  ## Mutants

  With `--mutants N`, the task also checks N mutants of each protocol
  (see `Accord.CrossCheck.Mutant`). A mutant is a small change to the
  IR, such as a guard removed or a branch sent to a different state. Many
  mutants have violations, so the cross-check also compares their
  counterexamples. The same seed gives the same mutants.

  ## Random protocols

  With `--random N`, the task writes N random protocols (see
  `Accord.CrossCheck.RandomProtocol`), from the seeds `--seed` to
  `--seed + N - 1`, and checks them instead of the project protocols.
  The source of each random protocol goes into the work directory. Use
  `--keep` to keep it.

  The task also checks protocols with `tla: :off`. It makes their spec
  from the IR, as `Accord.Test.TLACheck` does.

  The task fails when a comparison finds a difference. A protocol that
  has no TLA+ spec, or that uses a feature that the explorer does not
  support, is reported but does not make the task fail.

  TLC must be available, as for `mix accord.check`.
  """

  use Mix.Task

  alias Accord.CrossCheck
  alias Accord.CrossCheck.{Mutant, RandomProtocol, Report, TLC}

  @shortdoc "Compare the native explorer with TLC"

  @impl Mix.Task
  def run(args) do
    Mix.Task.run("compile", [])

    {opts, names, _} =
      OptionParser.parse(args,
        strict: [
          jobs: :integer,
          max_states: :integer,
          timeout: :integer,
          keep: :boolean,
          mutants: :integer,
          seed: :integer,
          random: :integer
        ]
      )

    jar = TLC.find_jar() || Mix.raise("tla2tools.jar not found (see mix help accord.check)")

    root = Path.join(System.tmp_dir!(), "accord_crosscheck_#{System.os_time()}")

    protocols =
      cond do
        count = opts[:random] -> random_protocols(count, opts, root)
        names == [] -> discover_protocols()
        true -> Enum.map(names, &Module.concat([&1]))
      end

    run_opts = [
      jar: jar,
      max_states: Keyword.get(opts, :max_states, 200_000),
      timeout: Keyword.get(opts, :timeout, 120)
    ]

    jobs = Enum.flat_map(protocols, &jobs(&1, opts))

    reports =
      jobs
      |> Task.async_stream(
        fn {subject, name, extra} ->
          dir = Path.join(root, name)

          report =
            CrossCheck.run(subject, run_opts |> Keyword.put(:dir, dir) |> Keyword.merge(extra))

          Mix.shell().info(Report.format(report))
          report
        end,
        max_concurrency: Keyword.get(opts, :jobs, 2),
        timeout: :infinity,
        ordered: true
      )
      |> Enum.map(fn {:ok, report} -> report end)

    if Keyword.get(opts, :keep, false) do
      Mix.shell().info("TLC files are in #{root}")
    else
      File.rm_rf(root)
    end

    summarize(reports)
  end

  # Compiles `count` random protocols. Their source goes into the work
  # directory, so that a difference can be reproduced.
  defp random_protocols(count, opts, root) do
    first = Keyword.get(opts, :seed, 1)
    dir = Path.join(root, "random")
    File.mkdir_p!(dir)

    Enum.flat_map(first..(first + count - 1)//1, fn seed ->
      case RandomProtocol.compile(seed) do
        {:ok, module, code} ->
          File.write!(Path.join(dir, "p#{seed}.ex"), code)
          [module]

        {:error, reason, code} ->
          File.write!(Path.join(dir, "p#{seed}.ex"), code)
          Mix.shell().info("seed #{seed}: not compared (#{String.slice(reason, 0, 120)})")
          []
      end
    end)
  end

  # The original protocol, then its mutants (with --mutants N).
  defp jobs(mod, opts) do
    original = {mod, inspect(mod), []}

    case Keyword.get(opts, :mutants, 0) do
      0 ->
        [original]

      count ->
        config = Accord.Explore.Model.model_config(mod)
        seed = Keyword.get(opts, :seed, 1)

        mutants =
          for m <- Mutant.sample(mod.__ir__(), count, seed) do
            {m.ir, inspect(m.ir.name), [config: config, label: m.description]}
          end

        [original | mutants]
    end
  end

  defp summarize(reports) do
    outcomes = Enum.flat_map(reports, & &1.outcomes)
    count = fn status -> Enum.count(outcomes, &(&1.status == status)) end
    errors = Enum.count(reports, & &1.error)
    failed = reports |> Enum.reject(&Report.ok?/1) |> Enum.reject(& &1.error)

    Mix.shell().info(
      "\n#{length(reports)} protocols: #{count.(:match)} match, #{count.(:mismatch)} mismatch, " <>
        "#{count.(:inconclusive)} inconclusive, #{count.(:skipped)} skipped, " <>
        "#{errors} not compared"
    )

    if failed != [] do
      names = Enum.map_join(failed, ", ", &inspect(&1.protocol))
      Mix.raise("cross-check found differences in: " <> names)
    end
  end

  defp discover_protocols do
    Mix.Project.compile_path()
    |> Path.join("*.beam")
    |> Path.wildcard()
    |> Enum.map(&(&1 |> Path.basename(".beam") |> String.to_atom()))
    |> Enum.filter(fn mod ->
      Code.ensure_loaded?(mod) and function_exported?(mod, :__tla_span__, 1) and
        function_exported?(mod, :__ir__, 0)
    end)
    |> Enum.sort()
  end
end
