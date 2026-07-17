defmodule Accord.MixProject do
  use Mix.Project

  @version "0.1.0"
  @source_url "https://github.com/QuinnWilton/accord"

  def project do
    [
      app: :accord,
      version: @version,
      elixir: "~> 1.19",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      dialyzer: [
        plt_add_apps: [:ex_unit, :mix],
        plt_local_path: "priv/plts/project.plt",
        plt_core_path: "priv/plts/core.plt"
      ],

      # Hex
      description: "Runtime protocol contracts for Elixir with blame assignment.",
      package: package(),
      docs: docs(),
      source_url: @source_url,
      homepage_url: @source_url,

      # Testing
      elixirc_paths: elixirc_paths(Mix.env())
    ]
  end

  def application do
    [
      extra_applications: [:logger]
    ]
  end

  # examples/ compiles in dev and test so CI breaks when a DSL change
  # breaks an example — protocol compilation runs the full validation
  # pipeline and TLA+ emission, so "the examples compile" means "the
  # examples validate and produce specs". Excluded from :prod to keep
  # the hex package lean.
  defp elixirc_paths(:test), do: ["lib", "test/support", "examples"]
  defp elixirc_paths(:dev), do: ["lib", "examples"]
  defp elixirc_paths(_), do: ["lib"]

  defp deps do
    [
      {:pentiment, "~> 0.1.5"},
      {:propcheck, "~> 1.4"},
      {:stream_data, "~> 1.0", only: [:dev, :test]},
      {:assert_boundary, "~> 0.1.0", only: :test},
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      {:ex_doc, "~> 0.35", only: :dev, runtime: false},
      # The HTTP/2 example wires the accord monitor between a client and a live
      # Bandit server to detect real spec divergences. Bandit (and its transitive
      # hpax/thousand_island) is only needed there, so it stays out of :prod.
      {:bandit, "~> 1.12", only: [:dev, :test]}
    ]
  end

  defp package do
    [
      licenses: ["MIT"],
      links: %{
        "GitHub" => @source_url
      },
      files: ~w(lib mix.exs README.md LICENSE .formatter.exs)
    ]
  end

  defp docs do
    [
      main: "Accord",
      source_ref: "v#{@version}",
      source_url: @source_url
    ]
  end
end
