# Used by "mix format"
protocol_macros = [
  initial: 1,
  role: 1,
  track: 3,
  state: 2,
  state: 3,
  anystate: 1,
  on: 2,
  cast: 1,
  event: 1,
  event: 2,
  property: 2,
  model: 1,
  const: 2,
  state_timeout: 2,
  # Accord.Protocol.ModelBlock (inside `model ... do` blocks)
  sessions: 1,
  domain: 2,
  max_list_length: 1,
  state_constraint: 1,
  # Accord.Protocol.Block (inside `on ... do` blocks)
  reply: 1,
  goto: 1,
  guard: 1,
  update: 1,
  timeout: 1,
  branch: 2,
  # Accord.Protocol.Property (inside `property ... do` blocks)
  invariant: 1,
  invariant: 2,
  action: 1,
  liveness: 2,
  correspondence: 2,
  bounded: 2,
  ordered: 2,
  precedence: 2,
  reachable: 1,
  exclusive: 1,
  distinct: 2,
  forbidden: 1
]

[
  inputs: ["{mix,.formatter}.exs", "{config,lib,test}/**/*.{ex,exs}"],
  locals_without_parens: protocol_macros,
  export: [locals_without_parens: protocol_macros]
]
