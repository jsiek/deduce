import proof_checker


def test_statement_phases_share_kind_registry():
  expected = proof_checker._STATEMENT_PHASE_KINDS

  for phase in [
      "process_declaration",
      "type_check_stmt",
      "collect_env",
      "check_proofs",
  ]:
    assert proof_checker._STATEMENT_PHASE_REGISTRY[phase] == expected


def test_visibility_phase_uses_declaration_subset():
  assert proof_checker._STATEMENT_PHASE_REGISTRY[
      "process_declaration_visibility"] == proof_checker._DECLARATION_PHASE_KINDS
  assert set(proof_checker._DECLARATION_PHASE_KINDS).issubset(
      proof_checker._STATEMENT_PHASE_KINDS)
