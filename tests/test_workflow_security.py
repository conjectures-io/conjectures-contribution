from pathlib import Path

ROOT = Path(__file__).parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"


def _workflow(name: str) -> str:
    return (WORKFLOWS / name).read_text()


def test_pull_request_workflow_has_no_privileged_runner_or_merge_artifact() -> None:
    workflow = _workflow("contribution-pr.yml")

    assert "group: Default" not in workflow
    assert "verified-meta" not in workflow
    assert "Lean elaboration" not in workflow


def test_verifier_uses_default_branch_workflow_and_resolves_forks_by_sha() -> None:
    workflow = _workflow("contribution-verify.yml")
    sandbox_job = workflow.split("  verify:\n", 1)[1].split("  publish-metadata:\n", 1)[0]

    assert "workflows: ['contribution-pr']" in workflow
    assert "repos/$GH_REPO/commits/$RUN_HEAD_SHA/pulls" in workflow
    assert "workflow_run.pull_requests[0]" not in workflow
    assert "permissions: {}" in sandbox_job
    assert "group: Default" in sandbox_job
    assert "Run every rule again" in sandbox_job
    assert "verified-meta" in workflow


def test_merge_only_consumes_the_trusted_verifier_result() -> None:
    workflow = _workflow("contribution-merge.yml")

    assert "workflows: ['contribution-verify']" in workflow
    assert "workflow_run.event == 'workflow_run'" in workflow
    assert "workflow_run.path == '.github/workflows/contribution-verify.yml'" in workflow
    assert "name: verified-meta" in workflow
    assert workflow.index("Confirm the PR is still the one we verified") < workflow.index(
        "Label the pull request"
    )


def test_the_validator_comes_from_the_default_branch_not_the_pr_base() -> None:
    workflow = _workflow("contribution-verify.yml")
    trusted = workflow.split("Check out the trusted validator", 1)[1].split("- name:", 1)[0]

    assert "needs.resolve.outputs.trusted_sha" in trusted
    # A contributor chooses what to branch from, so the PR's base commit must never decide
    # which ruleset, pool or sandbox script judges it.
    assert "base_sha" not in trusted
