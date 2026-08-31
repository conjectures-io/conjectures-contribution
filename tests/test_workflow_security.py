from pathlib import Path

ROOT = Path(__file__).parents[1]
WORKFLOWS = ROOT / ".github" / "workflows"


def _workflow(name: str) -> str:
    return (WORKFLOWS / name).read_text()


def test_pull_request_workflow_has_no_privileged_runner_or_merge_artifact() -> None:
    workflow = _workflow("contribution-pr.yml")

    assert "group: DEV" not in workflow
    assert "verified-meta" not in workflow
    assert "Lean elaboration" not in workflow


def test_verifier_uses_the_default_branch_workflow_and_binds_one_pull_request() -> None:
    workflow = _workflow("contribution-verify.yml")
    sandbox_job = workflow.split("  verify:\n", 1)[1].split("  publish-metadata:\n", 1)[0]

    assert "workflows: ['contribution-pr']" in workflow
    assert 'gh api -X GET "repos/$GH_REPO/pulls"' in workflow
    assert "workflow_run.pull_requests[0]" not in workflow
    assert "permissions: {}" in sandbox_job
    assert "group: DEV" in sandbox_job
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


def test_the_verifier_resolves_forks_by_head_repository_not_by_commit() -> None:
    workflow = _workflow("contribution-verify.yml")

    # `commits/<sha>/pulls` returns an empty list for a fork head, so every fork
    # contribution failed to resolve. The event's head repository and branch are what
    # GitHub actually fills in for a pull_request run.
    assert "commits/$RUN_HEAD_SHA/pulls" not in workflow
    assert "workflow_run.head_repository.full_name" in workflow
    assert "workflow_run.head_branch" in workflow
    assert "$RUN_HEAD_SHA" in workflow
