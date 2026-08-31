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


def test_the_fork_checkout_opt_in_covers_the_candidate_only() -> None:
    workflow = _workflow("contribution-verify.yml")
    trusted = workflow.split("Check out the trusted validator", 1)[1].split("- name:", 1)[0]
    candidate = workflow.split("Check out the untrusted contribution", 1)[1].split("- name:", 1)[0]

    # checkout blocks fork code under workflow_run by default. Opting in is what lets the
    # candidate be fetched at all; granting it to the validator checkout would mean the
    # ruleset judging a contribution could come from the contribution.
    assert "allow-unsafe-pr-checkout: true" in candidate
    assert "allow-unsafe-pr-checkout" not in trusted
    assert "persist-credentials: false" in candidate


def test_the_workspace_step_fails_when_no_workspace_resolves() -> None:
    workflow = _workflow("contribution-verify.yml")
    step = workflow.split("Resolve the Lean workspace", 1)[1].split("- name:", 1)[0]
    code = "\n".join(line for line in step.splitlines() if not line.lstrip().startswith("#"))

    # `echo "path=$(script)"` exits with the status of echo, so a workspace that could not
    # be resolved passed this step and handed an empty path to the elaboration stage.
    assert 'echo "path=$(' not in code
    assert 'workspace="$(trusted/scripts/lean_workspace.sh "$commit")"' in step
    assert 'test -n "$workspace"' in step


def test_the_verifier_reports_its_result_back_to_the_pull_request() -> None:
    workflow = _workflow("contribution-verify.yml")
    report = workflow.split("  report:\n", 1)[1]

    # workflow_run runs attach to the branch, not the pull request, so without an explicit
    # check run a failed verification leaves the PR showing only the rewritable
    # `contribution-pr` check — that is, green.
    assert "needs: [resolve, verify]" in report
    assert "if: always() && needs.resolve.result == 'success'" in report
    assert "checks: write" in report
    assert 'gh api -X POST "repos/$GH_REPO/check-runs"' in report
    assert '-f head_sha="$HEAD_SHA"' in report
    assert "conclusion=failure" in report


def test_the_merge_acts_as_the_app_not_as_the_ambient_token() -> None:
    workflow = _workflow("contribution-merge.yml")

    # A push made with GITHUB_TOKEN triggers no workflow, so merging with it left
    # contribution-index unrun and the generated indexes stale. The app is a separate
    # identity whose push fires push triggers normally.
    assert "actions/create-github-app-token@" in workflow
    assert "app-id: ${{ vars.CONTRIB_APP_ID }}" in workflow
    assert "private-key: ${{ secrets.CONTRIB_APP_PRIVATE_KEY }}" in workflow
    assert "GH_TOKEN: ${{ secrets.GITHUB_TOKEN }}" not in workflow
    assert workflow.count("GH_TOKEN: ${{ steps.app-token.outputs.token }}") == 4

    # Reading another run's artifact needs actions: read, which the app deliberately does
    # not hold, so that one step keeps the ambient token.
    assert "github-token: ${{ secrets.GITHUB_TOKEN }}" in workflow


def test_the_merge_workflow_token_keeps_only_the_permission_it_still_uses() -> None:
    workflow = _workflow("contribution-merge.yml")
    header = workflow.split("concurrency:", 1)[0]

    assert "actions: read" in header
    for write in ("contents: write", "pull-requests: write", "issues: write"):
        assert write not in header
