import pytest

from core.archive import ArchiveError, RunDir, record_id


def test_round_files_and_done_marker(tmp_path):
    run = RunDir(tmp_path, "r1")
    run.create({"run_id": "r1", "seed": 0})
    assert run.exists() and run.config()["seed"] == 0
    assert run.next_round() == 0
    run.write(0, "prompt.md", "hello")
    run.write(0, "results.json", [{"a": 1}])
    assert run.read(0, "prompt.md") == "hello"
    assert run.read(0, "results.json") == [{"a": 1}]
    assert not run.round_done(0)
    run.mark_done(0)
    assert run.round_done(0) and run.done_rounds() == [0] and run.next_round() == 1
    with pytest.raises(ArchiveError):
        run.write(0, "prompt.md", "rewritten")


def test_run_cannot_be_created_twice(tmp_path):
    RunDir(tmp_path, "r1").create({"x": 1})
    with pytest.raises(ArchiveError):
        RunDir(tmp_path, "r1").create({"x": 2})


def test_archive_is_append_only_and_idempotent(tmp_path):
    run = RunDir(tmp_path, "r1")
    run.create({})
    recs = [{"record_id": record_id("r1", 0, 0, "net", k), "v": k} for k in (0, 1)]
    assert run.append_archive(recs) == 2
    assert run.append_archive(recs) == 0  # replaying a round adds nothing
    run.append_archive([{"record_id": record_id("r1", 1, 0, "net", 0), "v": 9}])
    got = run.read_archive()
    assert [r["v"] for r in got] == [0, 1, 9]
    with pytest.raises(ArchiveError):
        run.append_archive([{"v": 3}])
