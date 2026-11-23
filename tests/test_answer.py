"""The sections of an open-lane answer (core/open_lane/answer.py): headings as real sessions write them."""

from core.open_lane.answer import first_word, sections

REVIEW = ("VERDICT", "FOUND", "NOTES")
SCALING = ("CLAIM", "SCALING", "WHY IT HELPS", "NOTES")

# The reading of attn-max4-ptl-1 (round 6), shortened: the session's opening line ran into its answer, and the
# headings are in bold. The run's log said "no verdict" for it.
READER = ("I'll start by reading the locked proof's certificate and plan, then the checker's modules.**VERDICT:** clean\n\n"
          "**FOUND:**\n\nChecker closure read in full: `Candidate.Checker7.D` (Sound7.lean 78-87).\n"
          "- **Tables.lean 50-102 `buildTabs`**: every value enters through `I.weight`.\n- **Certificate**: empty.\n\n"
          "**NOTES:**\n\nNothing of substance unsettled.")


def test_a_heading_after_the_opening_line_and_in_bold_counts():
    s = sections(READER, REVIEW)
    assert first_word(s["VERDICT"]) == "clean"
    assert s["FOUND"].startswith("Checker closure read in full") and s["FOUND"].endswith("- **Certificate**: empty.")
    assert s["NOTES"] == "Nothing of substance unsettled."


def test_the_forms_of_a_heading():
    assert sections("VERDICT: **clean**.\nFOUND: one table.\nNOTES: none.", REVIEW) == {
        "VERDICT": "**clean**.", "FOUND": "one table.", "NOTES": "none."}
    assert first_word("**clean**.") == "clean" and first_word("Suspect: a table") == "suspect" and first_word("") == ""
    assert sections("**VERDICT**: suspect", REVIEW) == {"VERDICT": "suspect"}
    assert sections("__VERDICT:__ unclear", REVIEW) == {"VERDICT": "unclear"}
    assert sections("## Verdict\nclean\n### **Found:** a table", REVIEW) == {"VERDICT": "clean", "FOUND": "a table"}
    assert sections("I'll start.Now the lemma.CLAIM: x\nSCALING:\nthe bill grows like V^3\nNOTES: n", SCALING) == {
        "CLAIM": "x", "SCALING": "the bill grows like V^3", "NOTES": "n"}
    # two headings on one line: the text between them is the first one's
    assert sections("CLAIM: a.SCALING: b", SCALING) == {"CLAIM": "a.", "SCALING": "b"}
    # text that runs into a later heading belongs to the section before it
    assert sections("CLAIM: a\nthe end of a.**NOTES:** b", SCALING) == {"CLAIM": "a\nthe end of a.", "NOTES": "b"}


def test_what_is_not_a_heading():
    # a missing section is absent; text before the first heading belongs to none
    assert sections("It looks fine to me.\nFOUND: nothing.\n", REVIEW) == {"FOUND": "nothing."}
    # names inside other words, names in small letters in a sentence, and names inside code fences
    s = sections("CLAIM: a\nRESCALING: no\nwe found: no\n```\nSCALING: in code\n```\nNOTES: b", SCALING + ("FOUND",))
    assert s == {"CLAIM": "a\nRESCALING: no\nwe found: no\n```\nSCALING: in code\n```", "NOTES": "b"}
    # the first copy of a heading counts; later copies are text
    assert sections("CLAIM: a\nCLAIM: b", SCALING) == {"CLAIM": "a\nCLAIM: b"}
