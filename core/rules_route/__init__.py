"""The rule route: a rule an agent proposes becomes a rule the checker uses, without a person in between.

    proposals   collect NEW RULE IDEA answers from a run's round folders (core/rules_route/proposals.py)
    implement   a separate implementer agent, not the one being scored, writes rule.py, SOUNDNESS.md and
                test_rule.py for one proposal (core/rules_route/implement.py)
    audit       the rule against brute force on trained, random and perturbed networks (audit.py), its own
                tests and the static guard, inside the sandbox
    review      an adversarial reviewer agent tries to break the soundness argument; its counterexamples
                are audited (review.py)
    adopt       a rule that passes everything is copied to rules/<name>/ with status.json (adopt.py)

core/rules_route/route.py runs the steps from a config file, resumably. docs/RULE_ROUTE.md explains it.
"""
