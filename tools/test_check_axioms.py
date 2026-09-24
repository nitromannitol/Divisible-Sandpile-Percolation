"""Regression cases for the axiom gate's acceptance boundary."""

import unittest

from check_axioms import audit_closures


class AxiomGateTest(unittest.TestCase):
    def node(self, state="SEALED", kind="theorem"):
        return {"id": "example", "export": "Example.result", "state": state, "kind": kind}

    def report(self, axioms="propext, Classical.choice, Quot.sound", quote="'"):
        return f"{quote}Example.result{quote} depends on axioms: [{axioms}]\n"

    def test_clean_seal_and_both_diagnostic_quote_styles(self):
        for quote in ("'", "`"):
            self.assertEqual(audit_closures([self.node()], self.report(quote=quote), 0)[1], [])

    def test_registered_draft_is_reported_but_strict_check_rejects_it(self):
        nodes = [self.node("DRAFT_SORRY")]
        reports, errors = audit_closures(nodes, self.report("sorryAx"), 0)
        self.assertEqual(errors, [])
        self.assertIn("registered draft", reports[0])
        self.assertTrue(audit_closures(nodes, self.report("sorryAx"), 0, strict=True)[1])

    def test_transitive_debt_cannot_enter_a_seal_or_external(self):
        for node in (self.node(), self.node("FROZEN", "definition")):
            self.assertTrue(audit_closures([node], self.report("sorryAx"), 0)[1])

    def test_clean_draft_requires_explicit_registration(self):
        self.assertTrue(audit_closures([self.node("DRAFT_SORRY")], self.report(), 0)[1])

    def test_missing_duplicate_and_wrong_export_fail(self):
        for output in ("", self.report() * 2, self.report().replace("Example.result", "Other.result")):
            self.assertTrue(audit_closures([self.node()], output, 0)[1])

    def test_elaboration_failure_is_fatal_even_with_an_axiom_report(self):
        self.assertTrue(audit_closures([self.node()], self.report(), 1)[1])

    def test_nonstandard_axiom_is_rejected_even_in_a_draft(self):
        for state in ("SEALED", "DRAFT_SORRY"):
            self.assertTrue(audit_closures([self.node(state)], self.report("Other.assumption"), 0)[1])


if __name__ == "__main__":
    unittest.main()
