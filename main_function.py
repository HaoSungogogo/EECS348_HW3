from read import *
import binding

class fact(object):
    def __init__(self, statement, supported_by=[]):
        self.statement = statement
        if not supported_by:
            self.asserted = True
        else:
            self.asserted = False

        self.supported_by = supported_by
        self.facts_supported = []
        self.rules_supported = []

class rule(object):
    def __init__(self, rule, supported_by=[]):
        self.LHS = rule[0]
        self.RHS = rule[1]

        if not supported_by:
            self.asserted = True
        else:
            self.asserted = False

        self.supported_by = supported_by
        self.facts_supported = []
        self.rules_supported = []

class kb(object):
    def __init__(self):
        self.facts = []
        self.rules = []

    def add_fact(self, fact):
        self.facts.append(fact)

    def add_rule(self, rule):
        self.rules.append(rule)

    def rem_fact(self, fact):
        self.facts.remove(fact)

    def rem_rule(self, rule):
        self.rules.remove(rule)

    def kb_assert(self, statement):
        f = fact(statement)
        self.add_fact(f)

def Assert(object):
    if type(object) == fact:
        if object not in KB.facts:
            KB.add_fact(object)
        for oneRule in KB.rules:
            infer(object, oneRule)

    if type(object) == rule:
        if object not in KB.rules:
            KB.add_rule(object)
        for oneFact in KB.facts:
            infer(oneFact, object)


def infer(inferred_fact, inferred_rule):
    bindings = binding.match(inferred_fact.statement, inferred_rule.LHS[0], binding.bindings())
    if bindings != False:
        if len(inferred_rule.LHS) == 1:
            new_fact = binding.instantiate(inferred_rule.RHS, bindings)
            supported_by = [inferred_fact, inferred_rule]
            curr_fact = fact(new_fact, supported_by)
            assert(curr_fact)
            inferred_fact.facts_supported.append(curr_fact)
            inferred_rule.facts_supported.append(curr_fact)
            KB.facts.append(curr_fact)
        else:
            left = []
            right = []
            for i in range(len(inferred_rule.LHS)) :
                if i == 0:
                    continue
                else:
                    left.append(binding.instantiate(inferred_rule.LHS[i], bindings))
            right.append(binding.instantiate(inferred_rule.RHS, bindings))
            curr_rule = rule([left,right], [inferred_fact, inferred_rule])
            assert(curr_rule)
            inferred_fact.rules_supported.append(curr_rule)
            inferred_rule.facts_supported.append(curr_rule)
            KB.rules.append(curr_rule)


def Ask(object):
    res = []
    if type(object) == fact:
        if object in KB.facts:
            return True
        else:
            for oneRule in KB.rules:
                bindings = binding.match(object.statement, oneRule.LHS[0])
                if bindings != False:
                    res.append(bindings.pretty)
    if type(object) == rule:
        for oneFact in KB.facts:
            bindings = binding.match(oneFact.statement, object.LHS[0])
            if bindings != False:
                res.append(bindings.pretty)
    return res





if __name__ == "__main__":
    KB = kb()
    facts, rules = read_tokenize("statements.txt")
    # print rules

    for fact_statement in facts:
        Assert(fact(fact_statement))
    for rule_statement in rules:
        Assert(rule(rule_statement))
    print "*******rules********"
    for i in range(len(KB.rules)):
        print "LHS: "
        print KB.rules[i].LHS
        print "RHS: "
        print KB.rules[i].RHS
    print "********facts*******"
    for i in range(len(KB.facts)):
        print KB.facts[i].statement
    print Ask(fact(['flat', 'cube1']))



