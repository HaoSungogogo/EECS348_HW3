from read import *
from copy import *
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

# Action have three field:
# the precondition of action: if a fact or rule is in KB.facts, the precondition is the list of facts or rules that support this action
# the add of action: if the action(assert) will be taken, it means the new fact or rules including the current one and the inferred facts and rules
# that will be added to KB
# the retract of action: if a fact or rule in the KB, it means the facts and rules required to be delete
class Action(object):
    def __init__(self, object):
        self.precondition = []
        self.retract = []
        self.add = []

        if type(object) == fact:
            for ele in KB.facts:
                if object.statement == ele.statement:
                    for iter in ele.supported_by:
                        if type(iter) == fact:
                            self.precondition.append(iter.statement)
                        else:
                            self.precondition.append((iter.LHS, iter.RHS))
                    break
            self.retract.append(Why(object.statement))
        else:
            for ele in KB.rules:
                if object.LHS == ele.LHS and object.RHS == ele.RHS:
                    for iter in ele.supported_by:
                        if type(iter) == fact:
                            self.precondition.append(iter.statement)
                        else:
                            self.precondition.append((iter.LHS, iter.RHS))
                    break
            self.retract.append(Why_rule(object))

        self.add.append(Assert_shadow(object))


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
            Assert(curr_fact)
            inferred_fact.facts_supported.append(curr_fact)
            inferred_rule.facts_supported.append(curr_fact)
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
            Assert(curr_rule)
            inferred_fact.rules_supported.append(curr_rule)
            inferred_rule.facts_supported.append(curr_rule)




def Ask(object):
    res = []
    if type(object) == fact:
        for fact_iter in KB.facts:
            if fact_iter.statement == object.statement:
                return True
        for oneRule in KB.rules:
            binding_check = binding.match(object.statement, oneRule.LHS[0], binding.bindings())
            if binding_check != False:
                if binding_check.pretty not in res:
                    res.append(binding_check.pretty)

    if type(object) == rule:
        for oneFact in KB.facts:
            binding_check = binding.match(oneFact.statement, object.LHS[0], binding.bindings())
            if binding_check != False:
                if binding_check.pretty not in res:
                    res.append(binding_check.pretty)
    return res

def Why(statement):
    for iter in KB.facts:
        if iter.statement == statement:
            level = []
            level.append(iter)
            global_res = []
            while len(level) != 0:
                size = len(level)
                strs = ""
                for i in range(size):
                    cur = level.pop(0)
                    if len(cur.supported_by) != 0:
                        res = []
                        if type(cur) == fact:
                            strs += " " + str(cur.statement) + "is supported_by"
                            res.append(cur.statement)
                        if type(cur) == rule:
                            strs += " " + str(cur.LHS) + "=>" + str(cur.RHS) + "is supported_by"
                            res.append((cur.LHS, cur.RHS))
                    for element in cur.supported_by:
                        if type(element) == fact:
                            strs += " fact is: " + str(element.statement) + ","
                            res.append(element.statement)
                        else:
                            strs += " rule is: " + str(element.LHS) + "=>" + str(element.RHS)
                            res.append((element.LHS, element.RHS))
                        level.append(element)
                global_res.append(res)
                #print strs
            # print global_res
            return global_res



def Retract(object):
    if type(object) == fact:
        for iter in KB.facts:
            if iter.statement == object.statement:
                level = []
                level.append(iter)
                while len(level) != 0:
                    size = len(level)
                    for i in range(size):
                        cur = level.pop(0)
                        if len(cur.supported_by) != 0:
                            if type(cur) == fact:
                                KB.facts.remove(cur)
                            if type(cur) == rule:
                                KB.rules.remove(cur)
                        for element in cur.supported_by:
                            level.append(element)
    else:
        for iter in KB.rules:
            if iter.LHS == object.LHS and iter.RHS == object.RHS:
                level = []
                level.append(iter)
                while len(level) != 0:
                    size = len(level)
                    for i in range(size):
                        cur = level.pop(0)
                        if len(cur.supported_by) != 0:
                            if type(cur) == fact:
                                KB.facts.remove(cur)
                            if type(cur) == rule:
                                KB.rules.remove(cur)
                        for element in cur.supported_by:
                            level.append(element)

def Ask_plus(list_of_statement):
    list = []
    for statement in list_of_statement:
        binding_list = Ask(statement)
        if binding_list == True:
            continue
        else:
            if len(list) == 0:
                for iter in binding_list:
                    list.append(iter)
            else:
                for iter in binding_list:
                    flag = check(list, iter)
                    if flag == False:
                        return False
                    else:
                        list.append(iter)
    return list




def check(list, iter):
    for ele in list:
        if len(ele) == len(iter):
            set1 = {}
            set2 = {}
            for i in ele:
                set1[i[0]] = [i[1]]
            for i  in iter:
                set2[i[0]] = [i[1]]
            for i in set1:
                if i not in set2:
                    return True
            for i in set2:
                if i not in set1:
                    return True
            for i in set1:
                if set1[i] != set2[i]:
                    return False
            return True
    return True


#for the add of action object, it need to memory the facts and rules that it can inferred and the current, which is realized
#from Assert_shadow. The difference between Assert and Assert_shadow is that Assert will generate new fact and rule, but will not
#insert them into Knowledge Base, but Assert will insert them into Knowledge Base
def Assert_shadow (object, shadow_kb = None, res = None):
    if shadow_kb == None:
        shadow_kb = deepcopy(KB)
        print "count"
    if res == None:
        res = []

    if type(object) == fact:
        for temp in shadow_kb.facts:
            if object.statement == temp.statement:
                return res
        shadow_kb.add_fact(object)
        res.append(object.statement)
        for oneRule in shadow_kb.rules:
            infer_shadow(object, oneRule, shadow_kb, res)

    if type(object) == rule:
        for temp in shadow_kb.rules:
            if object.LHS == temp.LHS and object.RHS == temp.RHS:
                return res
        shadow_kb.add_rule(object)
        res.append((object.LHS, object.RHS))
        for oneFact in shadow_kb.facts:
            infer_shadow(oneFact, object, shadow_kb, res)

    return res

#Which is also used for building action class, see comments in Assert_shadow
def infer_shadow(inferred_fact, inferred_rule, shadow_kb, res):
    bindings = binding.match(inferred_fact.statement, inferred_rule.LHS[0], binding.bindings())
    if bindings != False:
        if len(inferred_rule.LHS) == 1:
            new_fact = binding.instantiate(inferred_rule.RHS, bindings)
            supported_by = [inferred_fact, inferred_rule]
            curr_fact = fact(new_fact, supported_by)
            Assert_shadow(curr_fact, shadow_kb, res)
            inferred_fact.facts_supported.append(curr_fact)
            inferred_rule.facts_supported.append(curr_fact)
            shadow_kb.facts.append(curr_fact)
            res.append(curr_fact.statement)
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
            Assert_shadow(curr_rule, shadow_kb, res)
            inferred_fact.rules_supported.append(curr_rule)
            inferred_rule.facts_supported.append(curr_rule)
            shadow_kb.rules.append(curr_rule)
            res.append((curr_rule.LHS, curr_rule.RHS))


def Why_rule(object):
    for iter in KB.rules:
        if iter.LHS == object.LHS and iter.RHS == object.RHS:
            level = []
            level.append(iter)
            global_res = []
            while len(level) != 0:
                size = len(level)
                strs = ""
                for i in range(size):
                    cur = level.pop(0)
                    if len(cur.supported_by) != 0:
                        res = []
                        if type(cur) == fact:
                            strs += " " + str(cur.statement) + "is supported_by"
                            res.append(cur.statement)
                        if type(cur) == rule:
                            strs += " " + str(cur.LHS) + "=>" + str(cur.RHS) + "is supported_by"
                            res.append((cur.LHS, cur.RHS))
                    for element in cur.supported_by:
                        if type(element) == fact:
                            strs += " fact is: " + str(element.statement) + ","
                            res.append(element.statement)
                        else:
                            strs += " rule is: " + str(element.LHS) + "=>" + str(element.RHS)
                            res.append((element.LHS, element.RHS))
                        level.append(element)
                global_res.append(res)
                #print strs
            # print global_res
            return global_res





if __name__ == "__main__":
    KB = kb()
    facts, rules = read_tokenize("statements.txt")
    # print rules

    for fact_statement in facts:
        Assert(fact(fact_statement))
    for rule_statement in rules:
        Assert(rule(rule_statement))
    # print "*******rules********"
    # for i in range(len(KB.rules)):
    #     print "LHS: "
    #     print KB.rules[i].LHS
    #     print "RHS: "
    #     print KB.rules[i].RHS
    # print "********facts*******"
    # for i in range(len(KB.facts)):
    #     print KB.facts[i].statement
    # print Ask_plus([fact(['inst', 'cube5', 'cube']), fact(['isa', 'sphere', 'abc'])])
    # print Ask(fact(['inst', 'cube5', 'cube']))
    # print Ask(fact(['inst', 'cube6', 'cube']))

    # temp = [[('?X', 'cube5'), ('?Y', 'cube')]]
    # iter = [('?X', 'cube4'), ('?Y', 'cube'), ('?Z', 'flat')]
    # print check(temp, iter)
    # Why(['flat', 'cube4'])
    # res = []
    # for fact_statement in facts:
    #     res.append(Assert_shadow(fact(fact_statement)))
    # for rule_statement in rules:
    #     res.append(Assert_shadow(rule(rule_statement)))
    # # res.append(Assert_shadow(fact(['flat', 'cube4'])))
    # print res

    # Retract(rule([[['isa', 'pyramid', '?z']],['inst', 'pyramid3', '?z']]))
    act = Action(fact(['flat', 'cube4']))
    print act.precondition
    print act.add
    print act.retract
