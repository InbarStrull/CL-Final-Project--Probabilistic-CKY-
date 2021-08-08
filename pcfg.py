import copy
import ptree
import itertools


class PRule(object):
    def __init__(self, variable, derivation, probability):
        self.variable = str(variable)
        self.derivation = tuple(derivation)
        self.probability = float(probability)

    def derivation_length(self):
        return len(self.derivation)

    def __repr__(self):
        compact_derivation = " ".join(self.derivation)
        return self.variable + ' -> ' + compact_derivation + ' (' + str(self.probability) + ')'

    def __eq__(self, other):
        try:
            return self.variable == other.variable and self.derivation == other.derivation
        except Exception:
            return False


class PCFG(object):
    def __init__(self, start_variable='S', rules=None):
        if rules is None:
            self.rules = {}
        else:
            self.rules = copy.deepcopy(rules)  # A dictionary that maps an str object to a list of PRule objects
        self.start = start_variable  # Start symbol of the grammar

    def add_rule(self, rule):
        """
        Adds a rule to dictionary of rules in grammar.
        """
        if rule.variable not in self.rules:
            self.rules[rule.variable] = []
        self.rules[rule.variable].append(rule)

    def remove_rule(self, rule):
        """
        Removes a rule from dictionary of rules in grammar.
        """
        try:
            self.rules[rule.variable].remove(rule)
        except KeyError:
            pass
        except ValueError:
            pass

    def eliminate_epsilon_rules(self, rule, black):
        """
        eliminate all rules of the form A → ε[p] (except A = S0)
        from the grammar
        :param rule: a rule of the form A → ε[p]
        :param black: "black list" of all epsilon rules variables that were removed
        :return: None
        """
        my_variable = rule.variable
        p = rule.probability
        self.remove_rule(rule)  # a. remove A --> epsilon[p]
        black.append(rule.variable)
        self.normalize(rule)  # b. normalize all remaining rules for A

        rhs = self.right_hand_side(my_variable, black)  # c. Find all rules where A appears in the right-hand side

        for vari in rhs:  # every variable found
            for r in rhs[vari]:  # every rule derivation that my_variable appears in
                deriv = r.derivation
                indices = self.indices_of_vari(deriv, my_variable)  # all occurrence indices of my_variable (list)
                new_rules = []  # a list of the required rule combinations
                m = len(indices)
                for k in range(1,
                               m + 1):  # all rules that can be obtained by applying the removed rule partially or fully
                    new_rules += self.remove_occurrences(k, indices, r, p)
                r.probability = self.new_prob_computation(r.probability, p, 0, m)  # update rule probability
                for new_rule in new_rules:
                    if self.exists(new_rule):  # If one of these rules already exists in the grammar we update its
                        # probability
                        existing = self.find_unknown_rule(new_rule)
                        existing.probability = existing.probability + new_rule.probability
                    else:
                        self.add_rule(new_rule)

    def exists(self, rule):
        """
        check if rule exists in the grammar
        :return: True if exists, else False
        """
        if rule.variable not in self.rules:
            return False
        for r in self.rules[rule.variable]:
            if r.derivation == rule.derivation:
                return True

    def find_unknown_rule(self, new_rule):
        """
        find and return a certain rule according
        to its derivation and variable
        """
        for rule in self.rules[new_rule.variable]:
            if rule == new_rule:
                return rule

    def remove_occurrences(self, k, indices, rule, p):
        """
        removes every combination of
        k-times occurrence of a variable
        from the derivation
        returns a list of the rules obtained
        by removing the occurrences.
        each rule as a tuple
        """
        combs = list(itertools.combinations(indices, k))  # all k-sized combination of indices to remove
        new_rules = []  # all new rules obtained by removing occurrences
        deriv = rule.derivation
        vari = rule.variable
        q = rule.probability
        m = len(indices)
        new_p = self.new_prob_computation(q, p, k, m)  # compute new probability for the rules
        for comb in combs:
            new_deriv = tuple([deriv[t] for t in range(len(deriv)) if
                               t not in comb])  # create new derivation from removing occurrences
            new_rule = PRule(vari, new_deriv, new_p)  # create new rule
            new_rules.append(new_rule)

        return new_rules

    @staticmethod
    def new_prob_computation(q, p, k, m):
        """
        compute: q * p_k * p_l
        :param q: probability of a rule
        :param p: probability of another rule
        :param k: k<m, number of removed occurrences of a variable
        :param m: total number of occurrences of a variable in a derivation
        :return: q * p_k * p_l
        """
        p_k = pow(p, k)
        p_l = pow(1 - p, m - k)
        return q * p_k * p_l

    @staticmethod
    def indices_of_vari(deriv, vari):
        """
        find the indices every occurrence of vari
        in a given derivation
        return a list of the indices
        """
        indices = []
        for v in range(len(deriv)):
            if deriv[v] == vari:
                indices.append(v)
        return indices

    def right_hand_side(self, my_variable, black):
        """
        find and return a dictionary of all rules where my_variable
        appears in the right-hand side
        """
        rhs = {}  # a dictionary of all the rules according to variable that my_variable appears in their derivations
        # {variable : rules with my_variable}
        for vari in self.rules:
            vari_list = []      # a list of all the rules in the derivations of vari that my_variable appears in them
            for rule in self.rules[vari]:
                if rule.variable not in black:
                    deriv = rule.derivation
                    if my_variable in deriv:
                        vari_list.append(rule)
            if vari_list:          # if my_variable appeared in at least one derivation
                rhs[vari] = vari_list   # add vari : vari_list to rhs

        return rhs

    @staticmethod
    def norm_computation(q, p):
        """
        compute q / (1 - p)
        :return: q / (1 - p)
        """
        return q / (1 - p)

    def normalize(self, curr_rule):
        """
        normalize all remaining rules for curr_rule
         each rule A → u[q] (where u ∈ (Σ ∪ V )∗) will become A → u[q/1−p]
        """
        my_variable = curr_rule.variable
        p = curr_rule.probability
        for rule in self.rules[my_variable]:    # each rule A → u[q] (where u ∈ (Σ ∪ V )∗)
            q = rule.probability
            rule.probability = self.norm_computation(q, p)  # will become A → u[q/1−p]

    def change_rule(self, rule, name):
        """
        change the given RHS of the
        given rule into a 2 symbols RHS
        remove the previous version of the rule
        from the grammar
        add the new version to the grammar
        return the RHS sequence that
        wasn't included in the new RHS version
        """
        prev_derivation = rule.derivation
        new_derivation = (prev_derivation[0], name)  # create new derivation
        updated_rule = PRule(rule.variable, new_derivation,
                             rule.probability)  # create a rule with the current variable and new derivation
        self.remove_rule(rule)  # remove current rule
        self.add_rule(updated_rule)  # add new rule
        return prev_derivation[1:]  # return derivation's "tail"

    def multiple_symbols(self, rule):
        """
        break the RHS of the given rule
        into a sequence of rules whose
        RHS <= 2 symbols
        """
        maxi = 0        # maxi =  max{i: v name = v_Ni, i > 0}
        vari = rule.variable
        for v in self.rules:
            if str(vari) + "_" in v:    # if variable of the form v_N exists in self.rules
                nv = v[2 + len(vari):]  # check its characters after N
                try:
                    nv = int(nv)        # check whether its characters form a number
                except ValueError:
                    pass
                if type(nv) == int:     # if so
                    if nv > maxi:
                        maxi = nv
        count = maxi + 1                # count will appear at the end of the new variable name
        length = len(rule.derivation)
        curr_rule = rule
        while length > 2:  # while the current rule's RHS contains more than 2 symbols
            name = vari + "_N" + str(count)  # generate a new name for a rule
            deriv = self.change_rule(curr_rule, name)  # change the current rule and return the end of its derivation
            curr_rule = PRule(name, deriv,
                              1)  # create a new rule with the returned derivation and the generated variable name
            self.add_rule(curr_rule)
            length = len(curr_rule.derivation)
            count += 1

    def is_variable(self, u):
        """
        return True if u is a variable
        else False
        """
        return u in self.rules

    def one_terminal(self, rule, side):
        """
        create a new rule of the form A → b[1] where b ∈ Σ
        if side:
        convert rule of the form A → bC[p] where b ∈ Σ and C ∈ V
        else:
        convert rule of the form: A → Bc[p] where B ∈ V and c ∈ Σ
        side: False when a variable is on the right and a terminal on the left
        True when a variable is on the left and a terminal on the left
        add created rules to the grammar
        return: converted rule
        """
        vari = rule.variable
        p = rule.probability
        deriv = rule.derivation
        ind = int(side)  # convert boolean value to int, just in case
        # ind == 1 if side == True, ind == 0 if side == False
        name = vari + "_Y" + str(ind)      # give a name to the new rule
        new_rule = PRule(vari, (deriv[ind], name), p)  # new rule to replace rule
        self.remove_rule(rule)
        self.add_rule(new_rule)
        self.add_rule(PRule(name, deriv[1 - ind], 1))  # create a new rule of the form A → b[1] where b ∈ Σ
        return new_rule

    def to_near_cnf(self):
        """
        Returns an equivalent near-CNF grammar.
        """
        near_cnf = PCFG(self.start, self.rules)  # generate a grammar with self.rules
        new_start = PRule("S_0", (self.start,), 1)  # 1. create new start variable
        near_cnf.add_rule(new_start)  # 1. add new start variable
        near_cnf.start = new_start.variable  # set as start variable

        # 2. eliminate epsilon rules
        go = True                      # a list of all epsilon rule
        black = []
        while go:
            epsilon_rules = []
            for vari in near_cnf.rules:
                for rule in near_cnf.rules[vari]:
                    if rule.derivation == () and rule not in black and rule.variable != near_cnf.start:
                        # if the rule is an epsilon rule (derivation ()) and it was already removed or it is S_0 --> ()
                        epsilon_rules.append(rule)
            for epsilon_rule in epsilon_rules:
                near_cnf.eliminate_epsilon_rules(epsilon_rule, black)

            go = epsilon_rules != []

        # 3. Convert “long rules”
        to_convert = []                         # a list of all rules with RHS > 2
        for vari in near_cnf.rules:  # a. Multiple symbols
            for rule in near_cnf.rules[vari]:
                if len(rule.derivation) > 2:
                    to_convert.append(rule)

        for rule in to_convert:
            near_cnf.multiple_symbols(rule)

        false_for_right = []                    # a list of all rules of the form A → Bc[p] where B ∈ V and c ∈ Σ
        true_for_left = []                      # a list of all rules of the form A → bC[p] where b ∈ Σ and C ∈ V
        both = []                               # a list of all rules of the form A → bc[p] where b,c ∈ Σ
        for vari in near_cnf.rules:  # b. Terminals
            for rule in near_cnf.rules[vari]:
                if len(rule.derivation) > 1:
                    res_first = near_cnf.is_variable(rule.derivation[0])
                    res_second = near_cnf.is_variable(rule.derivation[1])
                    if res_first and not res_second:  # rule of the form: A → Bc[p] where B ∈ V and c ∈ Σ
                        false_for_right.append(rule)

                    elif not res_first and res_second:  # rule of the form: A → bC[p] where b ∈ Σ and C ∈ V
                        true_for_left.append(rule)

                    elif not res_first and not res_second:  # r if both RHS variables are terminals
                        both.append(rule)

        for rule in false_for_right:
            near_cnf.one_terminal(rule,
                                  False)  # side == False when a variable is on the right and a terminal on the left

        for rule in true_for_left:
            near_cnf.one_terminal(rule,
                                  True)  # side == True when a variable is on the left and a terminal on the left

        for rule in both:
            new_rule = near_cnf.one_terminal(rule,
                                             False)  # first convert to the form A → bC[p] where b ∈ Σ and C ∈ V
            near_cnf.one_terminal(new_rule, True)  # then convert from the form A → bC[p] where b ∈ Σ and C ∈ V

        return near_cnf

    @staticmethod
    def table(row, col, val=None):
        """ create a row X col table"""
        mat = [[val]*col for x in range(row)]
        return mat

    def find_vars_to_terminal(self, w_j, var=True):
        """ find the variables that derive
        w_j and add them to a list (if var)
        or to a dictionary {variable_1: [w_j],... variable_k : [w_j]}
        (if not var)
        return the list or the dictionary
        according to the boolean flag"""
        varis = []
        matching = {}

        for variab in self.rules:
            for rule in self.rules[variab]:
                if w_j in rule.derivation:
                    if rule.derivation not in varis:  # if a derivation was not added
                        varis.append((rule.variable, rule.probability))  # add it to the variables list
                    matching[rule.variable] = ([(w_j, rule.probability)], 1)  # add each rule to the dictionary.
                    # value- a tuple of a list containing a tuple of w_j and its probability and 1 to so it will
                    # correspond to the shape of the non-terminal derivations in the bo table.
        if var:
            if varis:
                return varis  # if an empty list return None
        else:
            if matching:
                return matching  # if an empty dictionary return None

    @staticmethod
    def find_prob_in_cell(cell, var_to_find):
        """
        return the probability of the variable
        in the given cell if there
        else return 0
        """
        if cell:           # if not None
            for tups in cell:
                if tups[0] == var_to_find:
                    return tups[1]

        return 0

    def find_vars_to_vars(self, b, c, cell_to_compare, var=True):
        """ find the variables that derive
        the rule B C represented by b c respectively
        and add them to a list (if var)
        or to a dictionary {variable_1: [B, C],... variable_k : [B, C]}
        (if not var)
        return the list or the dictionary
        according to the boolean flag
        """
        varis = []
        matching = {}
        for var_b in b:  # find every combination of b and c
            for var_c in c:
                for variab in self.rules:
                    for rule in self.rules[variab]:
                        if (var_b[0], var_c[0]) == rule.derivation:  # found a variable that derives the current
                            # combination
                            b_prob = self.find_prob_in_cell(b, var_b[0])
                            c_prob = self.find_prob_in_cell(c, var_c[0])
                            to_compare = self.find_prob_in_cell(cell_to_compare, rule.variable)  # find the probability
                            # of the variable of the rule
                            if b_prob * c_prob * rule.probability > to_compare:  # if q·p1·p2
                                # is greater than the current probability of Z in (i, j):
                                app = True      # append to varis?
                                for num in range(len(varis)):
                                    if varis[num][0] == rule.variable:  # if a rule was add to varis
                                        app = False                     # don't append it to varis
                                        if varis[num][1] < b_prob * c_prob * rule.probability:  # if new probability
                                            varis[num] = list(varis[num])   # is better, replace variable probability
                                            varis[num][1] = b_prob * c_prob * rule.probability
                                            varis[num] = tuple(varis[num])
                                if app:
                                    varis.append((rule.variable, b_prob * c_prob * rule.probability))
                                # add it to the var-prob list
                            matching[rule.variable] = ([var_b, var_c], b_prob * c_prob * rule.probability)
                            # add each rule to the dictionary
        if var:
            if varis:
                return varis  # if an empty list return None
        else:
            if matching:
                return matching  # if an empty dictionary return None

    def find_unit_rules(self, vari):
        """
        find the unit rules that derive vari
        return a list of those rules
        """
        units = []
        for variab in self.rules:
            for rule in self.rules[variab]:
                if len(rule.derivation) == 1:   # if a unit rule
                    if vari in rule.derivation:  # if vari is the derivation
                        units.append(rule)

        return units

    def binary_rules(self, t, bp, j, s):
        """
        find every rule of the form A --> BC[p]
        in every partition in the given range (i+1, j)
        add the the rules that follow the probability
        requirements to t and to bp
        """
        for k in range(s+1, j):
            b = t[s][k]
            c = t[k][j]
            if b and c:
                fill_seq = self.find_vars_to_vars(b, c, t[s][j])  # find every A, A--> BC in G such that:
                # t[i][j](A.probability) < P(A → BC) · t[i][k](B.probability) · t[k][j](C.probability)
                # used for t, might be redundant
                fill_bp = self.find_vars_to_vars(b, c, t[s][j], False)  # find every A, A--> BC in G, used for bp
                if fill_seq is not None:  # if at least one matching rule was found
                    if t[s][j] is not None:  # (start block) if the cell was't empty
                        self.check_if_rule_was_added_list(t, s, j, fill_seq)
                    else:  # if the cell was empty
                        t[s][j] = fill_seq  # (end block)
                    # block might be redundant
                    if bp[s][j] is not None:  # if the cell was't empty
                        self.check_if_rule_was_added_dic(bp, s, j, fill_bp)
                    else:  # if the cell was empty
                        bp[s][j] = fill_bp

    @staticmethod
    def check_if_rule_was_added_list(t, s, j, cell):
        """
        when t[s][j] isn't empty
        for each variable in cell that is found
        in t[s][j], replace t[s][j][variable] to cell[variable]
        because its probability is larger (because it was added in
        find_vars_to_vars)
        for each variable in cell that is not
        found in t[s][j], add cell[variable]
        to t[s][j]
        :param t: table
        :param s:  row
        :param j:  column
        :param cell: rules to add to t
        :return: None
        """
        replace = [pair for pair in cell for exists in t[s][j] if pair[0] == t[s][j][0]]   # all tuples that there is
        # no need to add to t[s][j]
        delete = [pair for pair in t[s][j] for exists in cell if pair[0] == t[s][j][0]]
        do_add = [pair for pair in cell if pair not in replace]
        dont_change = [pair for pair in t[s][j] if pair not in delete]
        t[s][j] = replace + do_add + dont_change

    @staticmethod
    def check_if_rule_was_added_dic(bp, s, j, cell):
        """
        when bp[s][j] isn't empty
        for each variable in cell that is found
        in bp[s][j], replace bp[s][j][variable] to cell[variable]
        because its probability is larger (because it was added in
        find_vars_to_vars)
        for each variable in cell that is not
        found in bp[s][j], add cell[variable]
        to bp[s][j]
        :param bp: backpointers table
        :param s:  row
        :param j:  column
        :param cell: rules to add to bp
        :return: None
        """
        dont_add = []       # all items that there is no need to add to bp[s][j]
        for vari in cell:   # check if cell contains rules that appear in bp[s][j]
            if vari in bp[s][j]:
                bp[s][j][vari] = cell[vari]
                dont_add.append(vari)
        new_dic = {}
        for v in cell:
            if v not in dont_add:
                new_dic[v] = cell[v]

    def unary_rules(self, t, bp, j, s):
        """
        find every rule of the form A--> B[p]
        """
        if t[s+1][j] is not None:
            go = True
            to_add_later = []  # all relevant tuples: (unit rule, probability)
            units = []
            while go:          # while ∃A → B ∈ G s.t. t[i][j][A] < P(A → B) · t[i][j][B]
                go = False
                for each_var in t[s + 1][j]:
                    lst = self.find_unit_rules(each_var[0])   # find cell's unit rules
                    self.add_without_duplications(lst, units)
                if units:   # if unit rules are found
                    for each_var in t[s + 1][j]:
                        for u in units:
                            new_prob = u.probability * each_var[1]  # compute minimal probability
                            if u.derivation[0] == each_var[0]:
                                curr_prob = self.find_prob_in_cell(t[s + 1][j], u.variable)
                                if curr_prob < new_prob:
                                    # if u.probability · each_var[1] is greater that the current probability of the
                                    # u.variable in (i, j):
                                    if [u, new_prob, False] not in to_add_later:   # if a new unary rule was added
                                        go = True   # that means we should iterate one more time to check if there are
                                        to_add_later.append([u, new_prob, True])  # new unary rules

                for tup in to_add_later:  # after all new unary rules are collected
                    if tup[2] is True:
                        # update probabilities in cells for every variable that its probability wasn't updated
                        to_t = (tup[0].variable, tup[1])
                        t[s + 1][j].append(to_t)
                        bp[s + 1][j][tup[0].variable] = ([(tup[0].derivation[0], tup[0].probability)], tup[1])
                    tup[2] = False

    @staticmethod
    def add_without_duplications(list1, list2):
        """
        add list1's elements that don't
        appear in list2 to list2
        """
        for elem1 in list1:
            if elem1 not in list2:
                list2.append(elem1)

    def bp_no_prob(self, bp):
        """
        create and return a new backpointers table
        without probabilities
        """
        new_bp = self.table(len(bp), len(bp))
        for row in range(len(bp)):
            for coll in range(len(bp)):
                if bp[row][coll] is not None:       # for each cell in bp, if cell is not None:
                    new_dic = {}        # create a dictionary for the cell
                    new_bp[row][coll] = new_dic
                    for vari in bp[row][coll]:  # for each variable in the cell in bp
                        new_dic[vari] = []      # create a new list of values for the variable
                        for elem in range(len(bp[row][coll][vari][0])):
                            new_dic[vari].append(bp[row][coll][vari][0][elem][0])  # without its probability

        return new_bp

    def cky_parser(self, string):
        """
        Parses the input string given the grammar, using the probabilistic CKY algorithm.
        If the string has been generated by the grammar - returns a most likely parse tree for the input string.
        Otherwise - returns None.
        The CFG is given in near-CNF.
        """
        n = len(string) + 1
        t = self.table(n, n)  # each cell is either None or a list of variables
        # might be redundant because bp contains same variables and their derivation
        bp = self.table(n, n)  # backpointers table- bp[s][j] = {t[s][j][1] :
        # { [derivation],..... t[s][j][k] : [derivation] }
        for j in range(1, n):
            fill = self.find_vars_to_terminal(string[j-1])       # find every A, A--> w_j in G, used for t
            # might be redundant
            fill_bp = self.find_vars_to_terminal(string[j-1], False)    # find every A, A--> w_j in G, used for bp
            t[j-1][j] = fill
            bp[j-1][j] = fill_bp
            for s in range(j-2, -2, -1):    # go over every string partition
                self.binary_rules(t, bp, j, s+1)
                self.unary_rules(t, bp, j, s)   # find unit rules and add them to t and to bp

        new_bp = self.bp_no_prob(bp)
        if t[0][n-1] is not None:  # if the cell is not empty
            for pair in t[0][n-1]:
                if self.start in pair:    # is start variable is in that cell
                    root_prob = pair[1]
                    if root_prob < pow(2, -50):
                        return "the given grammar cannot derive the given string (low probability)"
                    tree = self.my_tree(new_bp, 0, n-1, root_prob, self.start)          # create a tree according to bp
                    return tree

        return "the given grammar cannot derive the given string"

    def my_tree(self, bp, row, col, root_prob, start):     # row = 0, col = last
        root = ptree.Node(start, [])
        tree = ptree.PTree(root, root_prob)
        self.tree_left(bp, root, row, col)  # start constructing from left, tree_left will build right tree as well
        return tree

    def tree_right(self, bp, root, row, col):
        if row >= len(bp) - 1 or col <= 0:  # "frame"- halting condition
            return None

        if len(bp[row][col][root.key]) < 2:     # root has no right child- finish
            return None

        need = bp[row][col][root.key][1]        # get root's right child
        curr = root.children
        curr.append(ptree.Node(need, []))             # add a brother to root's left child

        row = row + 1       # find child's derivation found down in the same column
        while row < len(bp) and (bp[row][col] is None or need not in bp[row][col]):
            row += 1
        self.tree_left(bp, curr[1], row, col)       # find left child of root's right child

    def tree_left(self, bp, root, row, col):
        if row >= len(bp) - 1 or col <= 0:  # "frame"- halting condition
            return None

        need = bp[row][col][root.key][0]    # get root's left child
        curr = root.children
        curr.append(ptree.Node(need, []))         # insert root's left child to the children list

        l_col = col    # find child's derivation found in the same row from left for constructing left path
        if len(bp[row][col][root.key]) == 2:    # if root has no right child, keep looking in the same column
            l_col -= 1                          # else go a column back
        while l_col > 0 and (bp[row][l_col] is None or need not in bp[row][l_col]):
            l_col -= 1

        self.tree_left(bp, curr[0], row, l_col)     # recursive call- find left child of root's left child

        if len(bp[row][col][root.key]) < 2:         # if root has no right child- finish
            return None

        self.tree_right(bp, root, row, col)         # find root's right child

    def is_valid_grammar(self):
        """
        Validates that the grammar is legal (meaning - the probabilities of the rules for each variable sum to 1).
        """
        epsilon = 0.0001
        for variable in self.rules:     # for each variable in the rules dictionary
            c = 0                       # initialize a counter to sum probabilities
            for rule in self.rules[variable]:   # for each LHS of the variable
                c += rule.probability           # add its probability to the counter
            if c < 1 - epsilon or c > 1 + epsilon:  # if c is not in the interval (1- epsilon, 1 + epsilon)
                return False
        return True
