import pcfg


def main():
    f = open("grammar.txt", "r")
    gram = f.read().split()
    grammar = generate_grammar(gram)
    near_cnf = grammar.to_near_cnf()
    sentences = read_sentences()
    for sentence in sentences:
        print(sentence)
        print(near_cnf.cky_parser(sentence.split()))


def read_sentences():
    """
    read the sentences from data.txt
    return a list of the sentences
    :return:
    """
    f = open("data.txt", "r")
    gram = f.read().splitlines()
    gram = [sentence for sentence in gram if sentence != ""]
    return gram


def generate_grammar(gram):
    """
    generate grammar from the list gram
    """
    c = 0
    while gram[c] != "start_variable":  # find start variable
        c += 1
    start = gram[c+1]
    grammar = pcfg.PCFG(start)          # create a PCFG with start and no rules
    while gram[c] != "Grammar":         # find the index of the first rule
        c += 1
    c += 3

    while gram[c] != '###########':
        c = adding_rules_grammar(c, gram, grammar)  # find each rule from the grammar and add it to the grammar
        c += 1

    while gram[c] != "Lexicon":         # find the index of the first rule of the lexicon
        c += 1
    c += 3

    while c < len(gram):
        var = gram[c]
        c = adding_rules_lexicon(c, gram, grammar, var)    # find each rule from the lexicon and add it to the grammar
        c += 1
    return grammar


def adding_rules_grammar(c, gram, grammar):
    """
    find the rule that begins in index c
    add it to grammar. rule from the grammar
    :param c: index of gram
    :param gram: grammar.txt as a list
    :param grammar: pcfg
    :return: c
    """
    vari = gram[c]       # starting at the variable
    tup = []            # a list of the variables in the derivation
    c += 2                  # skip vari and the arrow
    while "[" not in gram[c]:   # while there are variables in the derivation
        tup.append(gram[c])       # add them to the list
        c += 1
    tuple(tup)
    num = gram[c][1:len(gram[c]) - 1]   # get the probability out of the brackets
    r = pcfg.PRule(vari, tup, num)      # create a new rule
    grammar.add_rule(r)
    return c                            # return the index


def adding_rules_lexicon(c, gram, grammar, vari):
    """
    find the rule that begins in index c with
    variable vari
    add it to grammar. rule from the lexicon
    :param c: index of gram
    :param gram: grammar.txt as a list
    :param grammar: pcfg
    :param vari:
    :return: c
    """
    cont = True     # True if the terminal on gram[c] belongs to vari, else False
    c += 2          # skip vari and the arrow
    while cont:
        h = gram[c]                 # terminal
        h = h.replace('"', "")      # remove " " from edges
        tup = (h, )
        c += 1
        prob = gram[c][1:len(gram[c]) - 1]  # get the probability out of the brackets
        r = pcfg.PRule(vari, tup, prob)     # create a new rule
        grammar.add_rule(r)
        c += 1                              # move one index forward to check:
        if c >= len(gram):
            return c
        cont = (gram[c] == "|")             # whether vari is still the current variable
        c += 1                              # move to the next terminal (or forward)
    return c-2


main()
