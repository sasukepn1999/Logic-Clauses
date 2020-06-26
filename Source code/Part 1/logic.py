DEBUG = 1
INPUT = 'input1.txt'
OUTPUT = 'output1.txt'

def getInput(filename):
    _sentence = ''
    _num_clauses = 0
    _KB = []
    try:
        with open(filename, 'r') as _fp:
            # Getting alpha and number of clauses in KB
            _sentence = _fp.readline().strip()
            _num_clauses = int(_fp.readline())

            for _ in range(_num_clauses):
                _clause = [_unit.strip(' ') for _unit in _fp.readline().strip().split('OR')]
                _KB.append(_clause)

        return _sentence, _num_clauses, _KB
    except IOError as _err:
        if(DEBUG):
            print('File error:' + str(_err))
        else:
            pass
        exit()

# Setting output
def setOutput(filename, output):
    try:
        with open(filename, 'w') as _fp:
            for _element in output:
                if (isinstance(_element, dict)):
                    # Print number of new clause each loop times
                    _fp.write(str(_element['num']) + '\n')
                    
                    if (_element['num'] == 0):
                        continue

                    # Print Clauses each loop times
                    for _elem in _element['clauses']:
                        if (not _elem):
                            _fp.write('{}' + '\n')
                            continue

                        # Sort alpha-beta
                        _tmp = []
                        for _unit in _elem:
                            if (_unit[0] == '-'):
                                _tmp.append(_unit[1])
                            else:
                                _tmp.append(_unit)
                        _tmp, _elem = zip(*sorted(zip(_tmp, _elem)))

                        #Print new clauses
                        for _unit in _elem:
                            if (_unit == _elem[len(_elem) - 1]):
                                _end = '\n'
                            else:
                                _end = ' OR '
                            _fp.write(_unit + _end)
                else:
                    if (_element == False): 
                        _fp.write('NO')
                    else:
                        _fp.write('YES')
    except IOError as _err:
        if(DEBUG):
            print('File error:' + str(_err))
        else:
            pass
        exit()

# Getting negative of a (ex: negative of 'A' is '-A')
def negative(sentence):
    if sentence[0] == '-':
        return sentence[1]
    else:
        return '-' + sentence

# Normalizing clause (ex: 'A v A v C' --> 'A v C')
def normalize(clause):
    for _unit in clause:
        clause.remove(_unit)
        while (_unit in clause):
            clause.remove(_unit)
        clause.append(_unit)

# Resolving between Ci and Cj clauses
def PLResolve(ci, cj):
    _tmp_ci = ci.copy()
    _tmp_cj = cj.copy()
    
    _output = -1
    _is_true_clause = False
    _can_resolve = False
    for _unit in _tmp_ci:
        if (negative(_unit) in _tmp_cj):
            _tmp_ci.remove(_unit)
            _tmp_cj.remove(negative(_unit))
            _can_resolve = True
            break
    
    for _unit in _tmp_ci:
        if (negative(_unit) in _tmp_cj):
            _is_true_clause = True
            break
    
    if (_is_true_clause == False and _can_resolve == True):
        _tmp_ci.extend(_tmp_cj)
        normalize(_tmp_ci)
        _output = _tmp_ci

    return _output

def setO(filename, ci, cj):
    with open(filename, 'a') as _fp:
        _fp.write('(')
        for i in ci:
            if (i == ci[len(ci) - 1]):
                _end = ') ('
            else:
                _end = ' OR '
            _fp.write(i + _end)

        for i in cj:
            if (i == cj[len(cj) - 1]):
                _end = ')\n'
            else:
                _end = ' OR '
            _fp.write(i + _end)
        
# Checking if Set is subset in List (ex: ['A'] is subset in [['A'], ['B']])
def isSubsetInClauses(subset, clauses):
    if (len(clauses) == 0 or len(subset) == 0):
        return False

    _is_subset = True
    for _clause in clauses:
        for _unit in subset:
            if (_unit not in _clause or len(subset) != len(_clause)):
                _is_subset = False
                break
            _is_subset = True
        if (_is_subset):
            break
    return _is_subset 

# Checking if List is subset in List (ex: [['A'], ['B']] is subset in [['A'], ['B'], ['C']])
def isSubsetsInClauses(subsets, clauses):
    _is_subset = True

    for _subset in subsets:
        if (isSubsetInClauses(_subset, clauses) == False):
            _is_subset = False
            break
    return _is_subset

# Fletching new clauses into List 
def fletchClausesIntoList(new, clauses, output_loop, mode = 0):
     for _clause in new:
            if (_clause not in clauses): 
                if (mode): clauses.append(_clause)
                output_loop['clauses'].append(_clause)
                output_loop['num'] += 1

# PL Resolution
def PLResolution(KB, sentence):
    _output = []

    _clauses = KB.copy()
    _clauses.append([str(negative(sentence))])
    _new = []
    while(True):
        # Information each loop {'num': , 'clauses': }
        _output_loop = {'num': 0, 'clauses': []}
        
        # Resolution Algorithm
        _num_clauses_in_loop = 0
        _num_clauses = len(_clauses)
        for _first in range(_num_clauses):
            for _second in range(_first + 1, _num_clauses):
                # Resolving Ci and Cj clauses
                _resolvents = PLResolve(_clauses[_first], _clauses[_second])

                if (_resolvents != -1):
                    # Checking if new clause excisted
                    if (isSubsetInClauses(_resolvents, _new) == False):
                        # Normalizing clause (ex: 'A v A v C' --> 'A v C')
                        normalize(_resolvents)

                        # Adding new clause to list
                        _new += [_resolvents]

                    # Checking empty clause
                    if ([] in _new):
                        fletchClausesIntoList(_new, _clauses, _output_loop)    
                        _output.append(_output_loop)
                        return True, _output

        # Checking new clauses is subset in KB
        if (isSubsetsInClauses(_new, _clauses)):
            _output.append(_output_loop)
            return False, _output          

        fletchClausesIntoList(_new, _clauses, _output_loop, 1) 
        _output.append(_output_loop)

def PLExcution():
    a, num, KB = getInput(INPUT)
    is_entail, output = PLResolution(KB, a)
    output.append(is_entail)
    setOutput(OUTPUT, output)

if __name__ == "__main__":
    PLExcution()