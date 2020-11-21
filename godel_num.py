# Very simple compilers from Gödel numbers to FOL and back


# some helper functions before starting
def is_prime(p) :
    "predicate function checking for primeness of input"

    if not (p in [2,3,5,7,11,13]) and p < 14: 
        return False

    # classic sieve of Eratosthenes
    n = 2
    while n**2 <= p :
        if p % n == 0 :
            return False
        n += 1

    return True

   
def next_prime(p) :
    "returns the prime after the input"
    
    p += 1
    while not is_prime(p) :
        p += 1 

    return p


def p_index(p) :
    "index of a prime in the set of primes"

    prime = 2
    index = 1
    while prime < p :
        prime = next_prime(prime)
        index += 1

    if p == prime : 
        return index
    else :
        return -1

def prime_list(exp) :
    "factor an expression into primes"

    primes = []

    p = 2
    while exp > 1 or p < exp :
        # print(primes,p)
        if exp % p == 0 :
            primes.append(p)
            exp //= p
        else :
            p = next_prime(p)

    return primes

def prime_map(primes) :
    "make a map of number of primes"

    primes = prime_list(primes)

    p_map = {}
    for i in primes :
        if i in p_map :
            p_map[i] += 1
        else :
            p_map.update({i:1})

    return p_map

def parse_number(exp) :
    """parser for a number, 

        returns a tupple: (number, location stopped in string)"""

    i = 0 
    n = 0
    while i < len(exp) :
        if exp[i] >= '0' and exp[i] <= '9' :
            n += eval(exp[i])
            n *= 10
        else : break
        i += 1

    n //= 10
    return n,i



# Start of the compilers
def godel_to_fol(exp, latex=False) :
    """Gödel_number -> FOL
        Assuming Gödel numbers are small
        
        tested for n <= 10,000

        input not sanitized
    """

    gd_map = { '3'  : '(',
               '5'  : ')',
               '7'  : ',',
               '9'  : '\\lnot',
               '11' : '\\Rightarrow',
               '13' : '\\forall',
               '13+8*k' : 'x_k',
               '7+8*k' : 'a_k',
               '1+8*(2**n*3**k)' : 'f_k^n',
               '3+8*(2**n*3**k)' : 'A_k^n'
             }
    
    # change to python syntax
    exp = str(exp).replace('\\cdot','*')
    exp = str(exp).replace('^','**')
    exp = str(exp).replace('{','(').replace('}',')')
    exp = eval(str(exp)) # still some injection attack oportunity
                         # could replace with another library

    # base cases
    if exp == 3 : return gd_map[str(exp)]
    if exp == 5 : return gd_map[str(exp)]
    if exp == 7 : return gd_map[str(exp)]
    if exp == 9 : return gd_map[str(exp)]
    if exp == 11 : return gd_map[str(exp)]
    if exp == 13 : return gd_map[str(exp)]
    if (exp-1) % 8 == 0 :
        pm = prime_map((exp-1)//8)
        if 2 in pm.keys() and 3 in pm.keys() and len(pm) == 2 :
            return('f_'+str(pm[3])+'^'+str(pm[2]))
    if (exp-3) % 8 == 0 :
        pm = prime_map((exp-3)//8)
        if 2 in pm.keys() and 3 in pm.keys() and len(pm) == 2 :
            return('A_'+str(pm[3])+'^'+str(pm[2]))
    if (exp-7) % 8 == 0 : return 'a_'+str((exp-7)//8)
    if (exp-13) % 8 == 0 : return 'x_'+str((exp-13)//8)

    
    # so it may be one layer down
    p_map = prime_map(exp)

    # check if second layer is sequential primes
    p = 2
    while p_index(p) <= len(p_map) :
        if not (p in p_map.keys()) :
            return 'ERROR'
        p = next_prime(p)
    
    # prime bases need neighbor primes
    if len(p_map) < 2 :
        return 'ERROR'

    # Go one layer deeper, also recursive case
    expression = ''
    for p in p_map :
        expression += godel_to_fol(p_map[p])

    # recursive error handling as well
    if expression == '' or 'ERROR' in expression :
        return "ERROR"

    # allow activation of escape sequences \\ -> \
    if latex != False :
        print(expression)
    else :
        return expression


def fol_to_godel(exp, latex=False) :
    """FOL -> Gödel_number 
        This is pretty much just a bunch of in-place
        parser combinators. 

        Will parse FOL up until syntax mismatch

       Mind the mess"""

    
    g_number = []
    
    # extending this function to a number version of an error code
    if exp == 'ERROR' : return '-1'

    i = 0
    j = i
    while i < len(exp) and j <= len(exp) :
        if i > j :
            j = i
        sub_exp = exp[i:j]

        if sub_exp == '(' : 
            g_number.append(3)
            i += len('(')
        if sub_exp == ')' : 
            g_number.append(5)
            i += len(')')
        if sub_exp == ',' : 
            g_number.append(7)
            i += len(',')
        if sub_exp == '\\lnot' : 
            g_number.append(9)
            i += len('\\lnot')
        if sub_exp == '\\Rightarrow' : 
            g_number.append(11)
            i += len('\\Rightarrow')
        if sub_exp == '\\forall' : 
            g_number.append(13)
            i += len('\\forall')
        if sub_exp == 'x_' :
            a = parse_number(exp[i+len('x_'):])
            if a[0] == 0 : break
            g_number.append(13+8*a[0])
            i += a[1]
            i += len('x_')
        if sub_exp == 'a_' :
            a = parse_number(exp[i+len('a_'):])
            if a[0] == 0 : break
            g_number.append(7+8*a[0])
            i += a[1]
            i += len('a_')
        if sub_exp == 'f_' :
            down = parse_number(exp[i+len('f_'):])
            i += down[1]
            up = parse_number(exp[i+len('f_^'):])
            i += up[1]
            if up[0] == 0 : break
            if down[0] == 0 : break
            g_number.append(1+8*(2**up[0]*3**down[0]))
            i += len('f_^')
        if sub_exp == 'A_' :
            down = parse_number(exp[i+len('A_'):])
            i += down[1]
            up = parse_number(exp[i+len('A_^'):])
            i += up[1]
            if up[0] == 0 : break
            if down[0] == 0 : break
            g_number.append(3+8*(2**up[0]*3**down[0]))
            i += len('A_^')
        if (sub_exp == ' '  or 
           sub_exp == '\n' or
           sub_exp == '\t') :
            i += len(' ')

        j += 1

    if len(g_number) == 1 :
        return str(g_number[0])

    total = ''
    prime = 2
    for el in g_number :
        total += str(prime)+'^{'+str(el)+'} \\cdot '
        prime = next_prime(prime)
    total = total[:-len(' \\cdot ')]  

    # transform \\ -> \
    if latex != False :
        print(total)
    else :
        total = total.replace('^','**')
        total = total.replace('\\cdot','*')
        total = total.replace('{','(').replace('}',')')
        return total
            
# test code
def test(n) :
    " test if g(g^-1(x)) == x"

    for i in range(1,n) :

        # the eval(x) turns arithmetic into a number
        num = eval(fol_to_godel(godel_to_fol(i)))
        if not (num == i or num == -1) :
            return i

    return True


