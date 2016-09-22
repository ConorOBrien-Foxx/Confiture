import ast, cmath, copy, dictionary, fractions, functools, itertools, locale, math, numpy, operator, parser, random, re, sympy, sys, time

code_page  = '''¡¢£¤¥¦©¬®µ½¿€ÆÇÐÑ×ØŒÞßæçðıȷñ÷øœþ !"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~¶'''
code_page += '''°¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ƁƇƊƑƓƘⱮƝƤƬƲȤɓƈɗƒɠɦƙɱɲƥʠɼʂƭʋȥẠḄḌẸḤỊḲḶṂṆỌṚṢṬỤṾẈỴẒȦḂĊḊĖḞĠḢİĿṀṄȮṖṘṠṪẆẊẎŻạḅḍẹḥịḳḷṃṇọṛṣṭụṿẉỵẓȧḃċḋėḟġḣŀṁṅȯṗṙṡṫẇẋẏż«»‘’“”'''
# Unused letters for single atoms: kquƁƇƊƑƘⱮƝƤƬƲȤɓɗƒɦƙɱɲƥʠɼʂƭʋȥẸẈẒĿṘẎŻẹḥḳṃṇọụṿẉỵẓḋėġŀṅẏ

str_digit = '0123456789'
str_lower = 'abcdefghijklmnopqrstuvwxyz'
str_upper = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'

inf = float('inf')
nan = float('nan')
sys.setrecursionlimit(1 << 30)

class attrdict(dict):
	def __init__(self, *args, **kwargs):
		dict.__init__(self, *args, **kwargs)
		self.__dict__ = self

def arities(links):
	return [link.arity for link in links]

def at_index(index, array):
	array = iterable(array)
	if not array:
		return 0
	low_index = math.floor(index) - 1
	high_index = math.ceil(index) - 1
	if low_index == high_index:
		return array[low_index % len(array)]
	return [array[low_index % len(array)], array[high_index % len(array)]]

def bounce(array):
	return array[:-1] + array[::-1]

def carmichael(n):
    n = int(n)
    if n < 1:
        return 0
    c = 1
    for p, k in sympy.ntheory.factor_.factorint(n).items():
        c = lcm(c, 2 ** (k - 2) if p == 2 < k else (p - 1) * p ** (k - 1))
    return c

def create_chain(chain, arity = -1):
	return attrdict(
		arity = arity,
		chain = chain,
		call = lambda x = None, y = None: variadic_chain(chain, (x, y))
	)

def create_literal(string):
	return attrdict(
		arity = 0,
		call = lambda: safe_eval(string, False)
	)

def copy_to(atom, value):
	atom.call = lambda: value
	return value

def conv_dyadic_integer(link, larg, rarg):
	try:
		iconv_larg = int(larg)
		try:
			iconv_rarg = int(rarg)
			return link(iconv_larg, iconv_rarg)
		except:
			return iconv_larg
	except:
		try:
			return int(rarg)
		except:
			return 0

def conv_monadic_integer(link, arg):
	try:
		return link(int(arg))
	except:
		return 0

def determinant(matrix):
	matrix = sympy.Matrix(matrix)
	if matrix.is_square:
		return simplest_number(matrix.det())
	return simplest_number(math.sqrt((matrix * matrix.transpose()).det()))

def div(dividend, divisor, floor = False):
	if divisor == 0:
		return dividend * inf
	if divisor == inf:
		return 0
	if floor or (type(dividend) == int and type(divisor) == int and not dividend % divisor):
		return int(dividend // divisor)
	return dividend / divisor

def depth(link):
	if type(link) != list:
		return 0
	if not link:
		return 1
	return 1 + max(map(depth, link))

def diagonals(matrix):
	shifted = [None] * len(matrix)
	for index, row in enumerate(map(iterable, reversed(matrix))):
		shifted[~index] = index * [None] + row
	return rotate_left(zip_ragged(shifted), len(matrix) - 1)

def dot_product(left, right):
	left, right = iterable(left), iterable(right)
	if complex in map(type, left + right):
		right = [complex(t).conjugate() for t in right]
	product = sum(dyadic_link(atoms['×'], (left, right)))
	if product.imag == 0:
		product = product.real
		if type(product) != int and product.is_integer():
			product = int(product)
	return product

def dyadic_chain(chain, args):
	larg, rarg = args
	for link in chain:
		if link.arity < 0:
			link.arity = 2
	if chain and arities(chain[0:3]) == [2, 2, 2]:
		ret = dyadic_link(chain[0], args)
		chain = chain[1:]
	elif leading_constant(chain):
		ret = niladic_link(chain[0])
		chain = chain[1:]
	else:
		ret = larg
	while chain:
		if arities(chain[0:3]) == [2, 2, 0] and leading_constant(chain[2:]):
			ret = dyadic_link(chain[1], (dyadic_link(chain[0], (ret, rarg)), niladic_link(chain[2])))
			chain = chain[3:]
		elif arities(chain[0:2]) == [2, 2]:
			ret = dyadic_link(chain[0], (ret, dyadic_link(chain[1], args)))
			chain = chain[2:]
		elif arities(chain[0:2]) == [2, 0]:
			ret = dyadic_link(chain[0], (ret, niladic_link(chain[1])))
			chain = chain[2:]
		elif arities(chain[0:2]) == [0, 2]:
			ret = dyadic_link(chain[1], (niladic_link(chain[0]), ret))
			chain = chain[2:]
		elif chain[0].arity == 2:
			ret = dyadic_link(chain[0], (ret, rarg))
			chain = chain[1:]
		elif chain[0].arity == 1:
			ret = monadic_link(chain[0], ret)
			chain = chain[1:]
		else:
			output(ret)
			ret = niladic_link(chain[0])
			chain = chain[1:]
	return ret

def dyadic_link(link, args, conv = True, lflat = False, rflat = False):
	larg, rarg = args
	lflat = lflat or not hasattr(link, 'ldepth')
	rflat = rflat or not hasattr(link, 'rdepth')
	larg_depth = lflat or depth(larg)
	rarg_depth = rflat or depth(rarg)
	if (lflat or link.ldepth == larg_depth) and (rflat or link.rdepth == rarg_depth):
		if conv and hasattr(link, 'conv'):
			return link.conv(link.call, larg, rarg)
		return link.call(larg, rarg)
	conv = conv and hasattr(link, 'conv')
	if not lflat and larg_depth < link.ldepth:
		return dyadic_link(link, ([larg], rarg))
	if not rflat and rarg_depth < link.rdepth:
		return dyadic_link(link, (larg, [rarg]))
	if not rflat and (lflat or larg_depth - rarg_depth < link.ldepth - link.rdepth):
		return [dyadic_link(link, (larg, y)) for y in rarg]
	if not lflat and (rflat or larg_depth - rarg_depth > link.ldepth - link.rdepth):
		return [dyadic_link(link, (x, rarg)) for x in larg]
	return [dyadic_link(link, (x, y)) for x, y in zip(*args)] + larg[len(rarg) :] + rarg[len(larg) :]

def equal(array):
	array = iterable(array)
	return int(all(item == array[0] for item in array))

def extremes(min_or_max, link, array):
	array = iterable(array, make_range=True)
	if not array:
		return []
	results = [monadic_link(link, x) for x in array]
	best = min_or_max(results)
	return [x for x, fx in zip(array, results) if fx == best]

def flatten(argument):
	flat = []
	if type(argument) == list:
		for item in argument:
			flat += flatten(item)
	else:
		flat.append(argument)
	return flat

def from_base(digits, base):
	integer = 0
	for digit in digits:
		integer = base * integer + digit
	return integer

def from_diagonals(diagonals):
	upper_right = 1
	while len(diagonals[upper_right - 1]) > 1:
		upper_right += 1
	diagonals = rotate_left(diagonals, upper_right)
	shift = len(diagonals) - upper_right
	index = 0
	while shift:
		diagonals[index] = shift * [None] + diagonals[index]
		index += 1
		shift -= 1
	return zip_ragged(diagonals)

def from_exponents(exponents):
	integer = 1
	for index, exponent in enumerate(exponents):
		integer *= sympy.ntheory.generate.prime(index + 1) ** exponent
	return integer

def simplest_number(number):
	if abs(number ** 2) != number ** 2:
		return number
	if number % 1:
		return float(number)
	return int(number)

def grid(array):
	if depth(array) == 1:
		return join(array, ' ')
	if depth(array) == 2 and equal(map(len, array)):
		array = [[str(entry) for entry in row] for row in array]
		width = max(max([len(entry) for entry in row]) if row else 0 for row in array)
		array = [[list(entry.rjust(width)) for entry in row] for row in array]
		return join([join(row, ' ') for row in array], '\n')
	if depth(array) == 3 and all(type(item) == str for item in flatten(array)):
		array = [[''.join(entry) for entry in row] for row in array]
		width = max(max([len(entry) for entry in row]) if row else 0 for row in array)
		array = [[list(entry.ljust(width)) for entry in row] for row in array]
		return join([join(row, ' ') for row in array], '\n')
	return join(array, '\n')

def group(array):
	array = iterable(array, make_digits = True)
	grouped = {}
	for index, item in enumerate(array):
		item = repr(item) if type(item) == list else item
		if item in grouped:
			grouped[item].append(index + 1)
		else:
			grouped[item] = [index + 1]
	return [grouped[key] for key in sorted(grouped)]

def group_equal(array):
	array = iterable(array, make_digits = True)
	groups = []
	for x in array:
		if groups and groups[-1][0] == x:
			groups[-1].append(x)
		else:
			groups.append([x])
	return groups

def identity(argument):
	return argument

def iterable(argument, make_copy = False, make_digits = False, make_range = False):
	the_type = type(argument)
	if the_type == list:
		return copy.deepcopy(argument) if make_copy else argument
	if the_type != str and make_digits:
		return to_base(argument, 10)
	if the_type != str and make_range:
		return list(range(1, int(argument) + 1))
	return [argument]

def index_of(haystack, needle):
	for index, item in enumerate(iterable(haystack)):
		if item == needle:
			return 1 + index
	return 0

def isqrt(number):
	a = number
	b = (a + 1) // 2
	while b < a:
		a = b
		b = (a + number // a) // 2
	return int(a)

def is_string(iterable):
	if type(iterable) != list:
		return False
	return all(map(lambda t: type(t) == str, iterable))

def confiture_eval(code, arguments):
	return variadic_chain(parse_code(code)[-1] if code else '', arguments)

def confiture_uneval(argument, top = True):
	the_type = type(argument)
	if the_type in (float, int):
		return confiture_uneval_real(argument)
	if the_type == complex:
		return confiture_uneval_real(argument.real) + 'ı' + confiture_uneval_real(argument.imag)
	if the_type == str:
		return '”' + argument
	if all(map(is_string, argument)):
		strings = [''.join(string) for string in argument]
		if all(map(lambda t: code_page.find(t) < 250, ''.join(strings))):
			return '“' + '“'.join(strings) + '”'
	if is_string(argument):
		string = ''.join(argument)
		if all(map(lambda t: code_page.find(t) < 250, string)):
			return '“' + string + '”'
	middle = list(','.join(confiture_uneval(item, top = False) for item in argument))
	return middle if top else '[' + middle + ']'

def confiture_uneval_real(number):
	string = str(number if number % 1 else int(number))
	return string.lstrip('0') if number else string

def join(array, glue):
	array = iterable(array, make_copy = True)
	last = array.pop() if array else []
	glue = iterable(glue)
	ret = []
	for item in array:
		ret += iterable(item) + glue
	return ret + iterable(last)

def last_input():
	if len(sys.argv) > 3:
		return safe_eval(sys.argv[-1])
	return safe_eval(input())

def leading_constant(chain):
	return chain and arities(chain) + [1] < [0, 2] * len(chain)

def listify(element, dirty = False):
	if type(element) == str and dirty:
		return list(element)
	if type(element) in (int, float, complex) or (type(element) == str and len(element) == 1):
		return element
	if type(element) == numpy.int64:
		return int(element)
	if type(element) == numpy.float64:
		return float(element) if element % 1 else int(element)
	if type(element) == numpy.complex128:
		return complex(element)
	return [listify(item, dirty) for item in element]

def lcm(x, y):
    return x * y // (fractions.gcd(x, y) or 1)

def loop_until_loop(link, args, return_all = False, return_loop = False):
	ret, rarg = args
	cumret = []
	while True:
		cumret.append(ret)
		larg = ret
		ret = variadic_link(link, (larg, rarg))
		rarg = larg
		if ret in cumret:
			if return_all:
				return cumret
			if return_loop:
				return cumret[index_of(cumret, ret) - 1 :]
			return larg

def nfind(links, args):
	larg, rarg = args
	larg = larg or 0
	matches = variadic_link(links[1], args) if len(links) == 2 else last_input()
	found = []
	while len(found) < matches:
		if variadic_link(links[0], (larg, rarg)):
			found.append(larg)
		larg += 1
	return found

def matrix_to_list(matrix):
	return [[simplest_number(entry) for entry in row] for row in matrix.tolist()]

def max_arity(links):
	return max(arities(links)) if min(arities(links)) > -1 else (~max(arities(links)) or -1)

def maximal_indices(iterable):
	maximum = max(iterable)
	return [u + 1 for u, v in enumerate(iterable) if v == maximum]

def modinv(a, m):
    i, _, g = sympy.numbers.igcdex(a, m)
    return i % m if g == 1 else 0

def mold(content, shape):
	for index in range(len(shape)):
		if type(shape[index]) == list:
			mold(content, shape[index])
		else:
			item = content.pop(0)
			shape[index] = item
			content.append(item)
	return shape

def monadic_chain(chain, arg):
	init = True
	ret = arg
	while True:
		if init:
			for link in chain:
				if link.arity < 0:
					link.arity = 1
			if leading_constant(chain):
				ret = niladic_link(chain[0])
				chain = chain[1:]
			init = False
		if not chain:
			break
		if arities(chain[0:2]) == [2, 1]:
			ret = dyadic_link(chain[0], (ret, monadic_link(chain[1], arg)))
			chain = chain[2:]
		elif arities(chain[0:2]) == [2, 0]:
			ret = dyadic_link(chain[0], (ret, niladic_link(chain[1])))
			chain = chain[2:]
		elif arities(chain[0:2]) == [0, 2]:
			ret = dyadic_link(chain[1], (niladic_link(chain[0]), ret))
			chain = chain[2:]
		elif chain[0].arity == 2:
			ret = dyadic_link(chain[0], (ret, arg))
			chain = chain[1:]
		elif chain[0].arity == 1:
			if not chain[1:] and hasattr(chain[0], 'chain'):
				arg = ret
				chain = chain[0].chain
				atoms['⁸'].call = lambda literal = arg: literal
				init = True
			else:
				ret = monadic_link(chain[0], ret)
				chain = chain[1:]
		else:
			output(ret)
			ret = niladic_link(chain[0])
			chain = chain[1:]
	return ret

def monadic_link(link, arg, flat = False, conv = True):
	flat = flat or not hasattr(link, 'ldepth')
	arg_depth = flat or depth(arg)
	if flat or link.ldepth == arg_depth:
		if conv and hasattr(link, 'conv'):
			return link.conv(link.call, arg)
		return link.call(arg)
	conv = conv and hasattr(link, 'conv')
	if link.ldepth > arg_depth:
		return monadic_link(link, [arg], conv = conv)
	return [monadic_link(link, z, conv = conv) for z in arg]

def multiset_difference(left, right):
	result = iterable(left)[::-1]
	for element in iterable(right):
		if element in result:
			result.remove(element)
	return result[::-1]

def multiset_intersect(left, right):
	right = iterable(right, make_copy = True)
	result = []
	for element in iterable(left):
		if element in right:
			result.append(element)
			right.remove(element)
	return result

def multiset_symdif(left, right):
	return multiset_union(multiset_difference(left, right), multiset_difference(right, left))

def multiset_union(left, right):
	return iterable(left) + multiset_difference(right, left)

def nCr(left, right):
	if type(left) == int and type(right) == int:
		if right < 0:
			right = left - right
		if right < 0 or (left > 0 and right > left):
			return 0
		if left > 0:
			right = min(right, left - right)
		result = 1
		for i in range(right):
			result = result * (left - i) // (i + 1)
		return result
	return div(Pi(left), Pi(left - right) * Pi(right))

def niladic_chain(chain):
	while len(chain) == 1 and hasattr(chain[0], 'chain'):
		chain = chain[0].chain
	if not chain or chain[0].arity > 0:
		return monadic_chain(chain, 0)
	return monadic_chain(chain[1:], chain[0].call())

def niladic_link(link):
	return link.call()

def ntimes(links, args, cumulative = False):
	ret, rarg = args
	repetitions = variadic_link(links[1], args) if len(links) == 2 else last_input()
	repetitions = overload((int, bool), repetitions)
	if cumulative:
		cumret = [0] * repetitions
	for index in range(repetitions):
		if cumulative:
			cumret[index] = ret
		larg = ret
		ret = variadic_link(links[0], (larg, rarg))
		rarg = larg
	return cumret + [ret] if cumulative else ret

def order(number, divisor):
	if number == 0 or abs(divisor) == 1:
		return inf
	if divisor == 0:
		return 0
	ret = 0
	while True:
		number, residue = divmod(number, divisor)
		if residue:
			break
		ret += 1
	return ret

def overload(operators, *args):
	for operator in operators:
		try:
			ret = operator(*args)
		except:
			pass
		else:
			return ret

def partitions(array):
	array = iterable(array, make_digits = True)
	ret = []
	for index in range(1, len(array)):
		for subarray in partitions(array[index:]):
			subarray.insert(0, array[:index])
			ret.append(subarray)
	ret.append([array])
	return ret

def parse_code(code):
	lines = regex_flink.findall(code)
	links = [[] for line in lines]
	for index, line in enumerate(lines):
		chains = links[index]
		for word in regex_chain.findall(line):
			chain = []
			arity = str_arities.find(word[0])
			for token in regex_token.findall(word):
				if token in atoms:
					chain.append(atoms[token])
				elif token in quicks:
					popped = []
					while not quicks[token].condition(popped) and (chain or chains):
						popped.insert(0, chain.pop() if chain else chains.pop())
					chain += quicks[token].quicklink(popped, links, index)
				elif token in hypers:
					x = chain.pop() if chain else chains.pop()
					chain.append(hypers[token](x, links))
				else:
					chain.append(create_literal(regex_liter.sub(parse_literal, token)))
			chains.append(create_chain(chain, arity))
	return links

def parse_literal(literal_match):
	literal = literal_match.group(0)
	if literal[0] in '”⁾':
		return repr(literal[1:])
	elif literal[0] == '“':
		if literal[-1] in '«»‘’”':
			mode = literal[-1]
			literal = literal[:-1]
		else:
			mode = ''
		parsed = literal.split('“')[1:]
		if   mode == '»':
			parsed = [sss(string).replace('¶', '\n') for string in parsed]
		elif mode == '‘':
			parsed = [[code_page.find(char) for char in string] for string in parsed]
		elif mode == '’':
			parsed = [from_base([code_page.find(char) + 1 for char in string], 250) for string in parsed]
		else:
			parsed = [string.replace('¶', '\n') for string in parsed]
		if mode not in '‘’':
			parsed = [[string] if len(string) == 1 else string for string in parsed]
		if len(parsed) == 1:
			parsed = parsed[0]
	else:
		parsed = eval('+ 1j *'.join([
			repr(eval('* 10 **'.join(['-1' if part == '-' else (part + '5' if part[-1:] == '.' else part) or repr(2 * index + 1)
			for index, part in enumerate(component.split('ȷ'))])) if component else index)
			for index, component in enumerate(literal.split('ı'))
		]))
	return repr(parsed) + ' '

def partition_at(booleans, array, keep_border = True):
	booleans = iterable(booleans)
	array = iterable(array)
	chunks = []
	chunk = []
	index = 0
	while index < len(array):
		if index < len(booleans) and booleans[index]:
			chunks.append(chunk)
			chunk = [array[index]] if keep_border else []
		else:
			chunk.append(array[index])
		index += 1
	return chunks + [chunk]

def Pi(number):
	if type(number) == int:
		if number < 0:
			return inf
		try:
			return math.factorial(number)
		except:
			return functools.reduce(operator.mul, range(1, number + 1), 1)
	return math.gamma(number + 1)

def powerset(array):
	array = iterable(array, make_range = True)
	ret = []
	for t in range(len(array) + 1):
		ret += listify(itertools.combinations(array, t))
	return ret

def reduce(links, outmost_links, index):
	ret = [attrdict(arity = 1)]
	if len(links) == 1:
		ret[0].call = lambda z: reduce_simple(z, links[0])
	else:
		ret[0].call = lambda z: [reduce_simple(t, links[0]) for t in split_fixed(iterable(z), links[1].call())]
	return ret

def reduce_simple(array, link):
	array = iterable(array)
	return functools.reduce(lambda x, y: dyadic_link(link, (x, y)), array)

def reduce_cumulative(links, outmost_links, index):
	ret = [attrdict(arity = 1)]
	if len(links) == 1:
		ret[0].call = lambda t: list(itertools.accumulate(iterable(t), lambda x, y: dyadic_link(links[0], (x, y))))
	else:
		ret[0].call = lambda z: [reduce_simple(t, links[0]) for t in split_rolling(iterable(z), links[1].call())]
	return ret

def rld(runs):
	return list(itertools.chain(*[[u] * v for u, v in runs]))

def rle(array):
	return [[group[0], len(group)] for group in group_equal(array)]

def rotate_left(array, units):
	array = iterable(array)
	length = len(array)
	return array[units % length :] + array[: units % length] if length else []

def safe_eval(string, dirty = True):
	return listify(ast.literal_eval(string), dirty)

def shift_left(number, bits):
	if type(number) == int and type(bits) == int:
		return number << bits
	return number * 2 ** bits

def shift_right(number, bits):
	if type(number) == int and type(bits) == int:
		return number >> bits
	return div(number, 2 ** bits, floor = True)

def shuffle(array):
	array = iterable(array, make_copy = True, make_range = True)
	random.shuffle(array)
	return array

def sparse(link, args, indices):
	larg = args[0]
	indices = [index - 1 if index > 0 else index - 1 + len(larg) for index in iterable(variadic_link(indices, args))]
	ret = iterable(variadic_link(link, args))
	return [ret[t % len(ret)] if t in indices else u for t, u in enumerate(larg)]

def split_around(array, needle):
	chunk = []
	window = len(needle)
	index = 0
	while index < len(array):
		if array[index : index + window] == needle:
			yield chunk
			chunk = []
			index += window
		else:
			chunk.append(array[index])
			index += 1
	yield chunk

def split_at(array, needle):
	chunk = []
	for element in array:
		if element == needle:
			yield chunk
			chunk = []
		else:
			chunk.append(element)
	yield chunk

def split_evenly(array, chunks):
	array = iterable(array)
	min_width, overflow = divmod(len(array), chunks)
	ret = []
	high = 0
	for index in range(chunks):
		low = high
		high = low + min_width + (index < overflow)
		ret.append(array[low : high])
	return ret

def split_fixed(array, width):
	array = iterable(array)
	return [array[index : index + width] for index in range(0, len(array), width)]

def split_once(array, needle):
	array = iterable(array, make_digits = True)
	index = index_of(array, needle) or len(array)
	return [array[0 : index - 1], array[index :]]

def split_rolling(array, width):
	array = iterable(array)
	return [array[index : index + width] for index in range(len(array) - width + 1)]

def sss(compressed):
	decompressed = ''
	integer = from_base([code_page.find(char) + 1 for char in compressed], 250)
	while integer:
		integer, mode = divmod(integer, 3)
		if mode == 0:
			integer, code = divmod(integer, 96)
			decompressed += code_page[code + 32]
		else:
			flag_swap = False
			flag_space = decompressed != ''
			if mode == 2:
				integer, flag = divmod(integer, 3)
				flag_swap = flag != 1
				flag_space ^= flag != 0
			integer, short = divmod(integer, 2)
			the_dictionary = (dictionary.long, dictionary.short)[short]
			integer, index = divmod(integer, len(the_dictionary))
			word = the_dictionary[index]
			if flag_swap:
				word = word[0].swapcase() + word[1:]
			if flag_space:
				word = ' ' + word
			decompressed += word
	return decompressed

def stringify(iterable, recurse = True):
	if type(iterable) != list:
		return iterable
	if str in map(type, iterable) and not list in map(type, iterable) or not iterable:
		return ''.join(map(str, iterable))
	iterable = [stringify(item) for item in iterable]
	return stringify(iterable, False) if recurse else iterable

def symmetric_mod(number, half_divisor):
	modulus = number % (2 * half_divisor)
	return modulus - 2 * half_divisor * (modulus > half_divisor)

def time_format(bitfield):
	time_string = ':'.join(['%H'] * (bitfield & 4 > 0) + ['%M'] * (bitfield & 2 > 0) + ['%S'] * (bitfield & 1 > 0))
	return list(time.strftime(time_string))

def translate(mapping, array):
	array = iterable(array, make_copy = True)
	mapping = iterable(mapping, make_copy = True)
	while mapping:
		source = iterable(mapping.pop(0))
		destination = iterable(mapping.pop(0))
		for (index, item) in enumerate(array):
			if item in source:
				array[index] = destination[min(source.index(item), len(destination) - 1)]
	return array

def trim(trimmee, trimmer, left = False, right = False):
	lindex = 0
	rindex = len(trimmee)
	if left:
		while lindex < rindex and trimmee[lindex] in trimmer:
			lindex += 1
	if right:
		while lindex < rindex and trimmee[rindex - 1] in trimmer:
			rindex -= 1
	return trimmee[lindex:rindex]

def try_eval(string):
	try:
		return safe_eval(string)
	except:
		return listify(string, True)

def to_base(integer, base, bijective = False):
	if integer == 0:
		return [0] * (not bijective)
	if bijective:
		base = abs(base)
	if base == 0:
		return [integer]
	if base == -1:
		digits = [1, 0] * abs(integer)
		return digits[:-1] if integer > 0 else digits
	sign = -1 if integer < 0 and base > 0 else 1
	integer *= sign
	if base == 1:
		return [sign] * integer
	digits = []
	while integer:
		integer -= bijective
		integer, digit = divmod(integer, base)
		digit += bijective
		if digit < 0:
			integer += 1
			digit -= base
		digits.append(sign * digit)
	return digits[::-1]

def to_case(argument, lower = False, swap = False, title = False, upper = False):
	ret = []
	last_item = ' '
	for item in argument:
		if type(item) == str:
			if lower:
				ret.append(item.lower())
			elif swap:
				ret.append(item.swapcase())
			elif title:
				ret.append(item.lower() if type(last_item) == str and last_item in str_upper + str_lower else item.upper())
			elif upper:
				ret.append(item.upper())
		else:
			ret.append(item)
		last_item = item
	return ret

def to_exponents(integer):
	if integer == 1:
		return []
	pairs = sympy.ntheory.factor_.factorint(integer)
	exponents = []
	for prime in sympy.ntheory.generate.primerange(2, max(pairs) + 1):
		if prime in pairs:
			exponents.append(pairs[prime])
		else:
			exponents.append(0)
	return exponents

def unicode_to_confiture(string):
	return ''.join(chr(code_page.find(char)) for char in str(string).replace('\n', '¶') if char in code_page)

def unique(array):
	array = iterable(array, make_digits = True)
	result = []
	for element in array:
		if not element in result:
			result.append(element)
	return result

def variadic_chain(chain, args):
	args = list(filter(None.__ne__, args))
	if len(args) == 0:
		return niladic_chain(chain)
	if len(args) == 1:
		larg_save = atoms['⁸'].call
		atoms['⁸'].call = lambda literal = args[0]: literal
		ret = monadic_chain(chain, args[0])
		atoms['⁸'].call = larg_save
	if len(args) == 2:
		larg_save = atoms['⁸'].call
		atoms['⁸'].call = lambda literal = args[0]: literal
		rarg_save = atoms['⁹'].call
		atoms['⁹'].call = lambda literal = args[1]: literal
		ret = dyadic_chain(chain, args)
		atoms['⁸'].call = larg_save
		atoms['⁹'].call = rarg_save
	return ret

def variadic_link(link, args, flat = False, lflat = False, rflat = False):
	if link.arity < 0:
		args = list(filter(None.__ne__, args))
		link.arity = len(args)
	if link.arity == 0:
		return niladic_link(link)
	if link.arity == 1:
		return monadic_link(link, args[0], flat)
	if link.arity == 2:
		return dyadic_link(link, args, lflat, rflat)

def while_loop(link, condition, args, cumulative = False):
	ret, rarg = args
	cumret = []
	while variadic_link(condition, (ret, rarg)):
		if cumulative:
			cumret.append(ret)
		larg = ret
		ret = variadic_link(link, (larg, rarg))
		rarg = larg
	return cumret + [ret] if cumulative else ret

def windowed_exists(needle, haystack):
	haystack = iterable(haystack, make_digits = True)
	needle = iterable(needle, make_digits = True)
	needle_length = len(needle)
	for index in range(len(haystack)):
		if haystack[index : index + needle_length] == needle:
			return 1
	return 0

def windowed_index_of(haystack, needle):
	haystack = iterable(haystack, make_digits = True)
	needle = iterable(needle, make_digits = True)
	needle_length = len(needle)
	for index in range(len(haystack)):
		if haystack[index : index + needle_length] == needle:
			return 1 + index
	return 0

def windowed_sublists(array):
	array = iterable(array, make_range = True)
	return [sublist for width in range(1, len(array) + 1) for sublist in split_rolling(array, width)]

def output(argument, end = '', transform = stringify):
	if locale.getdefaultlocale()[1][0:3] == 'UTF':
		print(transform(argument), end = end)
	else:
		print(unicode_to_confiture(transform(argument)), end = unicode_to_confiture(end))
	sys.stdout.flush()
	return argument

def zip_ragged(array):
	return listify(map(lambda t: filter(None.__ne__, t), itertools.zip_longest(*map(iterable, array))))

atoms = {
	'³': attrdict(
		arity = 0,
		call = lambda: 100
	),
	'⁴': attrdict(
		arity = 0,
		call = lambda: 16
	),
	'⁵': attrdict(
		arity = 0,
		call = lambda: 10
	),
	'⁶': attrdict(
		arity = 0,
		call = lambda: ' '
	),
	'⁷': attrdict(
		arity = 0,
		call = lambda: '\n'
	),
	'⁸': attrdict(
		arity = 0,
		call = lambda: []
	),
	'⁹': attrdict(
		arity = 0,
		call = lambda: 256
	),
    '+': attrdict(
        arity = 2,
        ldepth = 0,
        rdepth = 0,
        call = operator.add
    ),
}

quicks = {

}

hypers = {

}

str_arities = 'øµð'
str_strings = '“[^«»‘’”]*[«»‘’”]?'
str_charlit = '”.'
str_chrpair = '⁾..'
str_realdec = '(?:0|-?\d*\.\d*|-?\d+|-)'
str_realnum = str_realdec.join(['(?:', '?ȷ', '?|', ')'])
str_complex = str_realnum.join(['(?:', '?ı', '?|', ')'])
str_literal = '(?:%s)' % '|'.join([str_strings, str_charlit, str_chrpair, str_complex])
str_litlist = '\[*' + str_literal + '(?:(?:\]*,\[*)' + str_literal + ')*' + '\]*'
str_nonlits = '|'.join(map(re.escape, list(atoms) + list(quicks) + list(hypers)))

regex_chain = re.compile('(?:^|[' + str_arities + '])(?:' + str_nonlits + '|' + str_litlist + '| )+')
regex_liter = re.compile(str_literal)
regex_token = re.compile(str_nonlits + '|' + str_litlist)
regex_flink = re.compile('(?=.)(?:[' + str_arities + ']|' + str_nonlits + '|' + str_litlist + '| )*¶?')
