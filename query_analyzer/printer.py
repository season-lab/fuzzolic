import z3
import os
import sys
import time

cond_counter = 0


class Condition:
    def __init__(self, size, opkind, args):
        self.size = size
        self.opkind = opkind
        self.args = args
        assert isinstance(args, list)

    def __repr__(self):

        s = ''
        if self.opkind == 'extract':
            assert len(self.args) == 3
            s = "%s[%s:%s]" % (self.args[0], self.args[1], self.args[2])
        elif self.opkind == 'ITE':
            assert len(self.args) == 3
            s = "if(%s) { %s } else { %s }" % (
                self.args[0], self.args[1], self.args[2])
        elif len(self.args) == 1:
            if self.opkind == 'const':
                s = "%s#%s" % (hex(self.args[0]), self.size)
            elif self.opkind == 'input':
                s = self.args[0]
            elif self.opkind == 'not':
                s = "!(%s)" % self.args[0]
            else:
                print("Unknown %s opkind" % self.opkind)
                sys.exit(1)
        else:
            for k in range(len(self.args)):
                if k == 0:
                    s += "(%s" % self.args[k]
                else:
                    s += " %s %s" % (self.opkind, self.args[k])
            s += ')'
        return s


class Transformer:
    def remove_leading_zeros(args, opkind):
        # from:
        #   (0x0#N .. X) == Y#M
        # where:
        #   Y is a const smaller than ???
        # to:
        #   X == Y
        assert opkind == '==' and len(args) == 2
        # ToDo: larger const values
        if args[0].opkind == '..' and len(args[0].args) == 2 \
                and args[1].opkind == 'const' and args[1].args[0] <= 0xFF \
                and args[0].args[0].opkind == 'const' and args[0].args[0].args[0] == 0:
            #
            args[0] = args[0].args[1]
            args[1].size = args[0].size
        return args

    def eq_sub_zero_to_eq(args, opkind):
        # from:
        #   X - Y == 0
        # to:
        #   X == Y
        assert opkind == '==' and len(args) == 2
        if args[1].opkind == 'const' and args[1].args[0] == 0 \
                and args[0].opkind == '-' and len(args[0].args) == 2:
            #
            args[1] = args[0].args[1]
            args[0] = args[0].args[0]
        return args

    def concat_concat(args, opkind):
        # from:
        #   (X .. (Y .. Z))
        # to:
        #   X .. Y .. Z
        assert opkind == '..'
        if args[0].opkind == '..':  # merge concat
            args = args[0].args + args[1:]
        return args

    def extract_concat_bytes(args, opkind, high, low):
        # from:
        #   (X1 .. X2 .. X3 .. [...])[high:low]
        # to:
        #   (Xi .. X(i+1))
        # keeping Xi if within [high:low]
        assert opkind == 'extract' and len(args) == 1
        if args[0].opkind == '..':
            slice = 0
            arg_to_keep = []
            start = None
            for c in reversed(args[0].args):
                if (slice >= low or (slice + c.size - 1) >= low) and slice <= high:
                    arg_to_keep = arg_to_keep + [c]
                    if start is None:
                        start = slice
                slice += c.size
            assert len(arg_to_keep) > 0 and start is not None
            if len(arg_to_keep) == 1:
                return None, arg_to_keep[0]
            else:
                pass  # ToDo
        return args, None

    def extract_same_size(args, opkind, high, low):
        # from:
        #   X[N:0]
        # where:
        #   - size(X) == N
        # to:
        #   X
        assert opkind == 'extract' and len(args) == 1
        if args[0].size == (high - low + 1):
            return None, args[0]
        return args, None

    def extract_sub_to_sub(args, opkind, high, low):
        # from:
        #   ((0#M .. X) - C#N)[high:0]
        # where:
        #   - C <= (1 << size(X)) - 1
        # to:
        #   X - C#size(X)
        assert opkind == 'extract' and len(args) == 1
        if args[0].opkind == '-' and args[0].args[1].opkind == 'const' \
                and low == 0 and args[0].args[1].args[0] <= ((1 << (high + 1)) - 1) \
                and args[0].args[0].opkind == '..' \
                and args[0].args[0].args[0].size >= (args[0].args[0].size - (high + 1)) \
                and args[0].args[0].args[0].opkind == 'const' and args[0].args[0].args[0].args[0] == 0:
            #
            if args[0].args[0].args[0].size > (args[0].args[0].size - (high + 1)):
                a = Condition(args[0].args[0].args[0].size -
                              (args[0].args[0].size - (high + 1)), 'const', [0])
                args[0].args[0].args = [args[0].args[0].args[0]] + \
                    [a] + args[0].args[0].args[1:]
            if len(args[0].args[0].args[1:]) == 1:
                a = args[0].args[0].args[1]
            else:
                a = Condition(high + 1, '..', args[0].args[0].args[1:])
            args = [a, args[0].args[1]]
            args[1].size = high + 1
            return None, Condition(high - low + 1, '-', args)

        return args, None

    def or_lshifted_bytes(args, opkind):
        # from:
        #   ((0#N .. X1) | ((0#N .. X2) << K1) | ((0#N .. X3) << K2) | ((0#N .. X4) << K3) | [...] )
        # where:
        #   - Ki \in {8, 16, 24, ...}
        #   - size(Xi) == 8, i.e., a single byte
        # to:
        #   (0#M .. [...] .. X4 .. X3 .. X2 .. X1)
        assert opkind == '|'

        bytes = {}  # distinct bytes
        size = args[0].size

        pattern_lshift_bytes = True
        for k in range(len(args)):
            a = args[k]
            if a.opkind == '..' and 0 not in bytes \
                and a.args[0].opkind == 'const' and a.args[0].args[0] == 0 \
                    and a.args[1].opkind == 'input' and a.args[1].size == 8:
                #
                bytes[0] = a.args[1]
                continue
            if a.opkind == '<<' \
                and a.args[1].opkind == 'const' and a.args[1].args[0] % 8 == 0 \
                and int(a.args[1].args[0] / 8) not in bytes \
                and a.args[0].opkind == '..' \
                and a.args[0].args[0].opkind == 'const' and a.args[0].args[0].args[0] == 0 \
                    and a.args[0].args[1].opkind == 'input' and a.args[0].args[1].size == 8:
                #
                bytes[int(a.args[1].args[0] / 8)] = a.args[0].args[1]
                continue
            pattern_lshift_bytes = False

        if pattern_lshift_bytes:
            offsets = sorted(bytes.keys())
            if offsets == list(range(1)) \
                    or offsets == list(range(2)) \
                    or offsets == list(range(4)) \
                    or offsets == list(range(8)):
                #
                assert len(offsets) <= int(size / 8)
                args = []
                if len(offsets) < int(size / 8):
                    args += [Condition(size - (len(offsets)
                                               * 8), 'const', [0])]
                for o in reversed(offsets):
                    args += [bytes[o]]
                return None, Condition(size, '..', args)

        return args, None


def get_invert_opkind(opkind):
    if opkind == '==':
        return '!='

    print("Inverting %s not yet implemented" % opkind)
    sys.exit(1)


def parse_condition(e, invert_opkind=False):
    opkind = str(e.decl())
    args = []

    if opkind == 'bv':
        val = int(e.params()[0])
        bits = e.params()[1]
        return Condition(bits, 'const', [val])
    elif opkind.startswith('input_'):
        return Condition(e.size(), 'input', [str(e)])

    args += [parse_condition(e.arg(0))]

    if opkind == 'Not':
        assert e.num_args() == 1
        if str(e.arg(0).decl()) in ['==', '!=']:
            return args[0]
        else:
            return Condition(1, 'not', args)
    elif opkind == 'Extract':
        assert e.num_args() == 1

        high, low = e.params()

        args, expr = Transformer.extract_same_size(args, 'extract', high, low)
        if expr:
            return expr

        args, expr = Transformer.extract_concat_bytes(
            args, 'extract', high, low)
        if expr:
            return expr

        args, expr = Transformer.extract_sub_to_sub(args, 'extract', high, low)
        if expr:
            return expr

        return Condition(e.size(), 'extract', [args[0]] + e.params())

    for k in range(1, e.num_args()):
        args += [parse_condition(e.arg(k))]

    if invert_opkind:
        opkind = get_invert_opkind(opkind)

    size = int(e.size()) if str(e.sort()) != 'Bool' else 1

    if opkind == 'Concat':
        opkind = '..'
        args = Transformer.concat_concat(args, opkind)

    elif opkind == 'If':
        opkind = 'ITE'

    elif opkind == '==' or opkind == '!=':
        args = Transformer.remove_leading_zeros(args, opkind)
        args = Transformer.eq_sub_zero_to_eq(args, opkind)
        args = Transformer.remove_leading_zeros(args, opkind)

    elif opkind in ['+', '-', '<<']:
        assert e.num_args() == 2

    elif opkind == 'ULE':
        opkind = '<=u'

    elif opkind == 'And':
        assert str(e.sort()) == 'Bool'
        opkind = '&&'

    elif opkind in ['&']:
        opkind = '&'

    elif opkind in ['|']:
        args, expr = Transformer.or_lshifted_bytes(args, opkind)
        if expr:
            return expr

    else:
        print("parse_condition for opkind %s not yet implemented" % opkind)
        sys.exit(1)

    res = Condition(size, opkind, args)

    # print(res)
    return res


def traslate_to_pseudocode(query):

    global cond_counter
    s = ''

    if str(query.decl()) != 'And':
        conjs = [query]
    else:
        conjs = query.children()

    for e in conjs:

        cond = parse_condition(e)
        cond_counter += 1
        s += "c%s = %s;\n" % (cond_counter, str(cond)[1:].rstrip(')'))
        s += 'assert(c%s);\n\n' % cond_counter

    return s


if len(sys.argv) != 2:
    print("Usage: %s <query_smtlib_file>" % sys.argv[0])
    sys.exit(1)

query_file = sys.argv[1]
query = z3.parse_smt2_file(query_file)
#query = z3.simplify(query)

print(query)
print("\n##########\n")

if False:
    solver = z3.Solver()
    solver.add(query)
    start = time.time()
    solver.check()
    end = time.time()
    print(end - start)

if str(query) not in ['True', 'False']:
    code = traslate_to_pseudocode(query)
    print(code)
