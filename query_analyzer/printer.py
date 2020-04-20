import z3
import os
import time

class Unbuffered(object):
   def __init__(self, stream):
       self.stream = stream
   def write(self, data):
       self.stream.write(data)
       self.stream.flush()
   def writelines(self, datas):
       self.stream.writelines(datas)
       self.stream.flush()
   def __getattr__(self, attr):
       return getattr(self.stream, attr)

import sys
sys.stdout = Unbuffered(sys.stdout)
sys.setrecursionlimit(2000)

cond_counter = -1


def longestRepeatedSubstring(str):
    # Returns the longest repeating non-overlapping
    # substring in str

    n = len(str)
    LCSRe = [[0 for x in range(n + 1)]
             for y in range(n + 1)]

    res = ""  # To store result
    res_length = 0  # To store length of result

    # building table in bottom-up manner
    index = 0
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):

            # (j-i) > LCSRe[i-1][j-1] to remove
            # overlapping
            if (str[i - 1] == str[j - 1] and
                    LCSRe[i - 1][j - 1] < (j - i)):
                LCSRe[i][j] = LCSRe[i - 1][j - 1] + 1

                # updating maximum length of the
                # substring and updating the finishing
                # index of the suffix
                if (LCSRe[i][j] > res_length):
                    res_length = LCSRe[i][j]
                    index = max(i, index)

            else:
                LCSRe[i][j] = 0

    # If we have non-empty result, then insert
    # all characters from first character to
    # last character of string
    if (res_length > 0):
        for i in range(index - res_length + 1,
                       index + 1):
            res = res + str[i - 1]

    if res is None:
        return ''

    res = res.strip()
    par = []
    largest = None
    for k in range(len(res)):
        if res[k] == '(':
            par.append(k)
        elif res[k] == ')':
            if len(par) == 0:
                break
            slice = [par.pop(), k]
            if largest is None or slice[1] - slice[0] > largest[1] - largest[0]:
                largest = slice
    if largest is None:
        return ''
    else:
        return res[largest[0]:largest[1]+1]


class Condition:
    def __init__(self, size, opkind, args):
        self.size = size
        self.opkind = opkind
        self.args = args
        self.vars = None
        self.ops = None
        assert isinstance(args, list)
        assert len(args) > 0

    def __repr__(self):

        s = ''
        if self.opkind == 'extract':
            assert len(self.args) == 3
            s = "%s[%s:%s]" % (self.args[0], self.args[1], self.args[2])
        elif self.opkind == 'ITE':
            assert len(self.args) == 3
            s = "if(%s) { %s } else { %s }" % (
                par_strip(str(self.args[0])), self.args[1], self.args[2])
        elif len(self.args) == 1:
            if self.opkind == 'const':
                s = "%s#%s" % (hex(self.args[0]), self.size)
            elif self.opkind == 'input':
                s = self.args[0]
            elif self.opkind == 'not':
                s = "!(%s)" % par_strip(str(self.args[0]))
            elif self.opkind == '~':
                s = "~(%s)" % par_strip(str(self.args[0]))
            elif self.opkind == 'neg':
                s = "-(%s)" % par_strip(str(self.args[0]))
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

    def get_vars(self):
        if self.vars is None:
            if self.opkind in ['extract', 'SExt', 'ZExt']:
                self.vars = self.args[0].get_vars()
            elif self.opkind == 'const':
                self.vars = set()
            elif self.opkind == 'input':
                self.vars = {self.args[0]}
            else:
                self.vars = set()
                for a in self.args:
                    self.vars = self.vars | a.get_vars()
        return self.vars

    def get_ops(self):
        if self.ops is None:
            if  self.opkind in ['extract', 'SExt', 'ZExt']:
                self.ops = {self.opkind}
                self.ops |= self.args[0].get_ops()
            elif self.opkind == 'const':
                self.ops = set()
            elif self.opkind == 'input':
                self.ops = set()
            else:
                self.ops = {self.opkind}
                for a in self.args:
                    self.ops |= a.get_ops()
        return self.ops


class Transformer:
    def bool_bin_op_remove_leading_zeros(args, opkind):
        # from:
        #   (0x0#N .. X) == (0x0#N .. Z)
        # where:
        #   Y is a const smaller than ???
        # to:
        #   X == Y
        if opkind not in ['==', '!=', '<=u', '>u'] or len(args) != 2:
            return args
        # ToDo: larger const values
        if args[0].opkind == '..' \
                and args[1].opkind == 'const' and args[1].args[0] <= 0xFF \
                and args[0].args[0].opkind == 'const' and args[0].args[0].args[0] == 0:
            #
            args[0] = args[0].args[1]
            args[1].size = args[0].size
        return args

    def bool_bin_op_remove_leading_zeros_both(args, opkind):
        # from:
        #   (0x0#N .. X) == (0x0#N .. Z)
        # to:
        #   X == Y
        if opkind in ['==', '!='] \
                and args[0].opkind == '..' and args[1].opkind == '..' \
                and args[0].args[0].opkind == 'const' and args[0].args[0].args[0] == 0 \
                and args[1].args[0].opkind == 'const' and args[1].args[0].args[0] == 0 \
                and args[0].args[0].size == args[1].args[0].size:
            #
            if len(args[0].args) == 2:
                args[0] = args[0].args[1]
            else:
                args[0].size = args[0].size - args[0].args[0].size
                args[0].args = args[0].args[1:]

            if len(args[1].args) == 2:
                args[1] = args[1].args[1]
            else:
                args[1].size = args[1].size - args[1].args[0].size
                args[1].args = args[1].args[1:]

            return None, Condition(args[0].size, opkind, args)
        return args, None

    def eq_remove_leading_zeros_with_extract(args, opkind):
        # from:
        #   (Z .. X)[high:0] == Y
        # where:
        #   - size(X) == (high + 1) == size(Y)
        # to:
        #   X == Y
        assert opkind == '==' and len(args) == 2
        if args[0].opkind == 'extract' \
                and args[0].args[1] + 1 == args[1].size and args[0].args[2] == 0 \
                and args[0].args[0].opkind == '..' \
                and args[0].args[0].size - args[0].args[0].args[0].size == args[1].size:
            #
            if len(args[0].args[0].args) == 1:
                args[0] = args[0].args[0].args[1]
            else:
                args[0] = args[0].args[0]
                args[0].args = args[0].args[1:]
                args[0].size = args[1].size
        assert len(args[0].args) > 0
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

    def eq_extract_sub_zero_to_eq(args, opkind):
        # from:
        #   ((0#M .. X) - (0#M .. Y)[N:0] == 0
        # where:
        #   N - M == size(X) == size(Y)
        # to:
        #   X == Y
        assert opkind == '==' and len(args) == 2
        if args[1].opkind == 'const' and args[1].args[0] == 0 \
                and args[0].opkind == 'extract' and args[0].args[0].opkind == '-' \
                and len(args[0].args[0].args) == 2 \
                and args[0].args[0].args[0].opkind == '..' \
                and args[0].args[0].args[1].opkind == '..' \
                and args[0].args[0].args[0].args[0].opkind == 'const' \
                and args[0].args[0].args[1].args[0].opkind == 'const' \
                and args[0].args[0].args[0].args[0].size == args[0].args[0].args[1].args[0].size \
                and args[0].args[0].args[0].size - args[0].args[0].args[0].args[0].size == (args[0].args[1] + 1) \
                and args[0].args[2] == 0 and len(args[0].args[0].args) == 2:
            #
            if len(args[0].args[0].args[0].args) == 2:
                args[0].args[0].args[0] = args[0].args[0].args[0].args[1]
            else:
                args[0].args[0].args[0].args = args[0].args[0].args[0].args[1:]
                assert len(args[0].args[0].args[0].args) > 0
                args[0].args[0].args[0].size = (args[0].args[1] + 1)
            if len(args[0].args[0].args[1].args) == 2:
                args[0].args[0].args[1] = args[0].args[0].args[1].args[1]
            else:
                args[0].args[0].args[1].args = args[0].args[0].args[1].args[1:]
                assert len(args[0].args[0].args[1].args) > 0
                args[0].args[0].args[1].size = (args[0].args[1] + 1)
            args[1] = args[0].args[0].args[1]
            args[0] = args[0].args[0].args[0]
        return args

    def concat_concat(args, opkind):
        # from:
        #   (X .. (Y .. Z))
        #   ((X .. Y) .. Z))
        # to:
        #   X .. Y .. Z
        assert opkind == '..'
        if args[0].opkind == '..':
            args = args[0].args + args[1:]
        if args[1].opkind == '..' and len(args) == 2:
            args = [args[0]] + args[1].args
        assert len(args) > 0
        return args

    def concat_merge_const(args, opkind):
        # from:
        #   (0#N1 .. 0#N2 .. X)
        # to:
        #   (0#(N1+N2) .. X)
        assert opkind == '..'
        if args[0].opkind == 'const' and args[0].args[0] == 0 \
                and args[1].opkind == 'const' and args[1].args[0] == 0:
            n = args[0].size + args[1].size
            args = [args[0]] + args[2:]
            assert len(args) > 0
            args[0].size = n
        assert len(args) > 0
        return args

    def extract_concat_bytes(args, opkind, high, low):
        # from:
        #   (X1 .. X2 .. X3 .. [...])[high:low]
        # to:
        #   (Xi .. X(i+1) .. [...])
        # keeping Xi if within [high:low]
        assert opkind == 'extract' and len(args) == 1
        if args[0].opkind == '..':
            slice = 0
            arg_to_keep = []
            sum_size_arg_to_keep = 0
            start = None
            for c in reversed(args[0].args):
                if (slice >= low or (slice + c.size - 1) >= low) and slice <= high:
                    arg_to_keep = [c] + arg_to_keep
                    sum_size_arg_to_keep += c.size
                    if start is None:
                        start = slice
                slice += c.size
            assert len(arg_to_keep) > 0 and start is not None
            if len(arg_to_keep) == 1 and sum_size_arg_to_keep == (high - low) + 1:
                return None, arg_to_keep[0]
            else:
                if sum_size_arg_to_keep == (high - low) + 1:
                    args[0].args = arg_to_keep
                    assert len(args[0].args) > 0
                    args[0].size = (high - low) + 1
                    return None, args[0]
        return args, None

    def extract_concat_bytes_const(args, opkind, high, low):
        # from:
        #   (0#N .. X)[high:low]
        # where: low >= size(X)
        # to:
        #   0#(high - low + 1)
        # keeping Xi if within [high:low]
        assert opkind == 'extract' and len(args) == 1
        if args[0].opkind == '..' and args[0].args[0].opkind == 'const' \
                and args[0].args[0].args[0] == 0 and low >= (args[0].size - args[0].args[0].size):
            args[0].args[0].size = (high - low) + 1
            return None, args[0].args[0]
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
        assert len(args) > 0
        return args, None

    def extract_with_leading_zeros(args, opkind, high, low):
        # from:
        #   (C#M .. X)[N:0]
        # where:
        #   size(X) < N + 1
        # to:
        #   (C#P .. X)
        # with P = N - size(X)
        assert opkind == 'extract' and len(args) == 1
        if args[0].opkind == '..' and args[0].args[0].opkind == 'const' \
                and low == 0 and args[0].size - args[0].args[0].size < high + 1:
            #
            args[0].args[0].size = (high + 1) - \
                (args[0].size - args[0].args[0].size)
            args[0].args[0].args[0] = args[0].args[0].args[0] & (
                (1 << args[0].args[0].size) - 1)
            return None, args[0]
        assert len(args) > 0
        return args, None

    def extract_sub_to_sub(args, opkind, high, low):
        # from:
        #   ((0#M .. X) - C#N)[high:0]
        # where:
        #   - C <= (1 << size(X)) - 1
        # to:
        #   X - C#size(X)
        assert opkind == 'extract' and len(args) == 1
        if args[0].opkind == '-' and len(args[0].args) == 2 \
                and args[0].args[1].opkind == 'const' \
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
                assert len(args[0].args[0].args[1:]) > 0
                a = Condition(high + 1, '..', args[0].args[0].args[1:])
            args = [a, args[0].args[1]]
            args[1].size = high + 1
            assert len(args) > 0
            return None, Condition(high - low + 1, '-', args)

        assert len(args) > 0
        return args, None

    def extract_binop_safe_const(args, opkind, high, low):
        # from:
        #   ((0#M .. X) op C#N)[high:0]
        # where:
        #   - C <= (1 << size(X)) - 1
        #   - ((0#M .. X) op C#N)[high:0] == X op C#size(X), i.e., safe to extract
        # to:
        #   X op C#size(X)
        assert opkind == 'extract' and len(args) == 1
        op = args[0].opkind
        if op not in ['^'] or len(args[0].args) != 2:
            return args, None
        # print(args[0])
        if args[0].args[1].opkind == 'const' \
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
                assert len(args[0].args[0].args) > 0
            if len(args[0].args[0].args[1:]) == 1:
                a = args[0].args[0].args[1]
            else:
                assert len(args[0].args[0].args[1:]) > 0
                a = Condition(high + 1, '..', args[0].args[0].args[1:])
            args = [a, args[0].args[1]]
            assert len(args) > 0
            args[1].size = high + 1
            return None, Condition(high - low + 1, '-', args)

        return args, None

    def extract_and_FF(args, opkind, high, low):
        # from:
        #   (X & C#M)[high:0]
        # where:
        #   - C == ((1 << (high + 1)) - 1)
        # to:
        #   X[high:0]
        assert opkind == 'extract'
        if args[0].opkind == '&' and args[0].args[1].opkind == 'const' and low == 0:
            mask = ((1 << (high + 1)) - 1)
            v = args[0].args[1].args[0] & mask
            if v == mask:
                return None, args[0].args[0]
        assert len(args) > 0
        return args, None

    def or_FF(args, opkind):
        # from:
        #   (X | C#M)
        # where:
        #   - C == ((1 << (high + 1)) - 1)
        # to:
        #   X
        assert opkind == '|'
        if len(args) == 2 and args[1].opkind == 'const' \
                and args[1].args[0] == ((1 << args[1].size) - 1):
            return None, args[0].args[0]
        return args, None

    def extract_add_const(args, opkind, high, low):
        # from:
        #   ((C1#N .. X) + C2#M)[high:0]
        # to:
        #   X + C2#size(X)          when size(X) == (high + 1)
        #   (C1#P1 + X) + C2#P2     otherwise
        assert opkind == 'extract' and len(args) == 1
        if args[0].opkind == '+' and low == 0 and \
                args[0].args[1].opkind == 'const' \
                and args[0].args[0].opkind == '..' \
                and len(args[0].args[0].args) == 2 \
                and args[0].args[0].args[0].opkind == 'const':
            args[0].size = (high + 1)
            args[0].args[1].size = (high + 1)
            args[0].args[1].args[0] = args[0].args[1].args[0] & (
                (1 << (high + 1)) - 1)
            if args[0].args[0].args[1].size == (high + 1):
                args[0].args[0] = args[0].args[0].args[1]
                return None, args[0]
            else:
                args[0].args[0].args[0].size = (
                    high + 1) - args[0].args[0].args[1].size
                args[0].args[0].args[0].args[0] = args[0].args[0].args[0].args[0] & (
                    (1 << args[0].args[0].args[0].size) - 1)
                return None, args[0]
        assert len(args) > 0
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
                # print("bytes[%s] = %s" % (int(a.args[1].args[0] / 8), a.args[0].args[1]))
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
                args = Transformer.concat_concat(args, '..')
                assert len(args) > 0
                return None, Condition(size, '..', args)

        assert len(args) > 0
        return args, None

    def shift_to_const(args, opkind):
        # from:
        #   (0#M .. X) l>> C
        # where:
        #   C == size(X)
        # to:
        #   0#(M + size(X))
        assert opkind == '>>l' and len(args) == 2
        if args[1].opkind == 'const' \
                and args[0].opkind == '..' and len(args[0].args) == 2 \
                and args[0].args[0].opkind == 'const' \
                and args[0].args[0].args[0] == 0 and args[0].args[1].size == args[1].args[0]:
            args[0].args[0].size = args[0].args[0].size + args[0].args[1].size
            return None, args[0].args[0]
        assert len(args) > 0
        return args, None

    def and_const_args(args, opkind):
        # from:
        #   C1#N & C2#N
        # to:
        #   (C1 & C2)#N
        assert opkind == '&' and len(args) == 2
        if args[0].opkind == 'const' and args[1].opkind == 'const':
            assert len([args[0].args[0] & args[1].args[0]]) > 0
            return None, Condition(args[0].size, 'const', [args[0].args[0] & args[1].args[0]])
        return args, None

    def and_arg_FF(args, opkind):
        # from:
        #   X & 0xFFFFF...
        # to:
        #   X
        assert opkind == '&' and len(args) == 2
        if args[0].opkind == 'const' and args[0].args[0] == ((1 << args[0].size) - 1):
            return None, args[1]
        if args[1].opkind == 'const' and args[1].args[0] == ((1 << args[1].size) - 1):
            return None, args[0]
        return args, None

    def or_zero(args, opkind):
        # from:
        #   0#N | X
        # to:
        #   X
        if opkind != '|' or len(args) != 2:
            return args, None
        if args[0].opkind == 'const' and args[0].args[0] == 0:
            if args[1].opkind == 'const' and args[1].args[0] == 0:
                return None, Condition(args[0].size, 'const', [0])
            else:
                return None, args[1]
        elif args[1].opkind == 'const' and args[1].args[0] == 0:
            return None, args[0]
        return args, None

    def eq_ite_const(args, opkind):
        # from:
        #   if (X) { 0#N } else { C#N } == 0#N
        #   if (X) { C#N } else { 0#N } != 0#N
        # to:
        #   X
        # from:
        #   if (X) { C#N } else { 0#N } == 0#N
        # to:
        #   !X
        assert opkind == '==' or opkind == '!='
        if args[1].opkind == 'const' and args[1].args[0] == 0 \
                and args[0].opkind == 'ITE' \
                and args[0].args[1].opkind == 'const' \
                and args[0].args[2].opkind == 'const':
            if opkind == '==' and args[0].args[1].args[0] == 0:
                return None, args[0].args[0]
            elif opkind == '!=' and args[0].args[2].args[0] == 0:
                return None, args[0].args[0]
            elif opkind == '==' and args[0].args[2].args[0] == 0:
                return None, Condition(args[0].args[0].size, 'not', [args[0].args[0]])
        return args, None

    def and_ite_const(args, opkind):
        # from:
        #   (if (X) { C1#N } else { C2#N }) & 0xff#N
        # where:
        #   C1 < 0xff && C2 < 0xff
        # to:
        #  if (X) { C1#N } else { C2#N }
        assert opkind == '&'
        if args[1].opkind == 'const' and args[1].args[0] == 0xFF \
                and args[0].opkind == 'ITE' \
                and args[0].args[1].opkind == 'const' \
                and args[0].args[1].args[0] < 0xFF \
                and args[0].args[2].opkind == 'const' \
                and args[0].args[2].args[0] < 0xFF:
            return None, args[0]
        return args, None

    def evaluate_concrete(args, opkind, high=None, low=None):
        # from:
        #   C#N op C#N
        # to:
        #   (C op C)#N
        if opkind == '^' and len(args) == 2 \
                and args[0].opkind == 'const' and args[1].opkind == 'const':
            args[0].args[0] = args[0].args[0] ^ args[1].args[0]
            return None, args[0]
        if opkind == '>>l' and len(args) == 2 \
                and args[0].opkind == 'const' and args[1].opkind == 'const':
            # ToDo: this should be a logical shift! FixMe
            args[0].args[0] = args[0].args[0] >> args[1].args[0]
            return None, args[0]
        if opkind == '+' and len(args) == 3 \
                and args[1].opkind == 'const' and args[2].opkind == 'const':
            args[1].args[0] = args[1].args[0] + args[2].args[0]
            args.pop()
            assert len(args) > 0
            return args, None
        if opkind == 'extract' and args[0].opkind == 'const' and low == 0:
            args[0].args[0] = args[0].args[0] & ((1 << (high + 1)) - 1)
            args[0].size = high + 1
            return None, args[0]
        if opkind == '..' and len(args) == 2 \
                and args[0].opkind == 'const' and args[1].opkind == 'const':
            args[1].args[0] = args[1].args[0] | (
                args[0].args[0] << args[1].size)
            args[1].size = args[1].size + args[0].size
            return None, args[1]
        return args, None


def get_invert_opkind(opkind):
    if opkind == '==':
        return '!='
    elif opkind == '!=':
        return '=='
    elif opkind == '<=u':
        return '>u'
    elif opkind == '>u':
        return '<=u'
    elif opkind == '>=u':
        return '<u'
    elif opkind == '>=':
        return '<'
    elif opkind == '<u':
        return '>=u'

    print("Inverting %s not yet implemented" % opkind)
    sys.exit(1)


def parse_condition(e):
    opkind = str(e.decl())
    args = []

    op_map = {'ULE': '<=u', 'UGT': '>u', 'UDiv': '/u',
              '/': '/',
              'bvudiv_i': '/u_i', 'UGE': '>=u', '>=': '>=',
              '<=': '<=', 'ULT':'<u', '>':'>', '<':'<',
              'SRem': '%', 'URem': '%u', 'bvsdiv_i': '/i',
              'bvsrem_i': '%i'}

    if opkind == 'bv':
        val = int(e.params()[0])
        bits = e.params()[1]
        return Condition(bits, 'const', [val])
    elif opkind.startswith('input_'):
        return Condition(e.size(), 'input', [str(e)])
    elif opkind.startswith('k!'):
        n = opkind[2:]
        return Condition(e.size(), 'input', ['input_' + n])
    elif opkind.startswith('s_load_'):
        return Condition(e.size(), 'input', [str(e)])
    elif opkind == "True" or opkind == "False":
        return Condition(1, 'input', [str(e)])

    args += [parse_condition(e.arg(0))]

    if opkind == 'Not':
        assert e.num_args() == 1
        if args[0].opkind == 'not':
            return args[0].args[0]
        elif args[0].opkind in ['==', '!=', '<=u', '>u', '>=u', '>=', '<u']:
            args[0].opkind = get_invert_opkind(args[0].opkind)
            return args[0]
        else:
            return Condition(1, 'not', args)

    elif opkind == '~':
        assert e.num_args() == 1
        return Condition(e.size(), '~', args)

    elif opkind == '-' and e.num_args() == 1:
        return Condition(e.size(), 'neg', args)

    elif opkind == 'SignExt':
        assert e.num_args() == 1
        return Condition(e.size(), 'SExt', [args[0]] + e.params())

    elif opkind == 'ZeroExt':
        assert e.num_args() == 1
        return Condition(e.size(), 'ZExt', [args[0]] + e.params())

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

        args, expr = Transformer.extract_and_FF(args, 'extract', high, low)
        if expr:
            return expr

        args, expr = Transformer.extract_with_leading_zeros(
            args, 'extract', high, low)
        if expr:
            return expr

        args, expr = Transformer.extract_add_const(args, 'extract', high, low)
        if expr:
            return expr

        args, expr = Transformer.extract_binop_safe_const(
            args, 'extract', high, low)
        if expr:
            return expr

        args, expr = Transformer.evaluate_concrete(args, 'extract', high, low)
        if expr:
            return expr

        args, expr = Transformer.extract_concat_bytes_const(
            args, 'extract', high, low)
        if expr:
            return expr

        return Condition(e.size(), 'extract', [args[0]] + e.params())

    for k in range(1, e.num_args()):
        args += [parse_condition(e.arg(k))]

    size = int(e.size()) if str(e.sort()) != 'Bool' else 1

    if opkind == 'Concat':
        opkind = '..'
        args = Transformer.concat_concat(args, opkind)
        args = Transformer.concat_merge_const(args, opkind)

        args, expr = Transformer.evaluate_concrete(args, opkind)
        if expr:
            return expr

    elif opkind == 'If':
        opkind = 'ITE'

    elif opkind == '==' or opkind == '!=':
        args = Transformer.bool_bin_op_remove_leading_zeros(args, opkind)
        args = Transformer.eq_extract_sub_zero_to_eq(args, opkind)
        args = Transformer.eq_sub_zero_to_eq(args, opkind)
        args = Transformer.eq_remove_leading_zeros_with_extract(args, opkind)
        args = Transformer.bool_bin_op_remove_leading_zeros(args, opkind)

        args, expr = Transformer.bool_bin_op_remove_leading_zeros_both(
            args, opkind)
        if expr:
            return expr

        args, expr = Transformer.eq_ite_const(args, opkind)
        if expr:
            return expr

    elif opkind in ['+', '-', '<<', 'LShR', '^', '*', '>>']:
        if opkind == 'LShR':
            opkind = '>>l'
            args, expr = Transformer.shift_to_const(args, opkind)
            if expr:
                return expr

        args, expr = Transformer.evaluate_concrete(args, opkind)
        if expr:
            return expr

    elif opkind in op_map:

        opkind = op_map[opkind]
        args = Transformer.bool_bin_op_remove_leading_zeros(args, opkind)

    elif opkind == 'And':
        assert str(e.sort()) == 'Bool'
        opkind = '&&'

    elif opkind == 'Or':
        assert str(e.sort()) == 'Bool'
        opkind = '||'

    elif opkind in ['&']:
        opkind = '&'
        args, expr = Transformer.and_const_args(args, opkind)
        if expr:
            return expr

        args, expr = Transformer.and_arg_FF(args, opkind)
        if expr:
            return expr

        args, expr = Transformer.and_ite_const(args, opkind)
        if expr:
            return expr

    elif opkind in ['|']:
        args, expr = Transformer.or_lshifted_bytes(args, opkind)
        if expr:
            return expr

        args, expr = Transformer.or_zero(args, opkind)
        if expr:
            return expr

        args, expr = Transformer.or_FF(args, opkind)
        if expr:
            return expr

    else:
        assert opkind not in op_map
        print("parse_condition for opkind %s not yet implemented" % opkind)
        sys.exit(1)

    res = Condition(size, opkind, args)

    # print(res)
    return res


def par_strip(s):
    if s[0] == '(' and s[-1] == ')':
        s = s[1:-1]
    return s

def get_defs(cond, defs, to_skip):
    s = ''
    for v in sorted(defs.keys()):
        if v in to_skip:
            continue
        label = "x_%s" % v
        index = 0
        while label in cond[index:]:
            index = cond[index:].index(label)
            assert index > 0 and len(label) > 0
            index += len(label)
            if not cond[index].isdigit() or True:
                to_skip.append(v)
                s += get_defs(defs[v], defs, to_skip)
                s += "x_%s = %s;\n" % (v, par_strip(defs[v]))
                break
    return s

def traslate_to_pseudocode(query):

    global cond_counter
    s = ''
    S = []
    C = []

    if str(query.decl()) != 'And':
        conjs = [query]
    else:
        conjs = query.children()

    defs = {}
    deps = {}
    parsed_exprs = set()
    for e in conjs:
        if e.get_id() in parsed_exprs:
            continue
        parsed_exprs.add(e.get_id())
        c = parse_condition(e)
        cond = str(c)
        for v in defs:
            cond = cond.replace(defs[v], 'x_%s' % v)

        r = longestRepeatedSubstring(cond).strip()
        while len(r) > 6 and r[0] == '(' and r[-1] == ')':
            v = len(defs)
            defs[v] = r
            cond = cond.replace(r, "x_%s" % v)
            r = longestRepeatedSubstring(cond)

        cond_counter += 1
        cs = get_defs(cond, defs, [])
        cs += "c%s = %s;\n" % (cond_counter, par_strip(cond))
        cs += 'assert(c%s);\n' % cond_counter
        # cs += 'vars_c%s = %s;\n' % (cond_counter, c.get_vars())
        # cs += '\n'

        s += cs
        S.append(cs)
        C.append(c)

        for d in c.get_vars():
            if d not in deps:
                deps[d] = []
            deps[d].append(cond_counter)

    return s, S, C, deps


def is_checksum(e):
    # condition 0: (in)equality
    if e.opkind in ['==', '!=']:
        assert len(e.args) == 2
        # condition 1: both operands involve input bytes
        if not (len(e.args[0].get_vars()) > 0 and len(e.args[1].get_vars()) > 0):
            return False
        # condition 2: operands involve disjoint input bytes
        if e.args[0].get_vars() & e.args[1].get_vars() != set():
            return False
        # condition 3: one operand is input-to-state
        i2s_args = [0, 1]
        for k in [0, 1]:
            if len(e.args[k].get_ops() - set(['..', 'extract', '<<l'])) != 0:
                i2s_args.remove(k)
        if len(i2s_args) != 1:
            return False
        # condition 4: other operand is not input-to-state
        if len(e.args[(i2s_args[0] + 1) % 2].get_ops() & set(['^'])) == 0:
            return False
        # print("Expression is a checksum")
        return True
    return False

def get_input_state_arg(e):
    assert len(e.args) == 2
    i2s_args = []
    not_i2s_args = []
    for k in [0, 1]:
        if len(e.args[k].get_ops() - set(['..', 'extract', '<<l'])) != 0:
            not_i2s_args.append(e.args[k])
        elif e.args[k].get_vars() == set():
            not_i2s_args.append(e.args[k])
        else:
            i2s_args.append(e.args[k])
    return i2s_args, not_i2s_args

def get_concrete_arg(e):
    assert len(e.args) == 2
    concrete = []
    non_concrete = []
    for k in [0, 1]:
        if e.args[k].get_vars() == set():
            concrete.append(e.args[k])
        else:
            non_concrete.append(e.args[k])
    return concrete, non_concrete

def find_opkind_expr(e, opkinds, depth):
    if e.opkind in opkinds:
        return [depth, e, set()]
    res = []
    other_opkinds = set([e.opkind])
    if e.opkind == 'const':
        return [None, None, None]
    elif e.opkind == 'input':
        return [None, None, None]
    elif e.opkind in ['extract', 'SExt', 'ZExt']:
        r = find_opkind_expr(e.args[0], opkinds, depth + 1)
        if r[0]:
            r[2] |= other_opkinds
            res.append(r)
    else:
        for a in e.args:
            r = find_opkind_expr(a, opkinds, depth + 1)
            if r[0]:
                res.append(r)
    if len(res) == 0:
        return [None, None, other_opkinds]
    else:
        res = sorted(res, key = lambda x: x[0])
        for k in range(len(res)):
            other_opkinds |= res[k][2]
        return [res[0][0], res[0][1], other_opkinds]

def find_expr(e, e2):
    if str(e) == str(e2):
        return True
    if e.opkind == 'const':
        return False
    elif e.opkind == 'input':
        return False
    elif e.opkind in ['extract', 'SExt', 'ZExt']:
        return find_expr(e.args[0], e2)
    else:
        for a in e.args:
            r = find_expr(a, e2)
            if r:
                return True
    return False

def is_mul_overflow_p1(e):
    # pattern:
    #   (a * b) / b == a
    #   (b * a) / b == a
    # where a is not concrete
    if e.opkind in ['==', '!=']:
        assert len(e.args) == 2
        i2s_args, others = get_input_state_arg(e)
        if len(i2s_args) != 1:
            return False
        i2s_arg = i2s_args[0]
        other_arg = others[0]

        if not i2s_arg.get_vars().issubset(other_arg.get_vars()):
            return False
        if '/u' not in other_arg.get_ops():
            return False
        if '*' not in other_arg.get_ops() and '<<' not in other_arg.get_ops() and '>>l' not in other_arg.get_ops():
            return False

        depth_1, a_mul_b_div_b, _= find_opkind_expr(other_arg, ['/u'], 0)
        depth_2, a_mul_b, _ = find_opkind_expr(other_arg, ['*', '<<', '>>l'], 0)

        if depth_1 is None:
            return False

        if depth_2 is None:
            return False

        if depth_1 >= depth_2:
            return False
        if not i2s_arg.get_vars().issubset(a_mul_b.get_vars()):
            return False
        # pattern: (a * b) / b == a
        if i2s_arg.get_vars() == a_mul_b.args[0].get_vars():
            if a_mul_b.args[1].get_vars() == a_mul_b_div_b.args[1].get_vars():
                # print("Expression is a mul overflow\n")
                return True
        # pattern: (a * b) / a == b
        if i2s_arg.get_vars() == a_mul_b.args[1].get_vars():
            if a_mul_b.args[0].get_vars() == a_mul_b_div_b.args[1].get_vars():
                # print("Expression is a mul overflow\n")
                return True
    return False

def is_mul_overflow_p2(e):
    # pattern:
    #   (a * b) / b == a
    #   (b * a) / b == a
    # where a is concrete
    if e.opkind in ['==', '!=']:
        assert len(e.args) == 2
        concrete_args, non_concrete_args = get_concrete_arg(e)
        if len(concrete_args) != 1:
            return False
        concrete_arg = concrete_args[0]
        other_arg = non_concrete_args[0]

        if '/u' not in other_arg.get_ops():
            return False
        if '*' not in other_arg.get_ops() and '<<' not in other_arg.get_ops() and '>>l' not in other_arg.get_ops():
            return False

        # pattern: (a * b) / b == a
        depth_1, a_mul_b_div_b, _ = find_opkind_expr(other_arg, ['/u'], 0)
        depth_2, a_mul_b, _ = find_opkind_expr(other_arg, ['*', '<<'], 0)

        if depth_1 is None:
            return False

        if depth_2 is None:
            return False

        # pattern: (a * b) / b == a
        if concrete_arg.get_vars() == a_mul_b.args[0].get_vars():
            if a_mul_b.args[1].get_vars() == a_mul_b_div_b.args[1].get_vars():
                # print("Expression is a mul overflow\n")
                return True
        # pattern: (a * b) / a == b
        if concrete_arg.get_vars() == a_mul_b.args[1].get_vars():
            if a_mul_b.args[0].get_vars() == a_mul_b_div_b.args[1].get_vars():
                # print("Expression is a mul overflow\n")
                return True

    return False

def is_mul_overflow(e):
    if is_mul_overflow_p1(e):
        return True
    return is_mul_overflow_p2(e)

def is_add_overflow(e):
    #   a + b < b
    #   a + b < a
    if e.opkind in ['<', '<u','>=', '>=u', '>', '>=', '>u', '>=u', '<=', '<=u']:
        assert len(e.args) == 2
        depth_1, x, other_ops_x = find_opkind_expr(e.args[0], ['+'], 0)
        depth_2, y, other_ops_y = find_opkind_expr(e.args[1], ['+'], 0)
        if depth_1 is None and depth_2 is None:
            return False
        if depth_1 is None:
            a_add_b = y
            other_ops = other_ops_y
            b = e.args[0]
        elif depth_2 is None:
            a_add_b = x
            other_ops = other_ops_x
            b = e.args[1]
        elif depth_1 < depth_2 and not find_expr(e.args[1], x):
            a_add_b = x
            other_ops = other_ops_x
            b = e.args[1]
        elif not find_expr(e.args[0], y):
            a_add_b = y
            other_ops = other_ops_y
            b = e.args[0]
        else:
            return False

        if len(other_ops - set(['..', 'extract'])) > 0:
            return False

        if b.get_vars() == a_add_b.args[0].get_vars():
            if b.get_vars() != set():
                return True
            else:
                return b.args[0] == a_add_b.args[0]
        if b.get_vars() == a_add_b.args[1].get_vars():
            if b.get_vars() != set():
                return True
            else:
                return b.args[0] == a_add_b.args[1]
    return False

def remove_condition(e):
    if is_checksum(e):
        return True
    if is_mul_overflow(e):
        return True
    if is_add_overflow(e):
        return True
    return False

if len(sys.argv) != 2:
    print("Usage: %s <query_smtlib_file>" % sys.argv[0])
    sys.exit(1)

query_file = sys.argv[1]
query = z3.parse_smt2_file(query_file)

if False:
    print(query)
    print("\n##########\n")

    print(z3.simplify(query))
    print("\n##########\n")

if str(query) in ['True', 'False']:
    print(query)
    sys.exit(0)

s, S, C, deps = traslate_to_pseudocode(query)

if False:
    print(s)
else:
    last_branch = C[-1]
    C_deps = set()
    vars_done = set()
    vars = last_branch.get_vars()
    while len(vars) > 0:
        v = vars.pop()
        vars_done.add(v)
        X = deps[v]
        C_deps |= set(X)
        for x in X:
            for vv in C[x].get_vars():
                if vv not in vars_done:
                    vars.add(vv)

    S_deps = []
    for x in C_deps:
        S_deps.append(x)
    S_deps = sorted(S_deps)
    for x in S_deps:
        print("%s" % S[x])
        if is_checksum(C[x]):
            print("Condition c%s detected as checksum\n" % x)
        if is_mul_overflow(C[x]):
            print("Condition c%s detected as mul overflow\n" % x)
        if is_add_overflow(C[x]):
            print("Condition c%s detected as add overflow\n" % x)
    print("\n#######\n")

if False:
    solver = z3.Solver()
    prev = query.children()[:-1]
    assert len(query.children()) - 1 == len(prev)
    for k in range(len(prev)):
        if k in S_deps and not remove_condition(C[k]):
        #if not remove_condition(C[k]):
            solver.add(prev[k])
    start = time.time()
    solver.set("timeout", 15000)
    r = solver.check()
    end = time.time()
    print("prev branches is %s - time %s\n" % (r, str(end - start)))
if False:
    solver = z3.Solver()
    if not remove_condition(C[-1]):
        solver.add(query.children()[-1])
    start = time.time()
    solver.set("timeout", 15000)
    r = solver.check()
    end = time.time()
    print("current branch is %s - time %s\n" % (r, str(end - start)))

if True:
    solver = z3.SimpleSolver()
    solver.set(':core.minimize', True)
    E = query.children()
    ctracks = []
    for k in range(len(E)):
        if True:
        #if k in S_deps and not remove_condition(C[k]):
        #if not remove_condition(C[k]):
            ctrack = z3.Bool('p' + str(len(ctracks)))
            solver.assert_and_track(E[k], ctrack)
            ctracks.append(ctrack)
    start = time.time()
    solver.set(timeout=15000)
    r = solver.check()
    end = time.time()
    print("query is %s - time %s\n" % (r, str(end - start)))

    if False and str(r) == 'unsat':
        unsat_core = solver.unsat_core()
        for p in unsat_core:
            idx = str(p).split("p")[1]
            s, S, C, deps = traslate_to_pseudocode(E[int(idx)])
            print(s)
            #print(E[int(idx)])