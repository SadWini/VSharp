using System.Runtime.InteropServices;

namespace VSharp.Wrapper;

unsafe public class YicesTypes
{
    public enum smt_status
    {
        STATUS_IDLE,
        STATUS_SEARCHING,
        STATUS_UNKNOWN,
        STATUS_SAT,
        STATUS_UNSAT,
        STATUS_INTERRUPTED,
        STATUS_ERROR
    };
    public enum term_constructor_t {
        YICES_CONSTRUCTOR_ERROR = -1, // to report an error

        // atomic terms
        YICES_BOOL_CONSTANT, // boolean constant
        YICES_ARITH_CONSTANT, // rational constant
        YICES_BV_CONSTANT, // bitvector constant
        YICES_SCALAR_CONSTANT, // constant of uninterpreted/scalar
        YICES_VARIABLE, // variable in quantifiers
        YICES_UNINTERPRETED_TERM, // (i.e., global variables, can't be bound)

        // composite terms
        YICES_ITE_TERM, // if-then-else
        YICES_APP_TERM, // application of an uninterpreted function
        YICES_UPDATE_TERM, // function update
        YICES_TUPLE_TERM, // tuple constructor
        YICES_EQ_TERM, // equality
        YICES_DISTINCT_TERM, // distinct t_1 ... t_n
        YICES_FORALL_TERM, // quantifier
        YICES_LAMBDA_TERM, // lambda
        YICES_NOT_TERM, // (not t)
        YICES_OR_TERM, // n-ary OR
        YICES_XOR_TERM, // n-ary XOR

        YICES_BV_ARRAY, // array of boolean terms
        YICES_BV_DIV, // unsigned division
        YICES_BV_REM, // unsigned remainder
        YICES_BV_SDIV, // signed division
        YICES_BV_SREM, // remainder in signed division (rounding to 0)
        YICES_BV_SMOD, // remainder in signed division (rounding to -infinity)
        YICES_BV_SHL, // shift left (padding with 0)
        YICES_BV_LSHR, // logical shift right (padding with 0)
        YICES_BV_ASHR, // arithmetic shift right (padding with sign bit)
        YICES_BV_GE_ATOM, // unsigned comparison: (t1 >= t2)
        YICES_BV_SGE_ATOM, // signed comparison (t1 >= t2)
        YICES_ARITH_GE_ATOM, // atom (t1 >= t2) for arithmetic terms: t2 is always 0
        YICES_ARITH_ROOT_ATOM, // atom (0 <= k <= root_count(p)) && (x r root(p, k)) for r in <, <=, ==, !=, >, >=


        YICES_ABS, // absolute value
        YICES_CEIL, // ceil
        YICES_FLOOR, // floor
        YICES_RDIV, // real division (as in x/y)
        YICES_IDIV, // integer division
        YICES_IMOD, // modulo
        YICES_IS_INT_ATOM, // integrality test: (is-int t)
        YICES_DIVIDES_ATOM, // divisibility test: (divides t1 t2)

        // projections
        YICES_SELECT_TERM, // tuple projection
        YICES_BIT_TERM, // bit-select: extract the i-th bit of a bitvector

        // sums
        YICES_BV_SUM, // sum of pairs a * t where a is a bitvector constant (and t is a bitvector term)
        YICES_ARITH_SUM, // sum of pairs a * t where a is a rational (and t is an arithmetic term)

        // products
        YICES_POWER_PRODUCT // power products: (t1^d1 * ... * t_n^d_n)
    }

    [StructLayout(LayoutKind.Explicit, Size = 12, Pack = 4)]
    public struct term_vector
    {
        [FieldOffset(0)]
        private uint capacity;
        [FieldOffset(4)]
        private uint size;
        [FieldOffset(8)]
        private IntPtr data;
    }
}
