using System;
using System.Runtime.InteropServices;

public class Yices
{
    enum term_constructor_t
    {
         YICES_CONSTRUCTOR_ERROR = -1, // to report an error

        // atomic terms
        YICES_BOOL_CONSTANT,       // boolean constant
        YICES_ARITH_CONSTANT,      // rational constant
        YICES_BV_CONSTANT,         // bitvector constant
        YICES_SCALAR_CONSTANT,     // constant of uninterpreted/scalar
        YICES_VARIABLE,            // variable in quantifiers
        YICES_UNINTERPRETED_TERM,  // (i.e., global variables, can't be bound)

        // composite terms
        YICES_ITE_TERM,            // if-then-else
        YICES_APP_TERM,            // application of an uninterpreted function
        YICES_UPDATE_TERM,         // function update
        YICES_TUPLE_TERM,          // tuple constructor
        YICES_EQ_TERM,             // equality
        YICES_DISTINCT_TERM,       // distinct t_1 ... t_n
        YICES_FORALL_TERM,         // quantifier
        YICES_LAMBDA_TERM,         // lambda
        YICES_NOT_TERM,            // (not t)
        YICES_OR_TERM,             // n-ary OR
        YICES_XOR_TERM,            // n-ary XOR

        YICES_BV_ARRAY,            // array of boolean terms
        YICES_BV_DIV,              // unsigned division
        YICES_BV_REM,              // unsigned remainder
        YICES_BV_SDIV,             // signed division
        YICES_BV_SREM,             // remainder in signed division (rounding to 0)
        YICES_BV_SMOD,             // remainder in signed division (rounding to -infinity)
        YICES_BV_SHL,              // shift left (padding with 0)
        YICES_BV_LSHR,             // logical shift right (padding with 0)
        YICES_BV_ASHR,             // arithmetic shift right (padding with sign bit)
        YICES_BV_GE_ATOM,          // unsigned comparison: (t1 >= t2)
        YICES_BV_SGE_ATOM,         // signed comparison (t1 >= t2)
        YICES_ARITH_GE_ATOM,       // atom (t1 >= t2) for arithmetic terms: t2 is always 0
        YICES_ARITH_ROOT_ATOM,     // atom (0 <= k <= root_count(p)) && (x r root(p, k)) for r in <, <=, ==, !=, >, >=


        YICES_ABS,                 // absolute value
        YICES_CEIL,                // ceil
        YICES_FLOOR,               // floor
        YICES_RDIV,                // real division (as in x/y)
        YICES_IDIV,                // integer division
        YICES_IMOD,                // modulo
        YICES_IS_INT_ATOM,         // integrality test: (is-int t)
        YICES_DIVIDES_ATOM,        // divisibility test: (divides t1 t2)

        // projections
        YICES_SELECT_TERM,         // tuple projection
        YICES_BIT_TERM,            // bit-select: extract the i-th bit of a bitvector

        // sums
        YICES_BV_SUM,              // sum of pairs a * t where a is a bitvector constant (and t is a bitvector term)
        YICES_ARITH_SUM,           // sum of pairs a * t where a is a rational (and t is an arithmetic term)

        // products
        YICES_POWER_PRODUCT        // power products: (t1^d1 * ... * t_n^d_n)
    }
    // Creation of constant expressions
    [DllImport("libyices.dll")]
    public static extern int yices_true();

    public static int MkTrue()
    {
        return yices_true();
    }
    [DllImport("libyices.dll")]
    public static extern int yices_false();
    public static int MkFalse()
    {
        return yices_false();
    }

    //abstract member MkConst: string * 'ISort -> 'IExpr

    //abstract member MkConstDecl: string * 'ISort -> 'IFuncDecl
    [DllImport("libyices.dll")]
    public static extern int yices_new_uninterpreted_term(int x);
    [DllImport("libyices.dll")]
    public static extern int yices_set_type_name(int x, string name);
    int MkConstDecl(int x, string name)
    {
        int newTerm = yices_new_uninterpreted_term(x);
        int flag = yices_set_type_name(newTerm, name);
        //if (flag == -1) throw error?
        return newTerm;
    }

    [DllImport("libyices.dll")]
    public static extern int yices_type_is_bitvector(int t);
    [DllImport("libyices.dll")]
    public static extern uint yices_bvtype_size(int t);
    //abstract member MkNumeral: string * 'ISort -> 'IExpr
    static public int MkNumeral(string v, int typ)
    {
        if (yices_type_is_bitvector(typ) == 1)
        {
            uint size = yices_bvtype_size(typ);
            if (Int32.TryParse(v, out int value))
                return yices_bvconst_int32(size, value);
            throw new FormatException("Can't parse int from string in MkNumeral(int, int)");
        }
        throw new ArgumentException("Not supported type in MkNumeral(string, int)");
    }

    //abstract member MkNumeral: uint * 'ISort -> 'IExpr
    static public int MkNumeral(uint v, int typ)
    {
        if (yices_type_is_bitvector(typ) == 1)
        {
            uint size = yices_bvtype_size(typ);
            return yices_bvconst_uint32(size, v);
        }
        throw new ArgumentException("Not supported type in MkNumeral(uint, int)");
    }

    //abstract member MkNumeral: int * 'ISort -> 'IExpr
    static public int MkNumeral(int v, int typ)
    {
        if (yices_type_is_bitvector(typ) == 1)
        {
            uint size = yices_bvtype_size(typ);
            return yices_bvconst_int32(size, v);
        }
        throw new ArgumentException("Not supported type in MkNumeral(int, int)");
    }

    //TO DO Implement FP Theory
    //abstract member MkFPNumeral: float32 * 'ISort -> 'IExpr
    //abstract member MkFPDoubleNumeral: float * 'ISort -> 'IExpr
    //abstract member MkFPRoundNearestTiesToEven: unit -> 'IExpr

//Creating sorts
    //abstract member MkBoolSort: unit -> 'ISort
    [DllImport("libyices.dll")]
    public static extern int yices_bool_type();

    public static int MkBoolSort()
    {
        return yices_bool_type();
    }
    //abstract member MkBitVecSort: uint -> 'ISort
    [DllImport("libyices.dll")]
    public static extern int yices_bv_type(uint size);

    public static int MkBitVecSort(uint size)
    {
        return yices_bv_type(size);
    }

    //TO DO Implement FP Theory
    //abstract member MkFPSort32: unit -> 'ISort
    //abstract member MkFPSort64: unit -> 'ISort

    //https://www.yumpu.com/en/document/read/10134532/yices-tutorial-the-yices-smt-solver-sri-international
    //Need to grasp how to implement array theory in function terms
    abstract member MkArraySort: 'ISort * 'ISort -> 'ISort
    abstract member MkRangeArraySort: 'ISort array * 'ISort -> 'ISort

    //abstract member BoolSort: unit -> 'ISort
    public static int BoolSort()
    {
        return yices_bool_type();
    }

//Creating terms
    //abstract member MkBV: uint32 * uint32 -> 'IBitVecExpr
    [DllImport("libyices.dll")]
    public static extern int yices_bvconst_uint32(uint size, uint v);
    public static int MkBV(uint v, uint size)
    {
        return yices_bvconst_uint32(size, v);
    }
    //abstract member MkBVInt: int * uint32 -> 'IBitVecExpr
    [DllImport("libyices.dll")]
    public static extern int yices_bvconst_int32(uint size, int v);
    public static int MkBVInt(int v, uint size)
    {
        return yices_bvconst_int32(size, v);
    }
    //abstract member MkBool: bool -> 'IBoolExpr
    public int MkBool(bool v)
    {
        return v ? yices_true() : yices_false();
    }
    //TO DO Implement FP Theory
    //abstract member MkFPToFP: 'IExpr * 'IFPExpr * 'ISort -> 'IFPExpr
    //abstract member MkFPToFP: 'IExpr * 'IBitVecExpr * 'ISort * bool -> 'IFPExpr

    //abstract member MkApp: 'IFuncDecl * [<ParamArray>] parameters : 'IExpr array -> 'IExpr
    [DllImport("libyices.dll")]
    public static extern int yices_application(int f, uint n, int[] arg);
    public static int MkApp(int f, params int[] args)
    {
        return yices_application(f, (uint) args.Length, args);
    }

    //abstract member MkFuncDecl: string * 'ISort array * 'ISort -> 'IFuncDecl
    [DllImport("libyices.dll")]
    public static extern int yices_function_type(uint n, int[] dom, int range);
    public static int MkFuncDecl(string name, int[] dom, int range)
    {
        int typ = yices_function_type((uint) dom.Length, dom, range);
        int newTerm = yices_new_uninterpreted_term(typ);
        int flag = yices_set_type_name(newTerm, name);
        //if (flag == -1) throw error?
        return newTerm;
    }
    //TO DO Implement FP Theory
    //abstract member MkFP: 'IBitVecExpr * 'IBitVecExpr * 'IBitVecExpr -> 'IFPExpr

//Array operations
    abstract member MkSelect: 'IArrayExpr * 'IExpr -> 'IExpr
    abstract member MkRangeSelect: 'IArrayExpr * 'IExpr array -> 'IExpr

//Solver operations
    abstract member MkSolver: uint option -> 'ISolver

//Terms conversion
    //TO DO Implement FP Theory
    //FP to BV and vice versa
    //abstract member MkFPToIEEEBV: 'IFPExpr -> 'IBitVecExpr
    //abstract member MkFPToBV: 'IExpr * 'IFPExpr * uint * bool -> 'IBitVecExpr

    //down casts from expr
    //Just return variable because all types are int
    abstract member MkEToBE: 'IExpr -> 'IBoolExpr
    abstract member MkEToBVE: 'IExpr -> 'IBitVecExpr
    abstract member MkEToFPE: 'IExpr -> 'IFPExpr
    abstract member MkEToAE: 'IExpr -> 'IArrayExpr

    //up casts to expr
    //Can terms in Yices be used by default as Expr in Z3?
    //abstract member MkBEToE: 'IBoolExpr -> 'IExpr
    public static int MkBEToE(int x)
    {
        return x;
    }
    //abstract member MkBVEToE: 'IBitVecExpr -> 'IExpr
    public static int MkBVEToE(int x)
    {
        return x;
    }

    abstract member MkFPEToE: 'IFPExpr -> 'IExpr

    //abstract member MkAEToE: 'IArrayExpr -> 'IExpr
    public static int MkAEToE(int x)
    {
        return x;
    }

    //casts with nums
    //abstract member MkEToBVNum: 'IExpr -> 'IBitVecNum
    public static int MkEToBVNum(int x)
    {
        return x;
    }
    abstract member MkEToFPNum: 'IExpr -> 'IFPNum

    //abstract member MkBVNumToBVE: 'IBitVecNum -> 'IBitVecExpr
    public static int MkBVNumToBVE(int x)
    {
        return x;
    }

//Terms conversion check
    //down casts from expr
    //abstract member MkCheckEToBE: 'IExpr -> bool
    [DllImport("libyices.dll")]
    public static extern int yices_term_is_bool(int x);
    public static bool MkCheckEToBE (int x)
    {
        return yices_term_is_bool(x) == 1;
    }

    //abstract member MkCheckEToBVE: 'IExpr -> bool
    [DllImport("libyices.dll")]
    public static extern int yices_term_is_bitvector(int x);
    public static bool MkCheckEToBVE (int x)
    {
        return yices_term_is_bitvector(x) == 1;
    }
    //TO DO Implement FP Theory
    //abstract member MkCheckEToFPE: 'IExpr -> bool

    abstract member MkCheckEToAE: 'IExpr -> bool

    //down casts to nums
    //abstract member MkCheckBVEToBVNum: 'IBitVecExpr -> bool
    [DllImport("libyices.dll")]
    public static extern int yices_term_is_atomic(int x);\

    //TO DO Implement FP Theory
    //abstract member MkCheckFPEToFPNum: 'IFPExpr -> bool

    //abstract member MkCheckEToBVNum: 'IExpr -> bool
    public static bool MkCheckEToBVNum (int x)
    {
        if (yices_term_is_bitvector(x) == 0) return false;
        return yices_term_is_atomic(x) == 1;
    }
    //TO DO Implement FP Theory
    //abstract member MkCheckEToFPNum: 'IExpr -> bool

    abstract member MkCheckEToINum: 'IExpr -> bool
    abstract member MkCheckEToRNum: 'IExpr -> bool


    //Common logic
    [DllImport("libyices.dll")]
    public static extern int yices_not(int x);//Arg must be a Boolean term
    [DllImport("libyices.dll")]
    public static extern int yices_and2(int x, int y);// MkAnd Args must be a Boolean term
    [DllImport("libyices.dll")]    // MkAndArray & MkAndSeq ??
    public static extern int yices_and(uint n, int[] a); //n is the number of arguments
    //arg must be an array of n Boolean terms
    [DllImport("libyices.dll")] // MkOr
    public static extern int yices_or2(int x, int y);// Args must be a Boolean term
    [DllImport("libyices.dll")] // MkXor
    public static extern int yices_xor(uint n, int[] a); //n is the number of arguments
    [DllImport("libyices.dll")]    // MkOrArray & MkOrSeq ??
    public static extern int yices_or(uint n, int[] a); //n is the number of arguments
    [DllImport("libyices.dll")] // MkEq
    public static extern int yices_eq(int x, int y);// Args must be a Boolean terms
    [DllImport("libyices.dll")] // MkITE
    public static extern int yices_ite(int c, int x, int y);// c must be a Boolean terms, x & y must be a compatible terms

    //BitVec logic
    [DllImport("libyices.dll")] // MkBVAnd
    public static extern int yices_bvand2(int x,int y);
    [DllImport("libyices.dll")] // MkBVOr
    public static extern int yices_bvor2(int x, int y);
    [DllImport("libyices.dll")] // MkBVXor
    public static extern int yices_bvxor2(int x, int y);
    [DllImport("libyices.dll")] // MkBVNot
    public static extern int yices_bvnot(int x);
    [DllImport("libyices.dll")] // MkBVULT
    public static extern int yices_bvlt_atom(int x, int y);
    [DllImport("libyices.dll")] // MkBVULE
    public static extern int yices_bvle_atom(int x, int y);
    [DllImport("libyices.dll")] // MkBVUGT
    public static extern int yices_bvgt_atom(int x, int y);
    [DllImport("libyices.dll")] // MkBVUGE
    public static extern int yices_bvge_atom(int x, int y);
    [DllImport("libyices.dll")] // MkBVSLT
    public static extern int yices_bvslt_atom(int x, int y);
    [DllImport("libyices.dll")] // MkBVSLE
    public static extern int yices_bvsle_atom(int x, int y);
    [DllImport("libyices.dll")] // MkBVSGT
    public static extern int yices_bvsgt_atom(int x, int y);
    [DllImport("libyices.dll")] // MkBVSGE
    public static extern int yices_bvsge_atom(int x, int y);

    //BitVec shifts
    // Need to check equivalence of bvshl in Z3 and Yices
    [DllImport("libyices.dll")]
    public static extern int yices_bvshl(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvashr(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvlshr(int x, int y);

    //BitVec conversions
    [DllImport("libyices.dll")]
    public static extern int yices_bvneg(int x);
    [DllImport("libyices.dll")]
    public static extern int yices_sign_extend(int x, uint y);
    [DllImport("libyices.dll")]
    public static extern int yices_zero_extend(int x, uint y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvextract(int x, uint y, uint z);
    [DllImport("libyices.dll")]
    public static extern int yices_bvconcat2(int x, int y); // const in yices function

    //BitVec arithmetics
    [DllImport("libyices.dll")]
    public static extern int yices_bvadd(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvsub(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvmul(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvdiv(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvsdiv(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvrem(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvsrem(int x, int y);

    //BitVec arithmetics without overflow/underflow
    //Yices doesn't support it by default. Is approach write custom checks in C good?
    abstract member MkBVAddNoUnderflow: 'IExpr * 'IExpr -> 'IBoolExpr
    abstract member MkBVAddNoOverflow: 'IExpr * 'IExpr * bool-> 'IBoolExpr
    abstract member MkBVMulNoUnderflow: 'IExpr * 'IExpr -> 'IBoolExpr
    abstract member MkBVMulNoOverflow: 'IExpr * 'IExpr * bool-> 'IBoolExpr

    //FP Logic
    //TO DO Implement FP Theory
    //abstract member MkFPEq: 'IFPExpr * 'IFPExpr -> 'IBoolExpr
    //abstract member MkFPLT: 'IExpr * 'IExpr -> 'IBoolExpr
    //abstract member MkFPLEq: 'IExpr * 'IExpr -> 'IBoolExpr
    //abstract member MkFPGT: 'IExpr * 'IExpr -> 'IBoolExpr
    //abstract member MkFPGEq: 'IExpr * 'IExpr -> 'IBoolExpr

    //FP arithmetics
    //TO DO Implement FP Theory
    //abstract member MkFPAdd: 'IExpr * 'IExpr * 'IExpr -> 'IExpr
    //abstract member MkFPMul: 'IExpr * 'IExpr * 'IExpr -> 'IExpr
    //abstract member MkFPSub: 'IExpr * 'IExpr * 'IExpr -> 'IExpr
    //abstract member MkFPDiv: 'IExpr * 'IExpr * 'IExpr -> 'IExpr
    //abstract member MkFPRem: 'IExpr * 'IExpr -> 'IExpr
    //abstract member MkFPNeg: 'IExpr -> 'IExpr

//Expression methods
    //Common methods
    //properties
    //abstract member GetSort: 'IExpr -> 'ISort
    [DllImport("libyices.dll")]
    public static extern int yices_type_of_term(int x);

    //abstract member GetExprType: 'IExpr -> Type

    //Didn't find toString in API, exists pretty printing, is possible to use for our purposes?
    //4700+ in yices.h
    abstract member String: 'IExpr -> string

    //Need to research exact functionality of this function in Z3
    //abstract member GetArgs: 'IExpr -> 'IExpr array
    [DllImport("libyices.dll")]
    public static extern int yices_term_child(int t, int i);
    [DllImport("libyices.dll")]
    public static extern int yices_term_num_child(int t);

    public static int[] GetArgs(int t)
    {
        int n = yices_term_num_child(t);
        int[] comp = new int[n];
        //if (n == 0) throw error?
        for (int i = 0; i < n; i++)
            comp[i] = yices_term_child(t, i);
        return comp;
    }
    //Check
    abstract member IsConst: 'IExpr -> bool
    abstract member IsConstantArray: 'IExpr -> bool
    abstract member IsDefaultArray: 'IExpr -> bool
    abstract member IsStore: 'IExpr -> bool

    //How did we realise it in Z3?
    abstract member IsQuantifier: 'IExpr -> bool
    //abstract member IsApp: 'IExpr -> bool
    public static bool IsApp(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_APP_TERM;
    }

    //abstract member IsTrue: 'IExpr -> bool
    public static bool IsTrue(int x)
    {
        return x == yices_true();
    }

    //abstract member IsFalse: 'IExpr -> bool
    public static bool IsFalse(int x)
    {
        return x == yices_false();
    }

    //abstract member IsNot: 'IExpr -> bool
    public static bool IsNot(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_NOT_TERM;
    }

    abstract member IsAnd: 'IExpr -> bool

    //abstract member IsOr: 'IExpr -> bool
    [DllImport("libyices.dll")]
    public static extern int yices_term_constructor(int x);
    public static bool IsOr(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_OR_TERM;
    }

    //abstract member IsEq: 'IExpr -> bool
    public static bool IsEq(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_EQ_TERM;
    }

    //abstract member IsBVSGT: 'IExpr -> bool
    public static bool IsBVSGT(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_NOT_TERM; //x > y <=> ! y >= x
    }
    //abstract member IsBVUGT: 'IExpr -> bool
    public static bool IsBVUGT(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_NOT_TERM; //x > y <=> ! y >= x
    }

    //abstract member IsBVSGE: 'IExpr -> bool
    public static bool IsBVSGE(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_BV_SGE_ATOM;
    }

    //abstract member IsBVUGE: 'IExpr -> bool
    public static bool IsBVUGE(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_BV_GE_ATOM;
    }

    //abstract member IsBVSLT: 'IExpr -> bool
    public static bool IsBVSLT(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_NOT_TERM; //x < y <=> ! y <= x
    }

    //abstract member IsBVULT: 'IExpr -> bool
    public static bool IsBVULT(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_NOT_TERM; //x < y <=> ! y <= x
    }

    //abstract member IsBVSLE: 'IExpr -> bool
    public static bool IsBVSLE(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_BV_SGE_ATOM; // x <= y <=> y >= x
    }

    //abstract member IsBVULE: 'IExpr -> bool
    public static bool IsBVULE(int x)
    {
        int temp = yices_term_constructor(x);
        return temp == (int) term_constructor_t.YICES_BV_GE_ATOM; // x <= y <=> y >= x
    }

    /* TO DO implement FP Theory
    abstract member IsFPGT: 'IExpr -> bool
    abstract member IsFPGE: 'IExpr -> bool
    abstract member IsFPLT: 'IExpr -> bool
    abstract member IsFPLE: 'IExpr -> bool
    */

    //BitVecNum properties
    abstract member Int64: 'IBitVecNum -> Int64
    //Exists function that give value as array of int bits
    abstract member Int: 'IBitVecNum -> int
    abstract member BigInteger: 'IBitVecNum -> BigInteger
    //abstract member SortSize: 'IBitVecExpr -> uint
    [DllImport("libyices.dll")]
    public static extern uint yices_term_bitsize(int t);
    public static uint SortSize(int t)
    {
        return yices_term_bitsize(t);
    }

    //TO DO FP Properties
    //abstract member FPEBits: 'IFPNum -> uint32
    //abstract member IsNaN: 'IFPNum -> bool
    //abstract member IsFPPlusInfinity: 'IFPNum -> bool
    //abstract member IsFPMinusInfinity: 'IFPNum -> bool
    //abstract member ExponentInt64: 'IFPNum -> int64
    //abstract member SignificandUInt64: 'IFPNum -> uint64
    //abstract member Sign: 'IFPNum -> bool

    //IntNum properties
    abstract member GetIntFromIntNum: 'IExpr -> int
    //RatNum properties
    abstract member GetValueFromRatNum: 'IExpr -> double
    //Quantifier properties
    abstract member GetQuantifierBody: 'IExpr -> 'IExpr

    //Solver methods
    abstract member MkSModel: 'ISolver -> 'IModel
    abstract member CheckSat: 'ISolver * 'IExpr array -> IStatus
    abstract member Assert: 'ISolver * [<ParamArray>] x : 'IBoolExpr array  -> unit
    abstract member GetReasonUnknown: 'ISolver -> string

    //Model methods
    abstract member Eval: 'IModel * 'IExpr * bool -> 'IExpr
    [DllImport("libyices.dll")]
    //https://github.com/SRI-CSL/yices2/blob/master/src/context/context_types.h#L726
    public static extern void yices_get_model(context_t ctx, int keep_subst);
    [DllImport("libyices.dll")]
    public static extern void yices_init();
    [DllImport("libyices.dll")]
    public static extern void yices_exit();
    public static void Main(string[] args)
    {
        yices_init();
    }
}
