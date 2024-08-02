using System;
using System.Numerics;
using System.Runtime.InteropServices;
using System.Runtime.InteropServices.JavaScript;
using Math.Gmp.Native;

//using VSharp.ISolver;
public class Yices
{
    enum term_constructor_t
    {
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
    //What is const of given sort?
    public static int MkConst(string s, int typ)
    {
        int t = yices_new_uninterpreted_term(typ);
        int flag = yices_set_type_name(t, s);
        return t;
    }

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

    //Common logic
    [DllImport("libyices.dll")]
    public static extern int yices_not(int x);//Arg must be a Boolean term

    public static int MkNot(int x)
    {
        return yices_not(x);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_and2(int x, int y);// MkAnd Args must be a Boolean term

    public static int MkAnd(int x, int y)
    {
        return yices_and2(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_and(uint n, int[] a); //n is the number of arguments

    public static int MkAndArray(params int[] x)
    {
        return yices_and((uint)x.Length, x);
    }

    public static int MkAndSeq(IEnumerable<int> x)
    {
        return yices_and((uint)Enumerable.Count(x), Enumerable.ToArray(x));
    }

    //arg must be an array of n Boolean terms
    [DllImport("libyices.dll")] // MkOr
    public static extern int yices_or2(int x, int y);// Args must be a Boolean term

    public static int MkOr(int x, int y)
    {
        return yices_or2(x, y);
    }

    [DllImport("libyices.dll")] // MkXor
    public static extern int yices_xor(uint n, int[] a); //n is the number of arguments

    public static int MkXor(IEnumerable<int> x)
    {
        return yices_xor((uint) Enumerable.Count(x), Enumerable.ToArray(x));
    }

    [DllImport("libyices.dll")]    // MkOrArray & MkOrSeq ??
    public static extern int yices_or(uint n, int[] a); //n is the number of arguments
    public static int MkOrArray(params int[] x)
    {
        return yices_or((uint)x.Length, x);
    }

    public static int MkOrSeq(IEnumerable<int> x)
    {
        return yices_or((uint)Enumerable.Count(x), Enumerable.ToArray(x));
    }

    [DllImport("libyices.dll")] // MkEq
    public static extern int yices_eq(int x, int y);// Args must be a Boolean terms

    public static int MkEq(int x, int y)
    {
        return yices_eq(x, y);
    }

    [DllImport("libyices.dll")] // MkITE
    public static extern int yices_ite(int c, int x, int y);// c must be a Boolean terms, x & y must be a compatible terms

    public static int MkITE(int c, int x, int y)
    {
        return yices_ite(c, x, y);
    }

    //BitVec logic
    [DllImport("libyices.dll")] // MkBVAnd
    public static extern int yices_bvand2(int x,int y);

    public static int MkBVAnd(int x, int y)
    {
        return yices_bvand2(x, y);
    }

    [DllImport("libyices.dll")] // MkBVOr
    public static extern int yices_bvor2(int x, int y);

    public static int MkBVOr(int x, int y)
    {
        return yices_bvor2(x, y);
    }

    [DllImport("libyices.dll")] // MkBVXor
    public static extern int yices_bvxor2(int x, int y);

    public static int MkBVXor(int x, int y)
    {
        return yices_bvxor2(x, y);
    }

    [DllImport("libyices.dll")] // MkBVNot
    public static extern int yices_bvnot(int x);

    public static int MkBVNot(int x)
    {
        return yices_bvnot(x);
    }

    [DllImport("libyices.dll")] // MkBVULT
    public static extern int yices_bvlt_atom(int x, int y);

    public static int MkBVULT(int x, int y)
    {
        return yices_bvlt_atom(x, y);
    }

    [DllImport("libyices.dll")] // MkBVULE
    public static extern int yices_bvle_atom(int x, int y);

    public static int MkBVULE(int x, int y)
    {
        return yices_bvle_atom(x, y);
    }

    [DllImport("libyices.dll")] // MkBVUGT
    public static extern int yices_bvgt_atom(int x, int y);

    public static int MkBVUGT(int x, int y)
    {
        return yices_bvgt_atom(x, y);
    }

    [DllImport("libyices.dll")] // MkBVUGE
    public static extern int yices_bvge_atom(int x, int y);

    public static int MkBVUGE(int x, int y)
    {
        return yices_bvge_atom(x, y);
    }

    [DllImport("libyices.dll")] // MkBVSLT
    public static extern int yices_bvslt_atom(int x, int y);

    public static int MkBVSLT(int x, int y)
    {
        return yices_bvslt_atom(x, y);
    }

    [DllImport("libyices.dll")] // MkBVSLE
    public static extern int yices_bvsle_atom(int x, int y);

    public static int MkBVSLE(int x, int y)
    {
        return yices_bvsle_atom(x, y);
    }

    [DllImport("libyices.dll")] // MkBVSGT
    public static extern int yices_bvsgt_atom(int x, int y);

    public static int MkBVSGT(int x, int y)
    {
        return yices_bvsgt_atom(x, y);
    }

    [DllImport("libyices.dll")] // MkBVSGE
    public static extern int yices_bvsge_atom(int x, int y);

    public static int MkBVSGE(int x, int y)
    {
        return yices_bvsge_atom(x, y);
    }

    //BitVec shifts
    // Need to check equivalence of bvshl in Z3 and Yices
    [DllImport("libyices.dll")]
    public static extern int yices_bvshl(int x, int y);

    public static int MkBVSHL(int x, int y)
    {
        return yices_bvshl(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvashr(int x, int y);

    public static int MkBVASHR(int x, int y)
    {
        return yices_bvashr(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvlshr(int x, int y);

    public static int MkBVLSHR(int x, int y)
    {
        return yices_bvlshr(x, y);
    }

    //BitVec conversions
    [DllImport("libyices.dll")]
    public static extern int yices_bvneg(int x);

    public static int MkBVNeg(int x)
    {
        return yices_bvneg(x);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_sign_extend(int x, uint y);

    public static int MkSignExtend(uint y, int x)
    {
        return yices_sign_extend(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_zero_extend(int x, uint y);

    public static int MkZeroExtend(uint y, int x)
    {
        return yices_zero_extend(x, y)
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvextract(int x, uint y, uint z);

    public static int MkExtract(uint y, uint z, int x)
    {
        return yices_bvextract(x,  y, z);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvconcat2(int x, int y);

    public static int MkConcat(int x, int y)
    {
        return yices_bvconcat2(x, y);
    }

    //BitVec arithmetics
    [DllImport("libyices.dll")]
    public static extern int yices_bvadd(int x, int y);

    public static int MkBVAdd(int x, int y)
    {
        return yices_bvadd(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvsub(int x, int y);

    public static int MkBVSub(int x, int y)
    {
        return yices_bvsub(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvmul(int x, int y);

    public static int MkBVMul(int x, int y)
    {
        return yices_bvmul(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvdiv(int x, int y);

    public static int MkBVUDiv(int x, int y)
    {
        return yices_bvdiv(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvsdiv(int x, int y);

    public static int MkBVSDiv(int x, int y)
    {
        return yices_bvsdiv(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvrem(int x, int y);

    public static int MkBVURem(int x, int y)
    {
        return yices_bvrem(x, y);
    }

    [DllImport("libyices.dll")]
    public static extern int yices_bvsrem(int x, int y);

    public static int MkBVSRem(int x, int y)
    {
        return yices_bvsrem(x, y);
    }

    //BitVec arithmetics without overflow/underflow
    //Yices doesn't support it by default. Is approach write custom checks in C good?
    //abstract member MkBVAddNoUnderflow: 'IExpr * 'IExpr -> 'IBoolExpr
    [DllImport("libyices.dll")]
    public static extern int yices_bvconst_zero(uint x);

    [DllImport("libyices.dll")]
    public static extern int yices_implies(int x, int y);
    public static int MkBVAddNoUnderflow(int l, int r)
    {
        /*
         * (bvadd no udf a b) ==>
         *    (=> (and (bvslt a 0) (bvslt b 0)) (bvslt (bvadd a b) 0))
         * */
        uint size = yices_term_bitsize(l);
        int zero = yices_bvconst_zero(size);
        int lSLTZero = yices_bvsle_atom(l, zero);
        int rSLTZero = yices_bvsle_atom(r, zero);
        int sum = yices_bvadd(l, r);
        int sumLTZero = yices_bvsle_atom(sum, zero);

        return yices_implies(yices_and2(lSLTZero, rSLTZero), sumLTZero);
    }

    //abstract member MkBVAddNoOverflow: 'IExpr * 'IExpr * bool-> 'IBoolExpr
    public static int MkBVAddNoOverflow(int l, int r, bool isSigned)
    {
        if (isSigned)
        {
            /*
             * (bvadd no ovf signed a b) ==>
             *    (=> (and (bvslt 0 a) (bvslt 0 b)) (bvslt 0 (bvadd a b)))
             * */
            uint size = yices_term_bitsize(l);
            int zero = yices_bvconst_zero(size);
            int zeroSLTl = yices_bvsle_atom(zero, l);
            int zeroSLTr = yices_bvsle_atom(zero, r);
            int sum = yices_bvadd(l, r);
            int zeroSLTsum = yices_bvsle_atom(zero, sum);

            return yices_implies(yices_and2(zeroSLTl, zeroSLTr), zeroSLTsum);
        }
        /*
         * (bvadd no ovf unsigned a b) ==>
         *    (= 0 (extract [highestBit] (bvadd (concat 0 a) (concat 0 b))))
         * */
        int extL = yices_zero_extend(l, 1);
        int extR = yices_zero_extend(r, 1);
        int sumU = yices_bvadd(extL, extR);
        uint highestBitIdx = yices_term_bitsize(sumU) - 1;
        int sumFirstBit = yices_bvextract(sumU, highestBitIdx, highestBitIdx);

        return yices_eq(sumFirstBit, yices_bvconst_zero(0));
    }

    //abstract member MkBVMulNoUnderflow: 'IExpr * 'IExpr -> 'IBoolExpr
    public static int MkBVMulNoUnderflow(int l, int r)
    {
        return MkBVSignedMulNoOverflow(l, r, false);
    }

   //abstract member MkBVMulNoOverflow: 'IExpr * 'IExpr * bool-> 'IBoolExpr
    [DllImport("libyices.dll")]
    public static extern int yices_bveq_atom(int x, int y);
    [DllImport("libyices.dll")]
    public static extern int yices_bvconst_one(uint x);

    public static int MkBVMulNoOverflow(int l, int r, bool isSigned)
    {
        if (isSigned) return MkBVSignedMulNoOverflow(l, r, true);
        return MkBVUnsignedMulNoOverflow(l, r);
    }

    public static int MkBVSignedMulNoOverflow(int l, int r, bool isOverflow)
    {
        uint size = yices_term_bitsize(l);
        uint signBitIdx = size - 1;
        int lSign = yices_bvextract(l, signBitIdx, signBitIdx);
        int rSign = yices_bvextract(r, signBitIdx, signBitIdx);
        int comp = yices_bveq_atom(lSign, rSign);

        int overflowSignCheck = (isOverflow) ? comp : yices_not(comp);

        int extL = yices_bvconcat2(lSign, l);
        int extR = yices_bvconcat2(rSign, r);
        int mulResult = yices_bvmul(extL, extR);

        int msb0 = yices_bvextract(mulResult, size, size);
        int msb1 = yices_bvextract(mulResult, size - 1, size - 1);
        int overflow1 = yices_bveq_atom(yices_bvconst_one(1), yices_bvxor2(msb0, msb1));

        int lSignBitSet = yices_bveq_atom(yices_bvconst_one(1), lSign);

        // Overflow is possible when sign bits are equal
        // lhsSign = 1, rhsSign = 0 -> false
        // lhsSign = 0, rhsSign = 1 -> false
        int overflow2 = isOverflow
            ? yices_ite(lSignBitSet,
                MkBVUnsignedMulBitOverflowCheck(yices_bvnot(l), yices_bvnot(r), size - 1),
                MkBVUnsignedMulBitOverflowCheck(l, r, size - 1))
            : yices_ite(lSignBitSet,
                MkBVUnsignedMulBitOverflowCheck(yices_bvnot(l), r, size - 1),
                MkBVUnsignedMulBitOverflowCheck(l, yices_bvnot(r), size - 1));
        int overflow = yices_or2(overflow1, overflow2);

        return yices_not(yices_and2(overflowSignCheck, overflow));
    }

    public static int MkBVUnsignedMulNoOverflow(int l, int r)
    {
        uint size = yices_term_bitsize(l);

        int extL = yices_zero_extend(l, 1);
        int extR = yices_zero_extend(r, 1);

        int mulResult = yices_bvmul(extL, extR);
        int overflowBit = yices_bvextract(mulResult, size, size);
        int overflow1 = yices_bveq_atom(yices_bvconst_one(1), overflowBit);

        int overflow2 = MkBVUnsignedMulBitOverflowCheck(l, r, size);

        return yices_not(yices_or2(overflow1, overflow2));
    }

    public static int MkBVUnsignedMulBitOverflowCheck(int l, int r, uint size)
    {
        int[] data = new int[size];
        //Is it possible to just use int as type of ovf?
        int ovf = yices_false();
        for (uint i = 1; i < size; i++)
        {
            uint lBitIdx = size - i;
            int lBit = yices_bvextract(l, lBitIdx, lBitIdx);

            uint rBitIdx = i;
            int rBit = yices_bvextract(r, rBitIdx, rBitIdx);

            int lBitValue = yices_bveq_atom(yices_bvconst_one(1), lBit);
            int rBitValue = yices_bveq_atom(yices_bvconst_one(1), rBit);

            ovf = yices_or2(ovf, lBitValue);
            data[i] = yices_and2(ovf, rBitValue);
        }
        return yices_or((uint) data.Length, data);
    }
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
    //Can we rewrite Encoding.fs to don't use it?
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
    //abstract member IsConst: 'IExpr -> bool
    public static bool IsConst(int x)
    {
        if (yices_term_is_atomic(x) == 0)
            return false;
        int temp = yices_term_constructor(x);
        if (temp == (int)term_constructor_t.YICES_VARIABLE || temp == (int)term_constructor_t.YICES_UNINTERPRETED_TERM)
            return false;
        return true;
    }

    abstract member IsConstantArray: 'IExpr -> bool
    abstract member IsDefaultArray: 'IExpr -> bool
    abstract member IsStore: 'IExpr -> bool

    //abstract member IsQuantifier: 'IExpr -> bool
    public static bool IsQuantifier(int x)
    {
        int temp = yices_term_constructor(x);
        if (temp == (int)term_constructor_t.YICES_FORALL_TERM)
            return true;
        if (temp == (int)term_constructor_t.YICES_NOT_TERM)
        {
            int n = yices_term_num_child(x);
            if (n != 1) return false;
            int comp = yices_term_child(x, 0);
            if (yices_term_constructor(comp) == (int)term_constructor_t.YICES_FORALL_TERM)
                return true;
        }
        return false;
    }

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
    //abstract member Int64: 'IBitVecNum -> Int64
    //gives value of n-bitvector as array of n int bits
    [DllImport("libyices.dll")]
    public static extern uint yices_bv_const_value(int t, int[] val);
    public static long Int64(int t)
    {
        long temp = 0;
        uint n = yices_term_bitsize(t);
        int[] val = new int[n];

        for (uint i = 0; i < n; i++)
            temp += val[i] << (int) i;

    }

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



    //Quantifier properties
    //abstract member GetQuantifierBody: 'IExpr -> 'IExpr
    public static int GetQuantifierBody(int x)
    {
        int temp = yices_term_constructor(x);
        if (temp == (int) term_constructor_t.YICES_FORALL_TERM)
            return yices_term_child(x, yices_term_num_child(x) - 1);
        //exist x : P <=> !forall x : !P
        if (temp == (int)term_constructor_t.YICES_NOT_TERM)
        {
            int inner_term = yices_term_child(x, 0);
            temp = yices_term_constructor(inner_term);
            if (temp == (int)term_constructor_t.YICES_FORALL_TERM)
                return yices_term_child(yices_term_child(inner_term, yices_term_num_child(inner_term) - 1), 0);
        }
        throw new ArgumentException("The term is not quantifier, cannot get body");
    }

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
