/*using System;
using System.Runtime.InteropServices;

public class Yices
{
    [DllImport("libyices.dll")]
    public static extern int yices_true();
    [DllImport("libyices.dll")]
    public static extern int yices_false();
    // Need to grasp function yices_constant
    abstract member MkConst: string * 'ISort -> 'IExpr
    abstract member MkConstDecl: string * 'ISort -> 'IFuncDecl
    abstract member MkNumeral: string * 'ISort -> 'IExpr
    abstract member MkNumeral: uint * 'ISort -> 'IExpr
    abstract member MkNumeral: int * 'ISort -> 'IExpr
    abstract member MkFPNumeral: float32 * 'ISort -> 'IExpr
    abstract member MkFPDoubleNumeral: float * 'ISort -> 'IExpr
    abstract member MkFPRoundNearestTiesToEven: unit -> 'IExpr

//Creating sorts
    abstract member MkBoolSort: unit -> 'ISort
    abstract member MkBitVecSort: uint -> 'ISort
    abstract member MkFPSort32: unit -> 'ISort
    abstract member MkFPSort64: unit -> 'ISort
    abstract member MkArraySort: 'ISort * 'ISort -> 'ISort
    abstract member MkRangeArraySort: 'ISort array * 'ISort -> 'ISort
    abstract member BoolSort: unit -> 'ISort

//Creating terms
    abstract member MkBV: uint32 * uint32 -> 'IBitVecExpr
    abstract member MkBVInt: int * uint32 -> 'IBitVecExpr
    abstract member MkBool: bool -> 'IBoolExpr
    abstract member MkFPToFP: 'IExpr * 'IFPExpr * 'ISort -> 'IFPExpr
    abstract member MkFPToFP: 'IExpr * 'IBitVecExpr * 'ISort * bool -> 'IFPExpr
    abstract member MkApp: 'IFuncDecl * [<ParamArray>] parameters : 'IExpr array -> 'IExpr
    abstract member MkFuncDecl: string * 'ISort array * 'ISort -> 'IFuncDecl
    abstract member MkFP: 'IBitVecExpr * 'IBitVecExpr * 'IBitVecExpr -> 'IFPExpr
//Array operations
    abstract member MkSelect: 'IArrayExpr * 'IExpr -> 'IExpr
    abstract member MkRangeSelect: 'IArrayExpr * 'IExpr array -> 'IExpr

//Solver operations
    abstract member MkSolver: uint option -> 'ISolver

//Terms conversion
    //FP to BV and vice versa
    abstract member MkFPToIEEEBV: 'IFPExpr -> 'IBitVecExpr
    abstract member MkFPToBV: 'IExpr * 'IFPExpr * uint * bool -> 'IBitVecExpr
    //down casts from expr
    abstract member MkEToBE: 'IExpr -> 'IBoolExpr
    abstract member MkEToBVE: 'IExpr -> 'IBitVecExpr
    abstract member MkEToFPE: 'IExpr -> 'IFPExpr
    abstract member MkEToAE: 'IExpr -> 'IArrayExpr
    //up casts to expr
    abstract member MkBEToE: 'IBoolExpr -> 'IExpr
    abstract member MkBVEToE: 'IBitVecExpr -> 'IExpr
    abstract member MkFPEToE: 'IFPExpr -> 'IExpr
    abstract member MkAEToE: 'IArrayExpr -> 'IExpr
    //casts with nums
    abstract member MkEToBVNum: 'IExpr -> 'IBitVecNum
    abstract member MkEToFPNum: 'IExpr -> 'IFPNum
    abstract member MkBVNumToBVE: 'IBitVecNum -> 'IBitVecExpr

//Terms conversion check
    //down casts from expr
    abstract member MkCheckEToBE: 'IExpr -> bool
    abstract member MkCheckEToBVE: 'IExpr -> bool
    abstract member MkCheckEToFPE: 'IExpr -> bool
    abstract member MkCheckEToAE: 'IExpr -> bool
    //down casts to nums
    abstract member MkCheckBVEToBVNum: 'IBitVecExpr -> bool
    abstract member MkCheckFPEToFPNum: 'IFPExpr -> bool
    abstract member MkCheckEToBVNum: 'IExpr -> bool
    abstract member MkCheckEToFPNum: 'IExpr -> bool
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
    public static extern int yices_bvconcat2(int x, const int y); // const in yices function

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
    //Doesn't Yices support it?
    abstract member MkBVAddNoUnderflow: 'IExpr * 'IExpr -> 'IBoolExpr
    abstract member MkBVAddNoOverflow: 'IExpr * 'IExpr * bool-> 'IBoolExpr
    abstract member MkBVMulNoUnderflow: 'IExpr * 'IExpr -> 'IBoolExpr
    abstract member MkBVMulNoOverflow: 'IExpr * 'IExpr * bool-> 'IBoolExpr

    //FP Logic
    //Doesn't support
    abstract member MkFPEq: 'IFPExpr * 'IFPExpr -> 'IBoolExpr
    abstract member MkFPLT: 'IExpr * 'IExpr -> 'IBoolExpr
    abstract member MkFPLEq: 'IExpr * 'IExpr -> 'IBoolExpr
    abstract member MkFPGT: 'IExpr * 'IExpr -> 'IBoolExpr
    abstract member MkFPGEq: 'IExpr * 'IExpr -> 'IBoolExpr

    //FP arithmetics
    //Doesn't support
    abstract member MkFPAdd: 'IExpr * 'IExpr * 'IExpr -> 'IExpr
    abstract member MkFPMul: 'IExpr * 'IExpr * 'IExpr -> 'IExpr
    abstract member MkFPSub: 'IExpr * 'IExpr * 'IExpr -> 'IExpr
    abstract member MkFPDiv: 'IExpr * 'IExpr * 'IExpr -> 'IExpr
    abstract member MkFPRem: 'IExpr * 'IExpr -> 'IExpr
    abstract member MkFPNeg: 'IExpr -> 'IExpr

//Expression methods
    //Common methods
    //properties
    //There is support for the required functions for each type separately, write a mapper?
    abstract member GetSort: 'IExpr -> 'ISort
    abstract member GetExprType: 'IExpr -> Type
    //Didn't find toString in API
    abstract member String: 'IExpr -> string
    //Need to research exact functionality of this function in Z3
    abstract member GetArgs: 'IExpr -> 'IExpr array
    //Check
    abstract member IsConst: 'IExpr -> bool
    abstract member IsConstantArray: 'IExpr -> bool
    abstract member IsDefaultArray: 'IExpr -> bool
    abstract member IsStore: 'IExpr -> bool
    abstract member IsQuantifier: 'IExpr -> bool
    abstract member IsApp: 'IExpr -> bool
    abstract member IsTrue: 'IExpr -> bool
    abstract member IsFalse: 'IExpr -> bool
    abstract member IsNot: 'IExpr -> bool
    abstract member IsAnd: 'IExpr -> bool
    abstract member IsOr: 'IExpr -> bool
    abstract member IsEq: 'IExpr -> bool
    abstract member IsBVSGT: 'IExpr -> bool
    abstract member IsBVUGT: 'IExpr -> bool
    abstract member IsBVSGE: 'IExpr -> bool
    abstract member IsBVUGE: 'IExpr -> bool
    abstract member IsBVSLT: 'IExpr -> bool
    abstract member IsBVULT: 'IExpr -> bool
    abstract member IsBVSLE: 'IExpr -> bool
    abstract member IsBVULE: 'IExpr -> bool
    abstract member IsFPGT: 'IExpr -> bool
    abstract member IsFPGE: 'IExpr -> bool
    abstract member IsFPLT: 'IExpr -> bool
    abstract member IsFPLE: 'IExpr -> bool

    //BitVecNum properties
    abstract member Int64: 'IBitVecNum -> int64
    abstract member Int: 'IBitVecNum -> int
    abstract member BigInteger: 'IBitVecNum -> BigInteger
    abstract member SortSize: 'IBitVecExpr -> uint
    //FP Properties
    abstract member FPEBits: 'IFPNum -> uint32
    abstract member IsNaN: 'IFPNum -> bool
    abstract member IsFPPlusInfinity: 'IFPNum -> bool
    abstract member IsFPMinusInfinity: 'IFPNum -> bool
    abstract member ExponentInt64: 'IFPNum -> int64
    abstract member SignificandUInt64: 'IFPNum -> uint64
    abstract member Sign: 'IFPNum -> bool
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
*/
