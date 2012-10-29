package ru.inspirit.linalg
{
    import apparat.asm.__cint;

    public final class Cholesky
    {
        public function Cholesky()
        {
            //
        }
        
        // decomposing A inplace and solving for b also inplace => result vector stored in b
        public final function solve(A:Vector.<Number>, size:int, b:Vector.<Number>):Boolean
        {
            var col:int, row:int, col2:int;
            var val:Number;

            for (col = 0; col < size; ++col)
            {
                var inv_diag:Number = 1;
                var cs:int = __cint(col * size);
                var rs:int = cs;
                for (row = col; row < size; ++row)
                {
                    // correct for the parts of cholesky already computed
                    val = A[__cint(rs+col)];
                    for (col2 = 0; col2 < col; ++col2)
                    {
                        val -= A[__cint(col2*size+col)] * A[__cint(rs+col2)];
                    }
                    if (row == col)
                    {
                        // this is the diagonal element so don't divide
                        A[__cint(rs+col)] = val;
                        if(val == 0){
                            return false;
                        }
                        inv_diag = 1.0 / val;
                    } else {
                        // cache the value without division in the upper half
                        A[__cint(cs+row)] = val;
                        // divide my the diagonal element for all others
                        A[__cint(rs+col)] = val * inv_diag;
                    }
                    rs = __cint(rs + size);
                }
            }

            // first backsub through L
            var i:int, j:int;
            cs = 0;
            for (i = 0; i < size; ++i)
            {
                val = b[i];
                for (j = 0; j < i; ++j)
                {
                    val -= A[__cint(cs+j)] * b[j];
                }
                b[i] = val;
                cs = __cint(cs + size);
            }
            // backsub through diagonal
            cs = 0;
            for (i = 0; i < size; ++i)
            {
                b[i] /= A[__cint(cs + i)];
                cs = __cint(cs + size);
            }
            // backsub through L Transpose
            i = __cint(size-1);
            for (; i >= 0; --i)
            {
                val = b[i];
                j = __cint(i + 1);
                cs = __cint(j * size);
                for (; j < size; ++j)
                {
                    val -= A[__cint(cs + i)] * b[j];
                    cs = __cint(cs + size);
                }
                b[i] = val;
            }

            return true;
        }
    }
}
