package ru.inspirit.linalg
{
	import apparat.asm.DecLocalInt;
	import apparat.asm.IncLocalInt;
	import apparat.asm.__asm;
	import apparat.asm.__cint;
	import apparat.math.FastMath;
	/**
	 * @author Eugene Zatepyakin
	 */
	public final class LU
	{
        // temp cache buffers to avoid new Vector creation with each run
		protected const MAX_MN:int = 36;
		protected const TEMP_LU:Vector.<Number> = new Vector.<Number>(MAX_MN*MAX_MN);
		protected const TEMP_PV:Vector.<int> = new Vector.<int>(MAX_MN);
        
        // resize temp cache buffers
		public function relocateTempBuffer(size:int):void
		{
			if (size > TEMP_PV.length)
			{				
				TEMP_PV.length = size;
                TEMP_LU.length = size * size;
			}
		}
		
		public function decompose(A:Vector.<Number>, n:int, lu:Vector.<Number>, pivot:Vector.<int>):Boolean
		{
			var i:int, j:int, k:int, l:int;
			var p_k:int, p_row:int, p_col:int;
			var max:Number, max2:Number;
			
			i = __cint(n * n);
			while (i > 0)
			{
				__asm(DecLocalInt(i));
				lu[i] = A[i];
			}
			
			var pv:Vector.<int> = pivot;
			
			for(k = 0, p_k = 0; k < n; )
			{
				// find pivot
				pv[k] = k;
				max = FastMath.abs((lu[__cint(p_k+k)]));
				j = __cint(k + 1);
				p_row = __cint(p_k + n);
				for (; j < n; )
				{
					max2 = FastMath.abs((lu[__cint(p_row + k)]));
					if ( max < max2 )
					{
						max = max2;
						pv[k] = j;
						p_col = p_row;
					}
					//
					__asm(IncLocalInt(j));
					p_row = __cint(p_row + n);
				}
				//
				// and if the pivot row differs from the current row, then
				// interchange the two rows.
				if (pv[k] != k)
				{
					i = p_k;
					l = p_col;
					for (j = 0; j < n; )
					{
						
						max = lu[i];
						lu[i] = lu[l];
						lu[l] = max;
						__asm(IncLocalInt(i), IncLocalInt(l), IncLocalInt(j));
					}
				}
				// and if the matrix is singular, return error
				if ( (lu[__cint(p_k+k)]) == 0.0 ) return false;
				
				// otherwise find the lower triangular matrix elements for column k
				i = __cint(k+1);
				p_row = __cint(p_k + n);
				max = 1.0 / (lu[__cint(p_k + k)]);
				for (; i < n; )
				{
					lu[__cint(p_row + k)] *= max;
					//
					__asm(IncLocalInt(i));
					p_row = __cint(p_row + n);
				}
				
				// update remaining matrix
				i = __cint(k+1);
				p_row = __cint(p_k + n);
				for (; i < n; )
				{
					j = __cint(k+1);
					max = lu[__cint(p_row + k)];
					for (; j < n; )
					{
						lu[__cint(p_row + j)] -= max * lu[__cint(p_k + j)];
						__asm(IncLocalInt(j));
					}
					//
					__asm(IncLocalInt(i));
					p_row = __cint(p_row + n);
				}
				//
				__asm(IncLocalInt(k));
				p_k = __cint(p_k + n);
			}
			
			return true;
		}
		
		public function solve(A:Vector.<Number>, n:int, x:Vector.<Number>, B:Vector.<Number>):Boolean
		{
			var i:int, k:int, p_k:int;
			var dum:Number;
			
			var lu:Vector.<Number> = TEMP_LU;
			var pv:Vector.<int> = TEMP_PV;
			
			if( !decompose(A, n, lu, pv) ) return false;
			
			// Solve the linear equation Lx = B for x, where L is a lower
			// triangular matrix with an implied 1 along the diagonal
			for (k = 0, p_k = 0; k < n; )
			{
				if (pv[k] != k)
				{
					dum = (B[k]);
					i = (pv[k]);
					B[k] = (B[i]);
					B[i] = dum;
				}
				dum = B[k];
				for (i = 0; i < k; ) 
				{
					dum -= x[i] * lu[__cint(p_k + i)];
					__asm(IncLocalInt(i));
				}
				x[k] = dum;
				//
				__asm(IncLocalInt(k));
				p_k = __cint(p_k + n);
			}
			
			// Solve the linear equation Ux = y, where y is the solution
			// obtained above of Lx = B and U is an upper triangular matrix
			
			k = __cint(n-1);
			p_k = __cint(n*(n-1));
			for (; k >= 0; )
			{
				if (pv[k] != k)
				{
					dum = (B[k]);
					i = (pv[k]);
					B[k] = (B[i]);
					B[i] = dum;
				}
				i = __cint(k + 1);
				dum = x[k];
				for (; i < n; )
				{
					dum -= x[i] * (lu[__cint(p_k + i)]);
					__asm(IncLocalInt(i));
				}
				var dum2:Number = (lu[__cint(p_k + k)]);
				if (dum2 == 0.0) return false;
				x[k] = dum / dum2;
				//
				__asm(DecLocalInt(k));
				p_k = __cint(p_k - n);
			}
			
			return true;
		}
		
		public function inverse(inv:Vector.<Number>, A:Vector.<Number>, n:int):Boolean
		{
            // use identity 
			var b:Vector.<Number> = TEMP_LU;
			var i:int, j:int, k:int;
			
			k = 0;
			for(i = 0; i < n; ++i)
			{
				for(j = 0; j < n; ++j)
				{
					b[k] = Number(i == j);
					__asm(IncLocalInt(k));
				}
			}
			
			return solve(A, n, inv, b);
		}
        
        // A and b modified inplace without new buffer creation
        public function solve_inplace(A:Vector.<Number>, m:int, b:Vector.<Number>):Boolean
        {
            var i:int, j:int, k:int, p:int = 1;
            var t:Number;
            const DBL_EPSILON:Number = 2.2204460492503131E-16;
            var im:int;
            
            for( i = 0; i < m; ++i )
            {
                k = i;
                im = __cint(i * m);
                
                for( j = __cint(i+1); j < m; ++j )
                    if( FastMath.abs(A[__cint(j*m + i)]) > FastMath.abs(A[__cint(k*m + i)]) )
                        k = j;
                
                if( FastMath.abs(A[__cint(k*m + i)]) < DBL_EPSILON ) return false;
                
                if( k != i )
                {
                    for ( j = i; j < m; ++j )
                    {
                        t = A[__cint(im + j)];
                        A[__cint(im + j)] = A[__cint(k * m + j)];
                        A[__cint(k * m + j)] = t;
                    }
                    
                    t = b[i];
                    b[i] = b[k];
                    b[k] = t;
                    
                    p = -p;
                }
                
                var d:Number = -1.0/A[__cint(im + i)];
                
                for( j = __cint(i+1); j < m; ++j )
                {
                    var alpha:Number = A[__cint(j*m + i)]*d;
                    
                    for( k = __cint(i+1); k < m; ++k )
                        A[__cint(j*m + k)] += alpha*A[__cint(im + k)];
                    
                    b[j] += alpha*b[i];
                }
                
                A[__cint(im + i)] = -d;
            }
            
            for( i = __cint(m-1); i >= 0; --i )
            {
                var s:Number = b[i];
                im = __cint(i * m);
                for ( k = __cint(i + 1); k < m; ++k )
                {
                    s -= A[__cint(im + k)] * b[k];
                }
                b[i] = s*A[__cint(im + i)];
            }
            
            return true;
        }
	}
}
