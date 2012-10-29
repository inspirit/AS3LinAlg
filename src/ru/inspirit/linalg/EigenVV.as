package ru.inspirit.linalg
{
	import apparat.asm.*;
	import apparat.math.FastMath;
	/**
	 * 
	 * Find the eigenvalues and eigenvectors of a symmetric n x n matrix A 
	 * using the Jacobi method. Upon return, the input matrix A will have been modified.
	 * 
	 * @author Eugene Zatepyakin
	 */
	public final class EigenVV
	{
        // cache
        protected const CACHE_SIZE:int = 33;
        protected var _w:Vector.<Number> = new Vector.<Number>(CACHE_SIZE);
        protected var _indR:Vector.<int> = new Vector.<int>(CACHE_SIZE);
        protected var _indC:Vector.<int> = new Vector.<int>(CACHE_SIZE);
        
        // resize temp cache buffers
		public function relocateTempBuffer(size:int):void
		{
			if (size > _w.length)
			{				
				_w.length = size;
                _indR.length = size;
                _indC.length = size;
			}
		}
        
        public function compute(A:Vector.<Number>, size:int, vectors:Vector.<Number>, values:Vector.<Number>):void
        {
            // this to be computed even if user dont ask for it
            var w:Vector.<Number> = _w;
            jacobi(A, size, w, vectors, size, size);
            if (values)
            {
                for (var i:int = 0; i < size; ++i)
                {
                    values[i] = w[i];
                }
            }
        }
        
        public function jacobi(A:Vector.<Number>, astep:int, W:Vector.<Number>, V:Vector.<Number>, vstep:int, n:int):void
        {
            const DBL_EPSILON:Number = 2.2204460492503131E-16;
            var i:int, j:int, k:int, m:int;
            var _in:int, _in2:int;
            
            if( V )
            {
                for( i = 0; i < n; ++i )
                {
                    _in = __cint(i*vstep);
                    for( j = 0; j < n; ++j ) V[__cint(_in + j)] = 0;
                    V[__cint(_in + i)] = 1;
                }
            }
            
            var iters:int;
            var maxIters:int = __cint(n * n * 30);
            var indR:Vector.<int> = _indR;
            var indC:Vector.<int> = _indC;
            var mv:Number = 0;
            var val:Number;
            
            for( k = 0; k < n; ++k )
            {
                W[k] = A[__cint((astep + 1)*k)];
                if( k < __cint(n - 1) )
                {
                    m = __cint(k + 1);
                    mv = FastMath.abs(A[__cint(astep * k + m)]);
                    i = __cint(k + 2);
                    for( ; i < n; ++i )
                    {
                        val = FastMath.abs(A[__cint(astep*k+i)]);
                        if( mv < val )
                            mv = val, m = i;
                    }
                    indR[k] = m;
                }
                if( k > 0 )
                {
                    m = 0;
                    mv = FastMath.abs(A[k]);
                    i = 1;
                    for( ; i < k; ++i )
                    {
                        val = FastMath.abs(A[__cint(astep*i+k)]);
                        if( mv < val )
                            mv = val, m = i;
                    }
                    indC[k] = m;
                }
            }
            
            var l:int;
            var p:Number;
            
            if( n > 1 ) for( iters = 0; iters < maxIters; ++iters )
            {
                // find index (k,l) of pivot p
                for( k = 0, mv = FastMath.abs(A[indR[0]]), i = 1; i < __cint(n-1); ++i )
                {
                    val = FastMath.abs(A[__cint(astep*i + indR[i])]);
                    if( mv < val )
                        mv = val, k = i;
                }
                l = indR[k];
                for( i = 1; i < n; ++i )
                {
                    val = FastMath.abs(A[__cint(astep*indC[i] + i)]);
                    if( mv < val )
                        mv = val, k = indC[i], l = i;
                }
                
                p = A[__cint(astep * k + l)];
                if ( FastMath.abs(p) <= DBL_EPSILON ) break;
                
                var y:Number = (W[l] - W[k])*0.5;
                var t:Number = FastMath.abs(y);
                // hypot(p, y)
                var ap:Number = FastMath.abs(p);
                var ap0:Number = ap; // cache
                var ay:Number = t;
                if (ap > ay)
                {
                    ay /= ap;
                    t += ap * Math.sqrt(1.0 + ay * ay);
                } else if (ay > 0)
                {
                    ap /= ay;
                    t += ay * Math.sqrt(1.0 + ap*ap);
                }
                //
                var s:Number = 0;// hypot(p, t);
                //
                ap = ap0;
                ay = FastMath.abs(t);
                if (ap > ay)
                {
                    ay /= ap;
                    s = ap * Math.sqrt(1.0 + ay * ay);
                } else if (ay > 0)
                {
                    ap /= ay;
                    s = ay * Math.sqrt(1.0 + ap*ap);
                }
                //
                var c:Number = t/s;
                s = p/s; t = (p/t)*p;
                if( y < 0 )
                    s = -s, t = -t;
                A[__cint(astep*k + l)] = 0;
                
                W[k] -= t;
                W[l] += t;
                
                var a0:Number, b0:Number;
                
                // rotate rows and columns k and l
                for ( i = 0; i < k; ++i )
                {
                    _in = __cint(astep * i + k);
                    _in2 = __cint(astep * i + l);
                    a0 = A[_in];
                    b0 = A[_in2];
                    A[_in] = a0 * c - b0 * s;
                    A[_in2] = a0 * s + b0 * c;
                }
                for ( i = __cint(k + 1); i < l; ++i )
                {
                    _in = __cint(astep * k + i);
                    _in2 = __cint(astep * i + l);
                    a0 = A[_in];
                    b0 = A[_in2];
                    A[_in] = a0 * c - b0 * s;
                    A[_in2] = a0 * s + b0 * c;
                }
                for ( i = __cint(l + 1); i < n; ++i )
                {
                    _in = __cint(astep * k + i);
                    _in2 = __cint(astep * l + i);
                    a0 = A[_in];
                    b0 = A[_in2];
                    A[_in] = a0 * c - b0 * s;
                    A[_in2] = a0 * s + b0 * c;
                }
                
                // rotate eigenvectors
                if ( V )
                {
                    for ( i = 0; i < n; ++i )
                    {
                        _in = __cint(vstep * k + i);
                        _in2 = __cint(vstep * l + i);
                        a0 = V[_in];
                        b0 = V[_in2];
                        V[_in] = a0 * c - b0 * s;
                        V[_in2] = a0 * s + b0 * c;
                    }
                }
                
                for( j = 0; j < 2; ++j )
                {
                    var idx:int = j == 0 ? k : l;
                    if( idx < __cint(n - 1) )
                    {
                        for( m = __cint(idx+1), mv = FastMath.abs(A[__cint(astep*idx + m)]), i = __cint(idx+2); i < n; ++i )
                        {
                            val = FastMath.abs(A[__cint(astep*idx+i)]);
                            if( mv < val )
                                mv = val, m = i;
                        }
                        indR[idx] = m;
                    }
                    if( idx > 0 )
                    {
                        for( m = 0, mv = FastMath.abs(A[idx]), i = 1; i < idx; ++i )
                        {
                            val = FastMath.abs(A[__cint(astep*i+idx)]);
                            if( mv < val )
                                mv = val, m = i;
                        }
                        indC[idx] = m;
                    }
                }
            }
            
            // sort eigenvalues & eigenvectors
            for( k = 0; k < __cint(n-1); ++k )
            {
                m = k;
                for( i = __cint(k+1); i < n; ++i )
                {
                    if( W[m] < W[i] )
                        m = i;
                }
                if( k != m )
                {
                    mv = W[m];
                    W[m] = W[k];
                    W[k] = mv;
                    if ( V )
                    {
                        for ( i = 0; i < n; ++i )
                        {
                            _in = __cint(vstep * m + i);
                            _in2 = __cint(vstep * k + i);
                            mv = V[_in];
                            V[_in] = V[_in2];
                            V[_in2] = mv;
                        }
                    }
                }
            }
        }
	}
}
