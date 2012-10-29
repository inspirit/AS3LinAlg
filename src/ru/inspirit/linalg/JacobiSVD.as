package ru.inspirit.linalg 
{
	import apparat.asm.*;
	import apparat.math.FastMath;
	import apparat.math.IntMath;
	
	/**
	 * ...
	 * @author Eugene Zatepyakin
	 */
	public final class JacobiSVD 
	{	
        // cache sys to avoid new Vector creation
		protected const MAX_MN:int = 33;
		
		protected const _W:Vector.<Number> = new Vector.<Number>(MAX_MN);
		protected const _U:Vector.<Number> = new Vector.<Number>(__cint(MAX_MN * MAX_MN));
		protected const _V:Vector.<Number> = new Vector.<Number>(__cint(MAX_MN * MAX_MN));
		
		protected const _W2:Vector.<Number> = new Vector.<Number>(MAX_MN);
		protected const _U2:Vector.<Number> = new Vector.<Number>(__cint(MAX_MN * MAX_MN));
		protected const _V2:Vector.<Number> = new Vector.<Number>(__cint(MAX_MN * MAX_MN));
		
		public function JacobiSVD() { }
		
        // resize temp cache buffers
		public function relocateTempBuffer(m:int, n:int):void
		{
			var mn:int = IntMath.max(m, n);
			if (mn > _W.length)
			{
				_W.length = _W2.length = mn;
				_U.length = _U2.length = _V.length = _V2.length = mn * mn;
			}
		}
		
		public function decompose(A:Vector.<Number>, m:int, n:int, 
							W:Vector.<Number>, U:Vector.<Number>, V:Vector.<Number>,
							computeUV:Boolean = true, transposeV:Boolean = false, transposeU:Boolean = false):void
		{
			var at:Boolean = false;
			var compute_uv:Boolean = computeUV;
			var full_uv:Boolean = computeUV;
			var i:int, j:int;
			var pa:int, pat:int, ati:int, a:int;
			var mi:int = m, ni:int = n;
			var mn:int = IntMath.max(m, n);
			
			if (null != U)
			{
				full_uv = ((m != n && (U.length >= __cint(mn*mn))) ? true : false);
			} else if (null != V)
			{
				full_uv = ((m != n && (V.length >= __cint(mn * mn))) ? true : false);
			}
			
			if (m < n)
			{
				mi = n;
				ni = m;
				at = true;
			}
			
			var urows:int = full_uv ? mi : ni;
			var temp_a:Vector.<Number> = _U2;//new Vector.<Number>(__cint(urows*mi), true);
			var temp_w:Vector.<Number> = _W2;//new Vector.<Number>(urows, true);
			var temp_v:Vector.<Number> = null;
			
			if (compute_uv)
			{
				temp_v = _V2;//new Vector.<Number>(__cint(ni * ni), true);
			}
			
			if ( !at )
			{
				// transpose
				for (i = 0, ati = 0, a = 0; i < m;)
				{
					pat = ati;
					pa = a;
					for (j = 0; j < n;)
					{
						temp_a[pat] = A[pa];
						__asm( IncLocalInt( j ), IncLocalInt( pa ) );
						pat = __cint( pat + m );
					}
					__asm( IncLocalInt( i ), IncLocalInt( ati ) );
					a = __cint( a + n );
				}
			}
			else
			{
				j = __cint(m * n);
				for (i = 0; i < j; ++i)
				{
					temp_a[i] = A[i];
				}
			}
			
			var astep:int = mi;
			var vstep:int = ni;
			run(temp_a, temp_w, temp_v, astep, vstep, mi, ni, compute_uv ? urows : 0);
			
			if(null!=W)
			{
				for (i = 0; i < ni; ++i)
				{
					W[i] = temp_w[i];
				}
			}
			
			if ( compute_uv )
			{
				if ( !at )
				{
					if(transposeU && null!=U)
					{
						j = __cint(urows * mi);
						for (i = 0; i < j; ++i)
						{
							U[i] = temp_a[i];
						}
					}
					else if(null!=U)
					{
						// transpose
						for (i = 0, ati = 0, a = 0; i < urows;)
						{
							pat = ati;
							pa = a;
							for (j = 0; j < mi;)
							{
								U[pat] = temp_a[pa];
								__asm( IncLocalInt( j ), IncLocalInt( pa ) );
								pat = __cint( pat + urows );
							}
							__asm( IncLocalInt( i ), IncLocalInt( ati ) );
							a = __cint( a + mi );
						}
					}
					if (transposeV && null!=V)
					{
						j = __cint(ni * ni);
						for (i = 0; i < j; ++i)
						{
							V[i] = temp_v[i];
						}
					}
					else if(null!=V)
					{
						for (i = 0, ati = 0, a = 0; i < ni;)
						{
							pat = ati;
							pa = a;
							for (j = 0; j < ni;)
							{
								V[pat] = temp_v[pa];
								__asm( IncLocalInt( j ), IncLocalInt( pa ) );
								pat = __cint( pat + ni );
							}
							__asm( IncLocalInt( i ), IncLocalInt( ati ) );
							a = __cint( a + ni );
						}
					}
				}
				else 
				{
					if(transposeU && null!=U)
					{
						j = __cint(ni * ni);
						for (i = 0; i < j; ++i)
						{
							U[i] = temp_v[i];
						}
					}
					else if(null!=U)
					{
						// transpose
						for (i = 0, ati = 0, a = 0; i < ni;)
						{
							pat = ati;
							pa = a;
							for (j = 0; j < ni;)
							{
								U[pat] = temp_v[pa];
								__asm( IncLocalInt( j ), IncLocalInt( pa ) );
								pat = __cint( pat + ni );
							}
							__asm( IncLocalInt( i ), IncLocalInt( ati ) );
							a = __cint( a + ni );
						}
					}
					if (transposeV && null!=V)
					{
						j = __cint(urows * mi);
						for (i = 0; i < j; ++i)
						{
							V[i] = temp_a[i];
						}
					}
					else if(null!=V)
					{
						for (i = 0, ati = 0, a = 0; i < urows;)
						{
							pat = ati;
							pa = a;
							for (j = 0; j <  mi;)
							{
								V[pat] = temp_a[pa];
								__asm( IncLocalInt( j ), IncLocalInt( pa ) );
								pat = __cint( pat + urows );
							}
							__asm( IncLocalInt( i ), IncLocalInt( ati ) );
							a = __cint( a +  mi );
						}
					}
				}
			}
		}
		
		public function pseudoInverse(inv:Vector.<Number>, mtx:Vector.<Number>, m:int, n:int):void
		{
			var i:int,j:int,k:int;
			var pu:int, pv:int, pa:int;
			var DBL_EPSILON:Number = 2.2204460492503131E-16;
			var dum:Number;
			var mn:int = IntMath.max(m, n);
			
			var W:Vector.<Number> = _W;//new Vector.<Number>(mn, true);
			var U:Vector.<Number> = _U;//new Vector.<Number>(__cint(mn * mn), true);
			var V:Vector.<Number> = _V;//new Vector.<Number>(__cint(mn * mn), true);
			
			decompose(mtx, m, n, W, U, V, true, false);
			
			var tolerance:Number = DBL_EPSILON * W[0] * n;
			
			for ( i = 0, pv = 0, pa = 0; i < n; ++i)
			{ 
				for ( j = 0, pu = 0; j < m; ++j, ++pa)
				{
					for (k = 0, dum = 0.0; k < n; ++k, ++pu)
					{
						var wk:Number = W[k];
						if (wk > tolerance) 
						{
							dum += V[__cint(pv + k)] * U[pu] / wk;
						}
					}
					inv[pa] = dum;
				}
				pv = __cint(pv + n);
			}
		}
		
		public function solve(A:Vector.<Number>, m:int, n:int, x:Vector.<Number>, B:Vector.<Number>):void
		{
			var i:int,j:int,k:int;
			var pu:int, pv:int;
			var DBL_EPSILON:Number = 2.2204460492503131E-16;
			var dum:Number, dum2:Number;
			
			var mn:int = IntMath.max(m, n);
			
			var W:Vector.<Number> = _W;//new Vector.<Number>(mn, true);
			var U:Vector.<Number> = _U;//new Vector.<Number>(__cint(mn * mn), true);
			var V:Vector.<Number> = _V;//new Vector.<Number>(__cint(mn * mn), true);
            
			decompose(A, m, n, W, U, V, true, false);
			
			var tolerance:Number = DBL_EPSILON * W[0] * n;
			
			for ( i = 0, pv = 0; i < n; ++i)
			{
				dum2 = 0.0;
				for (j = 0; j < n; ++j)
				{
					var wj:Number = Number(W[j]);
					if (wj > tolerance ) 
					{
						for (k = 0, dum = 0.0, pu = 0; k < m; ++k)
						{
							dum += Number(U[(__cint(pu + j))]) * Number(B[k]);
							pu = __cint(pu + n);
						}
						dum2 += dum * Number(V[(__cint(pv + j))]) / wj;
					}
				}
				x[i] = dum2;
				pv = __cint(pv + n);
			} 
		}
		
		protected function run(At:Vector.<Number>, W:Vector.<Number>, Vt:Vector.<Number>, 
								astep:int, vstep:int, m:int, n:int, n1:int):void
		{
			var eps:Number = 2.2204460492503131E-16;
			var i:int, j:int, k:int, iter:int, ii:int;
			var max_iter:int = IntMath.max(m, 30);
			var c:Number, s:Number, sd:Number;
			
			eps *= 10.0;
			
			var mm2:int = __cint((m - 4) + 1);
			var nm2:int = __cint((n - 4) + 1);
			
			var math:*;
			__asm(__as3(Math), SetLocal(math));
			
			for( i = 0; i < n; ++i )
			{
				ii = __cint(i*astep);
				for( k = 0, s = 0.0; k < m; )
				{
					var t:Number = At[ii];
					s += t*t;
					__asm(IncLocalInt(k),IncLocalInt(ii));
				}
				W[i] = s;
				
				if( null != Vt )
				{
					ii = __cint(i * vstep);
					for ( k = 0; k < n; ++k )
					{
						Vt[__cint(ii + k)] = 0.0;
					}
					Vt[__cint(ii + i)] = 1.0;
				}
			}
			
			var _ati:Number;
			var _atj:Number;
			var t0:Number;
			var t1:Number;
			
			var nm1:int = __cint(n - 1);
			for( iter = 0; iter < max_iter; ++iter )
			{
				var changed:Boolean = false;				
				
				for ( i = 0; i < nm1; ++i )
				{
					j = __cint(i + 1);
					for( ; j < n; ++j )
					{
						//_Tp *Ai = At + i*astep, *Aj = At + j*astep, a = W[i], p = 0, b = W[j];
						var Ai:int = __cint(i * astep);
						var Aj:int = __cint(j * astep);
						var a:Number = W[i];
						var p:Number = 0.0;
						var b:Number = W[j];
						
						k = 0;
						if(m >= 4)
						{
							for ( ; k < mm2; )
							{
								p += (At[__cint(Ai+k)]) * (At[__cint(Aj+k)]);
								__asm(IncLocalInt(k));
								p += (At[__cint(Ai+k)]) * (At[__cint(Aj+k)]);
								__asm(IncLocalInt(k));
								p += (At[__cint(Ai+k)]) * (At[__cint(Aj+k)]);
								__asm(IncLocalInt(k));
								p += (At[__cint(Ai+k)]) * (At[__cint(Aj+k)]);
								__asm(IncLocalInt(k));
							}
						}
						for ( ; k < m; )
						{
							p += (At[__cint(Ai+k)]) * (At[__cint(Aj+k)]);
							__asm(IncLocalInt(k));
						}
						
						__asm(__as3(math), __as3(a * b), CallProperty(__as3(Math.sqrt), 1), SetLocal(t));
						if ( FastMath.abs(p) <= eps * t )
						{
							continue;
						}
						
						p *= 2.0;
						var beta:Number = a - b;
						var gamma:Number = 0.0;
						var delta:Number;
						
						//hypot(p, beta);
						var ap:Number = FastMath.abs(p);
						var abeta:Number = FastMath.abs(beta);
						if( ap > abeta )
						{
							abeta /= ap;
							__asm(__as3(math), __as3(1.0 + abeta*abeta), CallProperty(__as3(Math.sqrt), 1), SetLocal(t));
							gamma = ap * t;
						} 
						else if( abeta > 0.0 )
						{
							ap /= abeta;
							__asm(__as3(math), __as3(1.0 + ap*ap), CallProperty(__as3(Math.sqrt), 1), SetLocal(t));
							gamma = abeta * t;
						}
						//
						
						if( beta < 0.0 )
						{
							delta = (gamma - beta) * 0.5;
							//s = std::sqrt(delta/gamma);
							__asm(__as3(math), __as3(delta/gamma), CallProperty(__as3(Math.sqrt), 1), SetLocal(s));
							c = (p/(gamma*s*2));
						}
						else
						{
							//c = std::sqrt((gamma + beta)/(gamma*2));
							__asm(__as3(math), __as3((gamma + beta)/(gamma*2)), CallProperty(__as3(Math.sqrt), 1), SetLocal(c));
							s = (p/(gamma*c*2));
							delta = (p*p*0.5/(gamma + beta));
						}
						
						if( iter & 1 )
						{
							W[i] = ((W[i]) + delta);
							W[j] = ((W[j]) - delta);
							
							//k = vblas.givens(Ai, Aj, m, c, s);
							
							k = 0;
							if(m >= 4)
							{
								for ( ; k < mm2; )
								{
									_ati = (At[__cint(Ai + k)]);
									_atj = (At[__cint(Aj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									At[__cint(Ai + k)] = t0; 
									At[__cint(Aj + k)] = t1;
									__asm(IncLocalInt(k));
									//
									_ati = (At[__cint(Ai + k)]);
									_atj = (At[__cint(Aj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									At[__cint(Ai + k)] = t0; 
									At[__cint(Aj + k)] = t1;
									__asm(IncLocalInt(k));
									//
									_ati = (At[__cint(Ai + k)]);
									_atj = (At[__cint(Aj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									At[__cint(Ai + k)] = t0; 
									At[__cint(Aj + k)] = t1;
									__asm(IncLocalInt(k));
									//
									_ati = (At[__cint(Ai + k)]);
									_atj = (At[__cint(Aj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									At[__cint(Ai + k)] = t0; 
									At[__cint(Aj + k)] = t1;
									__asm(IncLocalInt(k));
									//
								}
							}
							for ( ; k < m; )
							{
								_ati = (At[__cint(Ai + k)]);
								_atj = (At[__cint(Aj + k)]);
								t0 = c*_ati + s*_atj;
								t1 = -s*_ati + c*_atj;
								At[__cint(Ai + k)] = t0; 
								At[__cint(Aj + k)] = t1;
								__asm(IncLocalInt(k));
							}
						}
						else
						{
							a = b = 0;
							//k = vblas.givensx(Ai, Aj, m, c, s, &a, &b);
							k = 0;
							if(m >= 4)
							{
								for ( ; k < mm2; )
								{
									_ati = (At[__cint(Ai + k)]);
									_atj = (At[__cint(Aj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									At[__cint(Ai + k)] = t0; 
									At[__cint(Aj + k)] = t1;
									
									a += t0*t0; b += t1*t1;
									__asm(IncLocalInt(k));
									//
									_ati = (At[__cint(Ai + k)]);
									_atj = (At[__cint(Aj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									At[__cint(Ai + k)] = t0; 
									At[__cint(Aj + k)] = t1;
									
									a += t0*t0; b += t1*t1;
									__asm(IncLocalInt(k));
									//
									_ati = (At[__cint(Ai + k)]);
									_atj = (At[__cint(Aj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									At[__cint(Ai + k)] = t0; 
									At[__cint(Aj + k)] = t1;
									
									a += t0*t0; b += t1*t1;
									__asm(IncLocalInt(k));
									//
									_ati = (At[__cint(Ai + k)]);
									_atj = (At[__cint(Aj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									At[__cint(Ai + k)] = t0; 
									At[__cint(Aj + k)] = t1;
									
									a += t0*t0; b += t1*t1;
									__asm(IncLocalInt(k));
									//
								}
							}
							for ( ; k < m; )
							{
								_ati = (At[__cint(Ai + k)]);
								_atj = (At[__cint(Aj + k)]);
								t0 = c*_ati + s*_atj;
								t1 = -s*_ati + c*_atj;
								At[__cint(Ai + k)] = t0; 
								At[__cint(Aj + k)] = t1;
								
								a += t0*t0; b += t1*t1;
								__asm(IncLocalInt(k));
							}
							W[i] = a; W[j] = b;
						}
						
						changed = true;
						
						if( null != Vt )
						{
							//_Tp *Vi = Vt + i*vstep, *Vj = Vt + j*vstep;
							var Vi:int = __cint(i * vstep);
							var Vj:int = __cint(j * vstep);
							//k = vblas.givens(Vi, Vj, n, c, s);
							
							k = 0;
							if(n >= 4)
							{
								for( ; k < nm2; )
								{
									_ati = (Vt[__cint(Vi + k)]);
									_atj = (Vt[__cint(Vj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									Vt[__cint(Vi + k)] = t0;
									Vt[__cint(Vj + k)] = t1;
									__asm(IncLocalInt(k));
									//
									_ati = Number(Vt[__cint(Vi + k)]);
									_atj = Number(Vt[__cint(Vj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									Vt[__cint(Vi + k)] = t0;
									Vt[__cint(Vj + k)] = t1;
									__asm(IncLocalInt(k));
									//
									_ati = (Vt[__cint(Vi + k)]);
									_atj = (Vt[__cint(Vj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									Vt[__cint(Vi + k)] = t0;
									Vt[__cint(Vj + k)] = t1;
									__asm(IncLocalInt(k));
									//
									_ati = (Vt[__cint(Vi + k)]);
									_atj = (Vt[__cint(Vj + k)]);
									t0 = c*_ati + s*_atj;
									t1 = -s*_ati + c*_atj;
									Vt[__cint(Vi + k)] = t0;
									Vt[__cint(Vj + k)] = t1;
									__asm(IncLocalInt(k));
									//
								}
							}
							for( ; k < n; )
							{
								_ati = (Vt[__cint(Vi + k)]);
								_atj = (Vt[__cint(Vj + k)]);
								t0 = c*_ati + s*_atj;
								t1 = -s*_ati + c*_atj;
								Vt[__cint(Vi + k)] = t0;
								Vt[__cint(Vj + k)] = t1;
								__asm(IncLocalInt(k));
							}
						}
					}
				}
				if( !changed ) break;
			}
			
			for( i = 0; i < n; ++i )
			{
				ii = __cint(i * astep);
				for( k = 0, sd = 0.0; k < m; )
				{
					t = (At[ii]);
					sd += t*t;
					__asm(IncLocalInt(k),IncLocalInt(ii));
				}
				__asm(__as3(math), __as3(sd), CallProperty(__as3(Math.sqrt), 1), SetLocal(s));
				W[i] = s;
			}
			
			// sort
			
			for( i = 0; i < nm1; ++i )
			{
				j = i;
				k = __cint(i + 1);
				for( ; k < n; ++k )
				{
					if( W[j] < W[k] ) j = k;
				}
				if( i != j )
				{
					t = (W[i]);
					W[i] = (W[j]);
					W[j] = t;
					
					if( null != Vt )
					{
						Ai = __cint(i*astep);
						Aj = __cint(j*astep);
						
						k = 0;
						if(m >= 4)
						{
							for ( ; k < mm2; )
							{
								t = (At[__cint(Ai + k)]);
								At[__cint(Ai + k)] = (At[__cint(Aj + k)]);
								At[__cint(Aj + k)] = t;
								__asm(IncLocalInt(k));
								//
								t = (At[__cint(Ai + k)]);
								At[__cint(Ai + k)] = (At[__cint(Aj + k)]);
								At[__cint(Aj + k)] = t;
								__asm(IncLocalInt(k));
								//
								t = (At[__cint(Ai + k)]);
								At[__cint(Ai + k)] = (At[__cint(Aj + k)]);
								At[__cint(Aj + k)] = t;
								__asm(IncLocalInt(k));
								//
								t = (At[__cint(Ai + k)]);
								At[__cint(Ai + k)] = (At[__cint(Aj + k)]);
								At[__cint(Aj + k)] = t;
								__asm(IncLocalInt(k));
								//
							}
						}
						for ( ; k < m; )
						{
							t = (At[__cint(Ai + k)]);
							At[__cint(Ai + k)] = (At[__cint(Aj + k)]);
							At[__cint(Aj + k)] = t;
							__asm(IncLocalInt(k));
						}
						
						Ai = __cint(i*vstep);
						Aj = __cint(j*vstep);
						
						k = 0;
						if(n >= 4)
						{
							for ( ; k < nm2; )
							{
								t = (Vt[__cint(Ai + k)]);
								Vt[__cint(Ai + k)] = (Vt[__cint(Aj + k)]);
								Vt[__cint(Aj + k)] = t;
								__asm(IncLocalInt(k));
								//
								t = (Vt[__cint(Ai + k)]);
								Vt[__cint(Ai + k)] = (Vt[__cint(Aj + k)]);
								Vt[__cint(Aj + k)] = t;
								__asm(IncLocalInt(k));
								//
								t = (Vt[__cint(Ai + k)]);
								Vt[__cint(Ai + k)] = (Vt[__cint(Aj + k)]);
								Vt[__cint(Aj + k)] = t;
								__asm(IncLocalInt(k));
								//
								t = (Vt[__cint(Ai + k)]);
								Vt[__cint(Ai + k)] = (Vt[__cint(Aj + k)]);
								Vt[__cint(Aj + k)] = t;
								__asm(IncLocalInt(k));
								//
							}
						}
						for ( ; k < n; )
						{
							t = (Vt[__cint(Ai + k)]);
							Vt[__cint(Ai + k)] = (Vt[__cint(Aj + k)]);
							Vt[__cint(Aj + k)] = t;
							__asm(IncLocalInt(k));
						}
					}
				}
			}
			
			if( null == Vt ) return;
			
			var _seed:int = __cint( ((m*n)&255) << 16 | ((n1 + m)&255) << 8 | iter );
			var rnd:int;
			for( i = 0; i < n1; ++i )
			{
				//s = i < n ? Number(W[i]) : 0.0;
				s = Number(i < n) * (W[i]);
				Ai = __cint(i * astep);
				while( s == 0.0 )
				{
					// if we got a zero singular value, then in order to get the corresponding left singular vector
					// we generate a random vector, project it to the previously computed left singular vectors,
					// subtract the projection and normalize the difference.
					const val0:Number = 1.0 / Number(m);
					for( k = 0; k < m; ++k )
					{
						_seed = __cint(_seed * 214013 + 2531011);
						rnd = ((_seed >> 16) & 0x7fff) & 256;
						var val:Number = rnd ? val0 : -val0;
						At[__cint(Ai + k)] = val;
					}
					for( iter = 0; iter < 2; ++iter )
					{
						for( j = 0; j < i; ++j )
						{
							sd = 0.0;
							Aj = __cint(j * astep);
							for ( k = 0; k < m; ++k )
							{
								sd += (At[__cint(Ai + k)]) * (At[__cint(Aj + k)]);
							}
							var asum:Number = 0;
							for( k = 0; k < m; ++k )
							{
								t = (At[__cint(Ai + k)]) - sd * (At[__cint(Aj + k)]);
								At[__cint(Ai + k)] = t;
								asum += FastMath.abs(t);
							}
							if(asum)
							{
								asum = 1.0 / asum;
								for ( k = 0; k < m; ++k )
								{
									At[__cint(Ai + k)] *= asum;
								}
							} else {
								for ( k = 0; k < m; ++k )
								{
									At[__cint(Ai + k)] = 0.0;
								}
							}
						}
					}
					sd = 0.0;
					for( k = 0; k < m; ++k )
					{
						t = (At[__cint(Ai + k)]);
						sd += t*t;
					}
					//s = std::sqrt(sd);
					__asm(__as3(math), __as3(sd), CallProperty(__as3(Math.sqrt), 1), SetLocal(s));
				}
				
				s = 1.0 / s;
				for ( k = 0; k < m; ++k )
				{
					At[__cint(Ai + k)] *= s;
				}
			}
		}
		
	}

}