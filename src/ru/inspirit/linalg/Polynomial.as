package ru.inspirit.linalg 
{
	import apparat.asm.CallProperty;
	import apparat.asm.SetLocal;
	import apparat.asm.__as3;
	import apparat.asm.__asm;
	import apparat.asm.__cint;
	import apparat.math.FastMath;
	/**
	 * @author Eugene Zatepyakin
	 */
	public final class Polynomial
	{
		protected const MAX_SQRT:Number = Math.sqrt(Number.MAX_VALUE);
		protected const MAX_CUBE_ROOT:Number = Math.pow(Number.MAX_VALUE, 1.0/3.0);
		
		public function solveQuartic(a:Number, b:Number, c:Number, d:Number, result:Vector.<Number>):int
		{
			//const maxSqrt:Number = MAX_SQRT;
			//if (FastMath.abs(a) > maxSqrt)
			//{
				// very special case
				// do we need it?
			//}
			
			// Solve a cubic with a trivial root of 0
			if (d == 0)
			{
				var cubRes:Vector.<Number> = new Vector.<Number>(3, true);
				var n:int = solveCubic2(a, b, c, cubRes);
				result[0] = 0;
				result[1] = cubRes[0];
				result[2] = cubRes[1];
				result[3] = cubRes[2];
				return __cint(1 + n);
			}
			
			// We have a biquadratic
			if ((a == 0) && (c== 0))
			{
				var quadRes:Vector.<Number> = new Vector.<Number>(2, true);
				var quadRoot1:Number, quadRoot2:Number, tmp:Number;
				var math:*;
				__asm(__as3(Math), SetLocal(math));
				if (solveQuadratic(1, b, d, quadRes))
				{
					quadRoot1 = quadRes[0];
					quadRoot2 = quadRes[1];
					if (quadRoot1 < quadRoot2) 
					{
						tmp = quadRoot1;
						quadRoot1 = quadRoot2;
						quadRoot2 = tmp;
					}

					if (quadRoot1 < 0) return 0;
					
					__asm(__as3(math), __as3(quadRoot1), CallProperty(__as3(Math.sqrt), 1), SetLocal(quadRoot1));
					result[0] = quadRoot1;
					result[1] = -quadRoot1;

					if (quadRoot2 < 0) return 2;
					
					__asm(__as3(math), __as3(quadRoot2), CallProperty(__as3(Math.sqrt), 1), SetLocal(quadRoot2));
					//quadRoot2 = Math.sqrt(quadRoot2);
					result[2] = quadRoot2;
					result[3] = -quadRoot2;
					
					return 4;
				}
				else 
				{
					return 0;
				}
			}
			
			// Now we have to resort to some dodgy formulae!
			var k:int = 0;
			var nr:int;
			k = k + int(a < 0.0) * 2;
			k = k + int(b < 0.0);
			k = k + int(c < 0.0) * 8;
			k = k + int(d < 0.0) * 4;
			
			switch (k)
			{
				case 3 :
				case 9 : 
					nr = solveQuarticFerrari(a,b,c,d,result); 
					break;
				case 5 :
					nr = solveQuarticDescartes(a,b,c,d,result); 
					break;
				case 15 :
					//This algorithm is stable if we flip the sign of the roots
					nr = solveQuarticDescartes(-a,b,-c,d,result);
					result[0] *= -1; result[1] *= -1; result[2] *= -1; result[3] *= -1;
					break;
				default:
					nr = solveQuarticNeumark(a,b,c,d,result); 
					//nr = ferrariQuarticSolve(a,b,c,d,result); 
					//nr = yacfraidQuarticSolve(a,b,c,d,result); 
				break;
			}
			
			return nr;
		}
		
		public function solveQuarticNeumark(a:Number, b:Number, c:Number, d:Number, result:Vector.<Number>):int
		{
			var rts:Vector.<Number> = new Vector.<Number>(4, true);
			var worst3:Vector.<Number> = new Vector.<Number>(3, true);
			var v1:Vector.<Number> = new Vector.<Number>(4, true);
			var v2:Vector.<Number> = new Vector.<Number>(4, true);
			var v3:Vector.<Number> = new Vector.<Number>(4, true);
			var qrts:Vector.<Number> = new Vector.<Number>(12, true);  // quartic roots for each cubic root
			var y:Number,g:Number,gg:Number,h:Number,hh:Number,gdis:Number,gdisrt:Number;
			var hdis:Number,hdisrt:Number,g1:Number,g2:Number,h1:Number,h2:Number;
			var bmy:Number,gerr:Number,herr:Number,y4:Number,bmysq:Number;
			var hmax:Number,gmax:Number;
			
			// Solve a cubic with a trivial root of 0
			if (d == 0)
			{
				var cubRes:Vector.<Number> = new Vector.<Number>(3, true);
				var n:int = solveCubic2(a, b, c, cubRes);
				result[0] = 0;
				result[1] = cubRes[0];
				result[2] = cubRes[1];
				result[3] = cubRes[2];
				return __cint(1 + n);
			}
			
			var asq:Number = a * a;

			var d4:Number = d * 4.0;
			var p:Number =  -b * 2.0;
			var q:Number = b * b + a * c - d4;
			var r:Number = (c - a*b)*c + asq*d;
			var cubicRoots:int = solveCubic2(p,q,r, v3);

			var nQuarticRoots:Vector.<int> = new Vector.<int>(3, true); 
			
			var math:*;
			__asm(__as3(Math), SetLocal(math));
			
			for (var j3:int = 0; j3 < cubicRoots; ++j3)
			{
				y = v3[j3];    
				bmy = b - y;
				y4 = y * 4.0;
				bmysq = bmy*bmy;
				gdis = asq - y4;
				hdis = bmysq - d4;

				if ((gdis < 0.0) || (hdis < 0.0))
				{
					nQuarticRoots[j3] = 0;
				}
				else
				{
					g1 = a * 0.5;
					h1 = bmy* 0.5;
					gerr = asq + y4;
					herr = hdis;
					
					if (d > 0.0) herr = bmysq + d4;
					
					if ((y < 0.0) || (herr*gdis > gerr*hdis))
					{
						__asm(__as3(math), __as3(gdis), CallProperty(__as3(Math.sqrt), 1), SetLocal(gdisrt));
						//gdisrt = Math.sqrt(gdis);
						g2 = gdisrt*0.5;
						if (gdisrt != 0.0)
						{
							h2 = (a*h1 - c)/gdisrt;
						} else
						{
							h2 = 0.0;
						}
					}
					else
					{
						__asm(__as3(math), __as3(hdis), CallProperty(__as3(Math.sqrt), 1), SetLocal(hdisrt));
						//hdisrt = Math.sqrt(hdis);
						h2 = hdisrt*0.5;
						if (hdisrt != 0.0)
						{
							g2 = (a*h1 - c)/hdisrt;
						} else 
						{
							g2 = 0.0;
						}
					}
					/*
					note that in the following, the tests ensure non-zero
					denominators -
					*/
					h = h1 - h2;
					hh = h1 + h2;
					hmax = hh;
					if (hmax < 0.0) hmax =  -hmax;
					if (hmax < h) hmax = h;
					if (hmax <  -h) hmax =  -h;
					if ((h1 > 0.0)&&(h2 > 0.0)) h = d/hh;
					if ((h1 < 0.0)&&(h2 < 0.0)) h = d/hh;
					if ((h1 > 0.0)&&(h2 < 0.0)) hh = d/h;
					if ((h1 < 0.0)&&(h2 > 0.0)) hh = d/h;
					if (h > hmax) h = hmax;
					if (h <  -hmax) h =  -hmax;
					if (hh > hmax) hh = hmax;
					if (hh < -hmax) hh =  -hmax;

					g = g1 - g2;
					gg = g1 + g2;
					gmax = gg;
					if (gmax < 0.0) gmax = -gmax;
					if (gmax < g) gmax = g;
					if (gmax < -g) gmax = -g;
					if ((g1 > 0.0)&&(g2 > 0.0)) g = y/gg;
					if ((g1 < 0.0)&&(g2 < 0.0)) g = y/gg;
					if ((g1 > 0.0)&&(g2 < 0.0)) gg = y/g;
					if ((g1 < 0.0)&&(g2 > 0.0)) gg = y/g;
					if (g > gmax) g = gmax;
					if (g <  -gmax) g = -gmax;
					if (gg > gmax) gg = gmax;
					if (gg <  -gmax) gg = -gmax;

					var n1:int = int(solveQuadratic(1.0, gg, hh, v1) > 0);
					var n2:int = int(solveQuadratic(1.0, g, h, v2) > 0);
					nQuarticRoots[j3] = __cint(2*n1 + 2*n2);
					qrts[j3] = v1[0];
					qrts[__cint(3+j3)] = v1[1];
					qrts[__cint((2*n1) * 3 + j3)] = v2[0];
					qrts[__cint((2*n1+1) * 3 + j3)] = v2[1];
				}
				
				n1 = nQuarticRoots[j3];
				for (var j:int = 0; j < n1; ++j)
					rts[j] = qrts[__cint(j*3 + j3)];
				
				worst3[j3] = quarticError(a, b, c, d, rts, n1);
			}
			
			// choose solution
			j3 = 0;
			if (cubicRoots > 1)
			{
				if ((nQuarticRoots[1] > nQuarticRoots[j3]) ||
					((worst3[1] < worst3[j3] ) && (nQuarticRoots[1] == nQuarticRoots[j3]))) j3 = 1;
				if ((nQuarticRoots[2] > nQuarticRoots[j3]) ||
					((worst3[2] < worst3[j3] ) && (nQuarticRoots[2] == nQuarticRoots[j3]))) j3 = 2;
			}
			
			result[0] = qrts[j3];
			result[1] = qrts[__cint(3+j3)];
			result[2] = qrts[__cint(6+j3)];
			result[3] = qrts[__cint(9+j3)];
			
			return nQuarticRoots[j3];
		}
		
		public function solveQuarticDescartes(a:Number, b:Number, c:Number, d:Number, result:Vector.<Number>):int
		{
			var rts:Vector.<Number> = new Vector.<Number>(4, true);
			var worst3:Vector.<Number> = new Vector.<Number>(3, true);
			var v1:Vector.<Number> = new Vector.<Number>(4, true);
			var v2:Vector.<Number> = new Vector.<Number>(4, true);
			var v3:Vector.<Number> = new Vector.<Number>(4, true);
			var qrts:Vector.<Number> = new Vector.<Number>(12, true);  // quartic roots for each cubic root
			
			// Solve a cubic with a trivial root of 0
			if (d == 0)
			{
				var cubRes:Vector.<Number> = new Vector.<Number>(3, true);
				var n:int = solveCubic2(a, b, c, cubRes);
				result[0] = 0;
				result[1] = cubRes[0];
				result[2] = cubRes[1];
				result[3] = cubRes[2];
				return __cint(1 + n);
			}
			
			var j:int;
			var k:Number,y:Number;
			var p:Number,q:Number,r:Number;
			var e0:Number,e1:Number,e2:Number;
			var g:Number,h:Number;
			var asq:Number;
			var ainv4:Number;
			var e1invk:Number;
			
			asq = a*a;
			e2 = b - asq * (3.0/8.0);
			e1 = c + a*(asq*0.125 - b*0.5);
			e0 = d + asq*(b*0.0625 - asq*(3.0/256.0)) - a*c*0.25;

			p = 2.0*e2;
			q = e2*e2 - 4.0*e0;
			r = -e1*e1;
			
			var cubicRoots:int = solveCubic2(p,q,r, v3);
			var nQuarticRoots:Vector.<int> = new Vector.<int>(3, true);
			
			var math:*;
			__asm(__as3(Math), SetLocal(math));
			
			for (var j3:int = 0; j3 < cubicRoots; ++j3)
			{
				y = v3[j3];
				if (y <= 0.0)
				{
					nQuarticRoots[j3] = 0;
				} else
				{
					__asm(__as3(math), __as3(y), CallProperty(__as3(Math.sqrt), 1), SetLocal(k));
					//k = Math.sqrt(y);
					ainv4 = a*0.25;
					e1invk = e1/k;
					g = (y + e2 + e1invk)*0.5;
					h = (y + e2 - e1invk)*0.5 ;
					var n1:int = int(solveQuadratic( 1.0, -k, g, v1) > 0);
					var n2:int = int(solveQuadratic( 1.0, k, h, v2) > 0);
					
					qrts[j3] = v1[0] - ainv4;
					qrts[__cint(3+j3)] = v1[1] - ainv4;
					qrts[__cint((2*n1) * 3 + j3)] = v2[0] - ainv4;
					qrts[__cint((2*n1+1) * 3 + j3)] = v2[1] - ainv4;
					
					nQuarticRoots[j3]= __cint(n1*2 + n2*2);
				}
				
				n1 = nQuarticRoots[j3];
				for (j = 0; j < n1; ++j)
					rts[j] = qrts[__cint(j*3 + j3)];
				
				worst3[j3] = quarticError(a, b, c, d, rts, n1);
			}
			
			// choose solution
			j3 = 0;
			if (cubicRoots > 1)
			{
				if ((nQuarticRoots[1] > nQuarticRoots[j3]) ||
					((worst3[1] < worst3[j3] ) && (nQuarticRoots[1] == nQuarticRoots[j3]))) j3 = 1;
				if ((nQuarticRoots[2] > nQuarticRoots[j3]) ||
					((worst3[2] < worst3[j3] ) && (nQuarticRoots[2] == nQuarticRoots[j3]))) j3 = 2;
			}
			
			result[0] = qrts[j3];
			result[1] = qrts[__cint(3+j3)];
			result[2] = qrts[__cint(6+j3)];
			result[3] = qrts[__cint(9+j3)];
			
			return nQuarticRoots[j3];
		}
		
		public function solveQuarticFerrari(a:Number, b:Number, c:Number, d:Number, result:Vector.<Number>):int
		{
			var rts:Vector.<Number> = new Vector.<Number>(4, true);
			var worst3:Vector.<Number> = new Vector.<Number>(3, true);
			var v1:Vector.<Number> = new Vector.<Number>(4, true);
			var v2:Vector.<Number> = new Vector.<Number>(4, true);
			var v3:Vector.<Number> = new Vector.<Number>(4, true);
			var qrts:Vector.<Number> = new Vector.<Number>(12, true);  // quartic roots for each cubic root
			
			// Solve a cubic with a trivial root of 0
			if (d == 0)
			{
				var cubRes:Vector.<Number> = new Vector.<Number>(3, true);
				var n:int = solveCubic2(a, b, c, cubRes);
				result[0] = 0;
				result[1] = cubRes[0];
				result[2] = cubRes[1];
				result[3] = cubRes[2];
				return __cint(1 + n);
			}
			
			var j:int;
			var asqinv4:Number;
			var ainv2:Number;
			var d4:Number;
			var yinv2:Number;
			var p:Number,q:Number,r:Number;
			var y:Number;
			var e:Number,f:Number,esq:Number,fsq:Number,ef:Number;
			var g:Number,gg:Number,h:Number,hh:Number;
			
			ainv2 = a*0.5;
			asqinv4 = ainv2*ainv2;
			d4 = d*4.0;
			p = b;
			q = a*c-d4;
			r = (asqinv4 - b)*d4 + c*c;
			
			var cubicRoots:int = solveCubic2(p,q,r, v3);
			var nQuarticRoots:Vector.<int> = new Vector.<int>(3, true);
			
			var math:*;
			__asm(__as3(Math), SetLocal(math));
			
			for (var j3:int = 0; j3 < cubicRoots; ++j3)
			{
				y = v3[j3];
				yinv2 = y*0.5;
				esq = asqinv4 - b - y;
				fsq = yinv2*yinv2 - d;
				if ((esq < 0.0) && (fsq < 0.0))
				{
					nQuarticRoots[j3] = 0;
				} else 
				{
					ef = -(0.25*a*y + 0.5*c);
					if ( ((a > 0.0)&&(y > 0.0)&&(c > 0.0))
						|| ((a > 0.0)&&(y < 0.0)&&(c < 0.0))
						|| ((a < 0.0)&&(y > 0.0)&&(c < 0.0))
						|| ((a < 0.0)&&(y < 0.0)&&(c > 0.0))
						||  (a == 0.0)||(y == 0.0)||(c == 0.0))
					{
						if ((b < 0.0)&&(y < 0.0))
						{
							__asm(__as3(math), __as3(esq), CallProperty(__as3(Math.sqrt), 1), SetLocal(e));
							//e = Math.sqrt(esq);
							f = ef/e;
						}
						else if (d < 0.0)
						{
							__asm(__as3(math), __as3(fsq), CallProperty(__as3(Math.sqrt), 1), SetLocal(f));
							//f = Math.sqrt(fsq);
							e = ef/f;
						}
						else
						{
							if (esq > 0.0) {
								__asm(__as3(math), __as3(esq), CallProperty(__as3(Math.sqrt), 1), SetLocal(e));
								//e = Math.sqrt(esq);
							} else {
								e = 0.0;
							}
							if (fsq > 0.0) {
								__asm(__as3(math), __as3(fsq), CallProperty(__as3(Math.sqrt), 1), SetLocal(f));
								//f = Math.sqrt(fsq);
							} else {
								f = 0.0;
							}
							if (ef < 0.0) f = -f;
						}
					}
					else
					{
						if (esq > 0.0) {
							__asm(__as3(math), __as3(esq), CallProperty(__as3(Math.sqrt), 1), SetLocal(e));
							//e = Math.sqrt(esq);
						} else {
							e = 0.0;
						}
						if (fsq > 0.0) {
							__asm(__as3(math), __as3(fsq), CallProperty(__as3(Math.sqrt), 1), SetLocal(f));
							//f = Math.sqrt(fsq);
						} else {
							f = 0.0;
						}
						if (ef < 0.0) f = -f;
					}
					// note that e >= 0.0
					g = ainv2 - e;
					gg = ainv2 + e;
					if ( ((b > 0.0)&&(y > 0.0))
						|| ((b < 0.0)&&(y < 0.0)) )
					{
						if ((a > 0.0) && (e > 0.0)
							|| (a < 0.0) && (e < 0.0) )
						{
							g = (b + y)/gg;
						} 
						else if ((a > 0.0) && (e < 0.0)
							|| (a < 0.0) && (e > 0.0) )
						{
							gg = (b + y)/g;
						}
					}
					
					hh = -yinv2 + f;
					h = -yinv2 - f;
					if ( ((f > 0.0)&&(y < 0.0))
						|| ((f < 0.0)&&(y > 0.0)) )
					{
						h = d/hh;
					} 
					else if ( ((f < 0.0)&&(y < 0.0))
						|| ((f > 0.0)&&(y > 0.0)) )
					{
						hh = d/h;
					}
					
					var n1:int = int(solveQuadratic( 1.0, gg, hh, v1) > 0);
					var n2:int = int(solveQuadratic( 1.0, g, h, v2) > 0);
					
					qrts[j3] = v1[0];
					qrts[__cint(3+j3)] = v1[1];
					qrts[__cint((2*n1) * 3 + j3)] = v2[0];
					qrts[__cint((2*n1+1) * 3 + j3)] = v2[1];
					
					nQuarticRoots[j3]= __cint(n1*2 + n2*2);
					
				}
				
				n1 = nQuarticRoots[j3];
				for (j = 0; j < n1; ++j)
					rts[j] = qrts[__cint(j*3 + j3)];
				
				worst3[j3] = quarticError(a, b, c, d, rts, n1);
			}
			
			// choose solution
			j3 = 0;
			if (cubicRoots > 1)
			{
				if ((nQuarticRoots[1] > nQuarticRoots[j3]) ||
					((worst3[1] < worst3[j3] ) && (nQuarticRoots[1] == nQuarticRoots[j3]))) j3 = 1;
				if ((nQuarticRoots[2] > nQuarticRoots[j3]) ||
					((worst3[2] < worst3[j3] ) && (nQuarticRoots[2] == nQuarticRoots[j3]))) j3 = 2;
			}
			
			result[0] = qrts[j3];
			result[1] = qrts[__cint(3+j3)];
			result[2] = qrts[__cint(6+j3)];
			result[3] = qrts[__cint(9+j3)];
			
			return nQuarticRoots[j3];
		}
		
		public function solveCubic2(p:Number, q:Number, r:Number, result:Vector.<Number>):int
		{
			const maxSqrt:Number = MAX_SQRT;
			//const maxCubeRoot:Number = MAX_CUBE_ROOT;
			var root1:Number;
			var root2:Number;
			var root3:Number;
			var tmp:Number;
			var oneOverThree:Number = 1.0/3.0;
			
			if (r == 0)
			{
				//no constant term, so divide by x and the result is a
				//quadratic, but we must include the trivial x = 0 root
				var discriminant:Number = (p * p) - (4 * q);
				if (discriminant >= 0)
				{
					//This avoids a cancellation of errors. See
					//http://en.wikipedia.org/wiki/Quadratic_equation#Floating_point_implementation
					var t:Number = -0.5 * ( p + ((p < 0) ? -1 : 1) * Math.sqrt(discriminant));
				      
					root1 = t;
					root2 = q / t;
					root3 = 0;
					
					if (root1 < root2) 
					{
						tmp = root1;
						root1 = root2;
						root2 = tmp;
					}
					if (root2 < 0) 
					{
						tmp = root2;
						root2 = root3;
						root3 = tmp;
						if (root1 < 0) 
						{
							tmp = root1;
							root1 = root2;
							root2 = tmp;
						}
					}
					result[0] = root1;
					result[1] = root2;
					result[2] = root3;
					return 3;
				}
				else
				{
					result[0] = 0;
					return 1;
				}
			}
			
			if ((p == 0) && (q == 0))
			{
				//Special case
				//Equation is x^3 == -r
				root1 = Math.pow(-r, oneOverThree);
				result[0] = root1;
				result[1] = root1;
				result[2] = root1;
				return 3;
			}
			
			if ((p > maxSqrt) || (p < -maxSqrt))
			{
				//Equation limits to x^3 + p * x^2 == 0
				result[0] = -p;
				return 1;
			}
			
			if (q > maxSqrt)
			{
				//Special case, if q is large and the root is -r/q,
				//The x^3 term is negligble, and all other terms cancel.
				result[0] = -r / q;
				return 1;
			}
			
			if (q < -maxSqrt)
			{
				//Special case, equation is x^3 + q x == 0
				result[0] = -Math.sqrt(-q);
				return 1;
			}

			if ((r > maxSqrt) || (r < -maxSqrt))
			{
				//Another special case
				//Equation is x^3 == -r
				result[0] = -Math.pow(r, oneOverThree);
				return 1;
			}
			
			var v:Number = r + (2.0 * p * p / 9.0 - q) * (p * oneOverThree);

			if ((v > maxSqrt) || (v < -maxSqrt))
			{
				result[0] = -p;
				return 1;
			}
			
			var uo3:Number = q * oneOverThree - p * p / 9.0;
			var u2o3:Number = uo3 + uo3;
      
			if ((u2o3 > maxSqrt) || (u2o3 < -maxSqrt))
			{
				if (p==0)
				{
					if (q > 0)
					{
						result[0] = -r / q;
						return 1;
					}
	      
					if (q < 0)
					{
						result[0] = -Math.sqrt(-q);
						return 1;
					}
		
					result[0] = 0;
					return 1;
				}

				result[0] = -q/p;
				return 1;
			}
			
			var uo3sq4:Number = u2o3 * u2o3;
			if (uo3sq4 > maxSqrt)
			{
				if (p == 0)
				{
					if (q > 0)
					{
						result[0] = -r / q;
						return 1;
					}

					if (q < 0)
					{
						result[0] = -Math.sqrt(-q);
						return 1;
					}
					result[0] = 0;
					return 1;
				}

				result[0] = -q / p;
				return 1;
			}
			
			var j:Number = (uo3sq4 * uo3) + v * v;
  
			if (j > 0)
			{
				//Only one root (but this test can be wrong due to a
				//catastrophic cancellation in j 
				//(i.e. (uo3sq4 * uo3) == v * v)
				var w:Number = Math.sqrt(j);
				if (v < 0)
					root1 = Math.pow(0.5*(w-v), oneOverThree) - (uo3) * Math.pow(2.0 / (w-v), oneOverThree) - p * oneOverThree;
				else
					root1 = uo3 * Math.pow(2.0 / (w+v), oneOverThree) - Math.pow(0.5*(w+v), oneOverThree) - p * oneOverThree;

				//We now polish the root up before we use it in other calculations
				root1 = cubicNewtonRootPolish(p, q, r, root1, 15);
	 
				//We double check that there are no more roots by using a
				//quadratic formula on the factored problem, this helps when
				//the j test is wrong due to numerical error.
	  
				//We have a choice of either -r/root1, or q -
				//(p+root1)*root1 for the constant term of the quadratic. 
				//
				//The division one usually results in more accurate roots
				//when it finds them but fails to detect real roots more
				//often than the multiply.
				var B:Number = p + root1;
				var C:Number = -r / root1;
				discriminant = (B * B) - (4 * C);
				if (discriminant >= 0)
				{
					//This avoids a cancellation of errors. See
					//http://en.wikipedia.org/wiki/Quadratic_equation#Floating_point_implementation
					t = -0.5 * ( B + ((B < 0) ? -1 : 1) * Math.sqrt(discriminant));
				      
					root2 = t;
					root3 = C / t;
					
					result[0] = root1;
					result[1] = root2;
					result[2] = root3;
					
					return 3;
				}
				//
				//However, the multiply detects roots where there are none,
				//the division does not. So we must either accept missing
				//roots or extra roots, here we choose missing roots
				//
				//if (quadSolve(q-(p+root1)*root1, p + root1, 1.0, root2, root3)) 
				//  return 3;
				
				result[0] = root1;
				return 1;
			}
			
			if (uo3 >= 0)
			{
				//Multiple root detected	  
				root1 = Math.pow(v, oneOverThree) - p * oneOverThree;
				result[0] = root1;
				result[1] = root1;
				result[2] = root1;
				return 3;
			}
			
			var muo3:Number = - uo3;
			var s:Number;
			if (muo3 > 0)
			{
				s = Math.sqrt(muo3);
				if (p > 0) s = -s;
			}
			else {
				s = 0;
			}
			
			var scube:Number = s * muo3;
			if (scube == 0)
			{
				result[0] = - p * oneOverThree;
				return 1;
			}
			
			t = - v / (scube + scube);
			var k:Number = Math.acos(t) * oneOverThree;
			var cosk:Number = Math.cos(k);
			root1 = (s + s) * cosk - p * oneOverThree;
      
			var sinsqk:Number = 1.0 - cosk * cosk;
			if (sinsqk < 0) 
			{
				result[0] = root1;
				return 1;
			}

			//var rt3sink:Number = Math.sqrt(3) * Math.sqrt(sinsqk);
			var rt3sink:Number = 1.7320508075688772 * Math.sqrt(sinsqk);
			root2 = s * (-cosk + rt3sink) - p * oneOverThree;
			root3 = s * (-cosk - rt3sink) - p * oneOverThree;
			
			root1 = cubicNewtonRootPolish(p, q, r, root1, 10);
			root2 = cubicNewtonRootPolish(p, q, r, root2, 10);
			root3 = cubicNewtonRootPolish(p, q, r, root3, 10);
			
			result[0] = root1;
			result[1] = root2;
			result[2] = root3;
			
			return 3;
		}
		
		public function cubicNewtonRootPolish(p:Number, q:Number, r:Number, root:Number, iterations:int):Number
		{
			for (var it:int = 0; it < iterations; ++it)
			{
				var error:Number = ((root + p)*root + q) * root + r;
				var derivative:Number = (3.0 * root + 2 * p) * root + q;
	    
				if ((error == 0) || derivative == 0) return root;
	    
				root -= error / derivative;
			}
			return root;
		}
		
		public function solveCubic(a:Number, b:Number, c:Number, result:Vector.<Number>):int
		{
			var q:Number = a * a - 3 * b;
			var r:Number = 2 * a * a * a - 9 * a * b + 27 * c;
			
			var Q:Number = q / 9;
			var R:Number = r / 54;
			
			var Q3:Number = Q * Q * Q;
			var R2:Number = R * R;
			var CR2:Number = 729 * r * r;
			var CQ3:Number = 2916 * q * q * q;
			
			var sqrtQ:Number;
			
			if (R == 0 && Q == 0) 
			{
				// Tripple root in one place.
				b = -a / 3;
				result[0] = b;
				result[1] = b;
				result[2] = b;
				return 3;			
			} 
			else if (CR2 == CQ3) 
			{
				// This test is actually R2 == Q3, written in a form suitable for exact
				// computation with integers.
				//
				// Due to finite precision some double roots may be missed, and considered
				// to be a pair of complex roots z = x +/- epsilon i close to the real axis.
				
			    sqrtQ = Math.sqrt(Q);
			    b = a / 3;
			    if (R > 0) 
			    {
					result[0] = -2 * sqrtQ - b;
					result[1] =      sqrtQ - b;
					result[2] =      sqrtQ - b;
			    } else {
					result[0] =     -sqrtQ - b;
					result[1] =     -sqrtQ - b;
					result[2] =  2 * sqrtQ - b;
			    }
			    
			    return 3;			
			} 
			else if (CR2 < CQ3) 
			{
				// This case is equivalent to R2 < Q3.
				sqrtQ = Math.sqrt(Q);
				var sqrtQ3:Number = sqrtQ * sqrtQ * sqrtQ;
				var theta:Number = Math.acos(R / sqrtQ3);
				var norm:Number = -2 * sqrtQ;
				b = a / 3;
				var x0:Number = norm * Math.cos (theta / 3) - b;
				var x1:Number = norm * Math.cos ((theta + 6.283185307179586) / 3) - b;
				var x2:Number = norm * Math.cos ((theta - 6.283185307179586) / 3) - b;
			
				// Put the roots in ascending order.
				var xt:Number;
				if (x0 > x1)
				{
					xt = x0;
					x0 = x1;
					x1 = xt;
			    }
				if (x1 > x2)
			    {
			    	xt = x1;
			    	x1 = x2;
			    	x2 = xt;
					if (x0 > x1)
					{
						xt = x0;
						x0 = x1;
						x1 = xt;
					}
				}
				result[0] = x0;
				result[1] = x1;
				result[2] = x2;
			    return 3;
			  }
			  
			var sgnR:Number = (1.0 - (int(R < 0.0) << 1));
			var A:Number = -sgnR * Math.pow (FastMath.abs(R) + Math.sqrt(R2 - Q3), 1.0/3.0);
			var B:Number = Q / A ;
			result[0] = A + B - a / 3;
			return 1;
		}
		
		public function solveQuadratic(a:Number, b:Number, c:Number, result:Vector.<Number>):int
		{
			// Contingency: if A = 0, not a quadratic = linear
			if(a == 0)
			{
				//If B is zero then we have a NaN
				if(b == 0) return 0;
				
				var root:Number = -1.0 * c / b;
				result[0] = root;
				result[1] = root;
				return 1;
			}
			
			var discriminant:Number = (b * b) - (4 * a * c);

			//Cannot do imaginary numbers, yet
			if (discriminant < 0) return 0;

			//This avoids a cancellation of errors. See
			//http://en.wikipedia.org/wiki/Quadratic_equation#Floating_point_implementation
			var t:Number = -0.5 * ( b + ((b < 0) ? -1 : 1) * Math.sqrt(discriminant));

			result[0] = t / a;
			result[1] = c / t;
			
			return 2;
		}
		
		public function quarticError(a:Number, b:Number, c:Number, d:Number, roots:Vector.<Number>, rootCount:int):Number
		{
			var maxError:Number = 0;
			var currError:Number = maxError;
			var tmp:Number;
			var math:*;
			__asm(__as3(Math), SetLocal(math));
			for (var root:int = 0; root < rootCount; ++root)
			{
				const rt:Number = roots[root];
				const value:Number = (((rt+a) * rt + b) * rt + c) * rt + d;

				if (value == 0) { continue; }

				const deriv:Number = ((4 * rt + 3 * a) * rt + 2 * b) * rt + c;

				if (deriv != 0) 
				{
					currError = FastMath.abs(value / deriv);
				}
				else
				{
					const secDeriv:Number = (12 * rt + 6 * a) * rt + 2 * b;
					if (secDeriv != 0)
					{
						tmp = FastMath.abs(value / secDeriv);
						__asm(__as3(math), __as3(tmp), CallProperty(__as3(Math.sqrt), 1), SetLocal(currError));
						//currError = Math.sqrt(FastMath.abs(value / secDeriv));
					}
					else
					{
						const thirdDeriv:Number = 24 * rt + 6 * a;
						if (thirdDeriv != 0)
						{
							currError = Math.pow(FastMath.abs(value / thirdDeriv), 1.0/3.0);
						}
						else
						{
							tmp = FastMath.abs(value)/24;
							__asm(__as3(math), __as3(tmp), CallProperty(__as3(Math.sqrt), 1), SetLocal(tmp));
							__asm(__as3(math), __as3(tmp), CallProperty(__as3(Math.sqrt), 1), SetLocal(currError));
							//currError = Math.sqrt(Math.sqrt(FastMath.abs(value)/24));
						}
					}
				}
				maxError = FastMath.max(currError, maxError);
			}
			return maxError;
		}
	}
}
