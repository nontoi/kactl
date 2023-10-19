#include "../utilities/template.h"

#include "../../content/number-theory/ModSqrt.h"

int main() {
	rep(p,2,10000) {
		rep(i,2,p) if (p % i == 0) goto next;
		rep(a,0,p) {
			if (p != 2 && modpow(a, (p-1)/2, p) == p-1) continue;
			ll x = sqrt(a, p);
			assert(0 <= x && x < p);
			assert(x * x % p == a);
		}
next:;
	}
	cout<<"Tests passed!"<<endl;
}
