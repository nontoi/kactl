#include "../utilities/template.h"

#include "../../content/number-theory/ModularArithmetic.h"

int main() {
  const ll mod = 17;
	rep(a,0,mod) rep(b,1,mod) {
		mint<ll, mod> ma(a);
		mint<ll, mod> mb(b);
		mint<ll, mod> mc = ma / mb;
		assert((mc * mb).v == a);
	}
	mint<ll, mod> a = 2;
	ll cur = 1;
	rep(i, 0, mod) {
		assert((a.pow(i)).v == cur);
		cur = (cur * 2) % mod;
		// cout << i << ": " << (a ^ i).x << endl;
	}
	cout<<"Tests passed!"<<endl;
}
