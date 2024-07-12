/**
 * Author: FHVirus, from 8BQube, abc864197532, Fysty's code
 * Date: 2023-10-20
 * Description:
 * Status: tested @ yosupo judge
 */
#pragma once

#include "NumberTheoreticTransform.h"
#include "../number-theory/ModPow.h"
#include "../number-theory/ModSqrt.h"

template <ll mod = 998244353, ll root = 3> struct Poly : vl {
  typedef Poly P;
  static int bc(int n)
  { return n <= 1 ? 1 : 1 << (32 - __builtin_clz(n - 1)); }
  static NTT<mod, root> ntt; // coefficients in [0, P)
  explicit Poly(int n = 1) : vl(n) {}
  int n() const { return (int) size(); }
  static ll modsub(ll a, ll b) { return a-b + (a<b?mod:0); }
  static ll modinv(ll x) { return modpow(x, mod - 2, mod); }
  Poly(const vl &v) : vl(v) {}
  Poly(const P &p, int m) : vl(m)
  { copy_n(p.data(), min(sz(p), m), data()); }

  P &irev() { return reverse(all()), *this; }
  P &isz(int s) { return resize(s), *this; }
  P &iadd(const P &o) { // n() == o.n()
    rep(i,0,n()) (*this)[i] = ((*this)[i] + o[i]) % mod;
    return *this; }
  P &imul(ll k) {
    rep(i,0,n()) (*this)[i] = ((*this)[i] * k) % mod;
    return *this; }
  P &imul(P v) {
    rep(i,0,n()) (*this)[i] = ((*this)[i] * v[i]) % mod;
    return *this; }
  P &trim() {
    while (n() > 1 and back() == 0) pop_back(); 
    return *this; }

  P Mul(const P &o) const {
    const auto s = bc(n() + sz(o) - 1), inv = modinv(s);
    P x(*this, s), y(o, s), out(s);
    ntt(x.data(), s), ntt(y.data(), s);
    rep(i,0,s) out[-i & (s-1)] = x[i] * y[i] % mod * inv % mod;
    ntt(out.data(), s);
    return out.isz(n() + sz(o) - 1);
  }

  P Inv() const { assert(*begin() != 0);
    if (n() == 1) return vl{modinv(*begin())};
    const auto s = bc(n() * 2), inv = modinv(s);
    P x = P(*this, (n()+1)/2).Inv().isz(s), y(*this,s), out(s);
    ntt(x.data(), s), ntt(y.data(), s);
    rep(i, 0, s) {
      ll &t = out[-i & (s - 1)];
      t = x[i] * modsub(2, x[i]*y[i]%mod) % mod * inv % mod;
    }
    ntt(out.data(), s);
    return out.isz(n());
  }

  P sqimp() const { // coef[0] \in [1, mod)^2
    if (n() == 1) return vl{modsqrt((*this)[0], mod)};
    P x = P(*this, (n() + 1) / 2).Sqrt().isz(n());
    return x.iadd(Mul(x.Inv()).isz(n())).imul(mod / 2 + 1);
  }
  P Sqrt() const { // returns { -1 } on fail
    int m = 0; while (m < n() and (*this)[m] == 0) ++m;
    if (m == n()) return P(n());
    if (m % 2 or modsqrt((*this)[m], mod) == -1) return vl{-1};
    P p = P(vl{data() + m, data() + n()}, n() - m/2).sqimp();
    return p.irev().isz(sz(p) + m / 2).irev();
  }

  pair<P, P> DivMod(P o) const { // {0} for 0
    if (n() < sz(o)) return {vl{0}, *this};
    const int s = n() - sz(o) + 1;
    P x(o); x.irev().isz(s);
    P y(*this); y.irev().isz(s);
    P Q = y.Mul(x.Inv()).isz(s).irev();
    x = o.Mul(Q), y = *this;
    rep(i, 0, n()) y[i] = modsub(y[i], x[i]);
    return {Q, y.isz(max(1, sz(o)-1))};
  }

  P Dx() const {
    P ret(n() - 1);
    rep(i, 0, sz(ret)) ret[i] = (i + 1) * (*this)[i + 1] % mod;
    return ret.isz(max(1, sz(ret)));
  }
  P Sx() const {
    P ret(n() + 1);
    rep(i, 0, n()) ret[i+1] = modinv(i + 1) * (*this)[i] % mod;
    return ret;
  }
  P Ln() const { // coef[0] == 1
    return Dx().Mul(Inv()).Sx().isz(n());
  }
  P Exp() const { // coef[0] == 0
    if (n() == 1) return vl{1};
    P x = P(*this, (n() + 1) / 2).Exp().isz(n());
    P y = x.Ln(); y[0] = mod - 1;
    rep(i, 0, n()) y[i] = modsub((*this)[i], y[i]);
    return x.Mul(y).isz(n());
  }

  P Pow(const string &K) const {
    int nz = 0; ll nk = 0, nk2 = 0;
    while (nz < n() && !(*this)[nz]) ++nz;
    for (char c : K) {
      nk = (nk * 10 + c - '0') % mod;
      nk2 = nk2 * 10 + c - '0';
      if (nk2 * nz >= n()) return P(n());
      nk2 %= mod - 1;
    }
    if (!nk && !nk2) return P(vl{1}, n());
    P x = vl(data() + nz, data() + n() - nz * (nk2 - 1));
    ll x0 = x[0];
    return x.imul(modinv(x0)).Ln().imul(nk).Exp().
      imul(modpow(x0, nk2, mod)).irev().isz(n()).irev();
  }

  P tmul(int nn, const P &rhs) const {
    P Y = Mul(rhs).isz(n() + nn - 1);
    return P({Y.data() + n() - 1, Y.data() + Y.n()});
  }
  static vector<P> tree(const vl &x) {
    const int m = sz(x);
    vector<P> up(m * 2);
    rep(i, 0, m) up[m + i] = vl{(x[i] ? mod - x[i] : 0), 1};
    for (int i = m - 1; i > 0; --i)
      up[i] = up[i * 2].Mul(up[i * 2 + 1]);
    return up;
  }
  vl eval(const vl &x, const vector<P> &up) const {
    const int m = sz(x); if (!m) return {};
    vector<P> dn(m * 2);
    dn[1]=P(up[1]).irev().isz(n()).Inv().irev().tmul(m,*this);
    rep(i,2,m*2) dn[i] = up[i^1].tmul(up[i].n()-1, dn[i/2]);
    vl y(m); rep(i, 0, m) y[i] = dn[m + i][0];
    return y;
  }
  vl Eval(const vl &x) const { return eval(x, tree(x)); }
  static P Interpolate(const vl &x, const vl &y) { // 1e5, 1.4s
    const int m = sz(x);
    vector<P> up = tree(x), dn(m * 2);
    vl z = up[1].Dx().eval(x, up);
    rep(i, 0, m) z[i] = y[i] * modinv(z[i]) % mod;
    rep(i, 0, m) dn[m + i] = vl{z[i]};
    for (int i = m - 1; i > 0; --i)
     dn[i]=dn[i*2].Mul(up[i*2+1]).iadd(dn[i*2+1].Mul(up[i*2]));
    return dn[1];
  }

  // a_n = \sum c_j a_(n-j)
  static ll LinearRecursion(const vl &a, const vl &c, ll n) {
    const int k = sz(a); assert(sz(c) == k + 1);
    P C(k + 1), W(vl{1}, k), M = vl{0, 1};
    rep(i, 1, k + 1) C[k - i] = (c[i] == 0 ? 0 : mod - c[i]);
    C[k] = 1;
    while (n) {
      if (n % 2) W = W.Mul(M).DivMod(C).second;
      n /= 2; M = M.Mul(M).DivMod(C).second;
    }
    ll ret = 0;
    rep(i, 0, k) ret = (ret + W[i] * a[i]) % mod;
    return ret;
  }

  P TaylorShift(ll c) const {
    P fac(n()), caf(n()); fac[0] = 1;
    rep (i, 1, n()) fac[i] = fac[i-1] * i % mod;
    rep (i, 0, n()) caf[i] = modinv(fac[i]);
    P x = P(*this).imul(fac), y(n()); ll w = 1;
    rep (i, 0, n()) y[i] = w * caf[i] % mod, w = w * c % mod;
    return x.irev().Mul(y).isz(n()).irev().imul(caf);
  }
  P SamplingShift(int m, ll c) const {
    const int k = max(n(), m);
    P fac(k), caf(k); fac[0] = 1;
    rep (i, 1, k) fac[i] = fac[i-1] * i % mod;
    rep (i, 0, k) caf[i] = modinv(fac[i]);
    P x = P(*this).imul(caf), y = caf;
    rep (i, 0, n()) if (i & 1)
      y[i] = (y[i] == 0 ? 0 : mod - y[i]);
    x = x.Mul(y).isz(n()).imul(fac).irev();
    ll w = 1;
    rep (i, 0, n()) y[i] = caf[i] * w % mod,
        w = w * modsub(c, i) % mod;
    x = x.Mul(y).isz(n()).irev().imul(caf).isz(m);
    y = caf; y = y.isz(m);
    return x.Mul(y).isz(m).imul(fac);
  }
};
