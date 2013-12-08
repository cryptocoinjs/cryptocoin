!function(e){"object"==typeof exports?module.exports=e():"function"==typeof define&&define.amd?define(e):"undefined"!=typeof window?window.cryptocoin=e():"undefined"!=typeof global?global.cryptocoin=e():"undefined"!=typeof self&&(self.cryptocoin=e())}(function(){var define,module,exports;return (function e(t,n,r){function s(o,u){if(!n[o]){if(!t[o]){var a=typeof require=="function"&&require;if(!u&&a)return a(o,!0);if(i)return i(o,!0);throw new Error("Cannot find module '"+o+"'")}var f=n[o]={exports:{}};t[o][0].call(f.exports,function(e){var n=t[o][1][e];return s(n?n:e)},f,f.exports,e,t,n,r)}return n[o].exports}var i=typeof require=="function"&&require;for(var o=0;o<r.length;o++)s(r[o]);return s})({1:[function(require,module,exports){

var me = module.exports

me.VERSION = '0.3.0' //in sync with package.json

var Crypto = {
  sha256: require('sha256'),
  ripemd160: require('ripemd160')
}

me.Address = require('btc-address')
me.Key = require('eckey')
me.ECDSA = require('ecdsa')
me.BigInteger = require('bigi')
me.Crypto = Crypto
me.base58 = require('bs58')
me.convertHex = require('convert-hex')
me.secureRandom = require('secure-random')
},{"bigi":2,"bs58":4,"btc-address":5,"convert-hex":6,"ecdsa":7,"eckey":11,"ripemd160":14,"secure-random":16,"sha256":17}],2:[function(require,module,exports){
!function(globals) {
'use strict'

/***
  scroll to the bottom for the UMDjs declarations
***/

// Copyright (c) 2005  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Basic JavaScript BN library - subset useful for RSA encryption.

// Bits per digit
var dbits;

// JavaScript engine analysis
var canary = 0xdeadbeefcafe;
var j_lm = ((canary&0xffffff)==0xefcafe);

// (public) Constructor
function BigInteger(a,b,c) {
  if (!(this instanceof BigInteger)) {
    return new BigInteger(a, b, c);
  }

  if(a != null) {
    if("number" == typeof a) this.fromNumber(a,b,c);
    else if(b == null && "string" != typeof a) this.fromString(a,256);
    else this.fromString(a,b);
  }
}

var proto = BigInteger.prototype;

// return new, unset BigInteger
function nbi() { return new BigInteger(null); }

// am: Compute w_j += (x*this_i), propagate carries,
// c is initial carry, returns final carry.
// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
// We need to select the fastest one that works in this environment.

// am1: use a single mult and divide to get the high bits,
// max digit bits should be 26 because
// max internal value = 2*dvalue^2-2*dvalue (< 2^53)
function am1(i,x,w,j,c,n) {
  while(--n >= 0) {
    var v = x*this[i++]+w[j]+c;
    c = Math.floor(v/0x4000000);
    w[j++] = v&0x3ffffff;
  }
  return c;
}
// am2 avoids a big mult-and-extract completely.
// Max digit bits should be <= 30 because we do bitwise ops
// on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
function am2(i,x,w,j,c,n) {
  var xl = x&0x7fff, xh = x>>15;
  while(--n >= 0) {
    var l = this[i]&0x7fff;
    var h = this[i++]>>15;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x7fff)<<15)+w[j]+(c&0x3fffffff);
    c = (l>>>30)+(m>>>15)+xh*h+(c>>>30);
    w[j++] = l&0x3fffffff;
  }
  return c;
}
// Alternately, set max digit bits to 28 since some
// browsers slow down when dealing with 32-bit numbers.
function am3(i,x,w,j,c,n) {
  var xl = x&0x3fff, xh = x>>14;
  while(--n >= 0) {
    var l = this[i]&0x3fff;
    var h = this[i++]>>14;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x3fff)<<14)+w[j]+c;
    c = (l>>28)+(m>>14)+xh*h;
    w[j++] = l&0xfffffff;
  }
  return c;
}

// wtf?
BigInteger.prototype.am = am1;
dbits = 26;

/*
if(j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
  BigInteger.prototype.am = am2;
  dbits = 30;
}
else if(j_lm && (navigator.appName != "Netscape")) {
  BigInteger.prototype.am = am1;
  dbits = 26;
}
else { // Mozilla/Netscape seems to prefer am3
  BigInteger.prototype.am = am3;
  dbits = 28;
}
*/

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = ((1<<dbits)-1);
var DV = BigInteger.prototype.DV = (1<<dbits);

var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2,BI_FP);
BigInteger.prototype.F1 = BI_FP-dbits;
BigInteger.prototype.F2 = 2*dbits-BI_FP;

// Digit conversions
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr,vv;
rr = "0".charCodeAt(0);
for(vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

function int2char(n) { return BI_RM.charAt(n); }
function intAt(s,i) {
  var c = BI_RC[s.charCodeAt(i)];
  return (c==null)?-1:c;
}

// (protected) copy this to r
function bnpCopyTo(r) {
  for(var i = this.t-1; i >= 0; --i) r[i] = this[i];
  r.t = this.t;
  r.s = this.s;
}

// (protected) set from integer value x, -DV <= x < DV
function bnpFromInt(x) {
  this.t = 1;
  this.s = (x<0)?-1:0;
  if(x > 0) this[0] = x;
  else if(x < -1) this[0] = x+DV;
  else this.t = 0;
}

// return bigint initialized to value
function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

// (protected) set from string and radix
function bnpFromString(s,b) {
  var self = this;

  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 256) k = 8; // byte array
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else { self.fromRadix(s,b); return; }
  self.t = 0;
  self.s = 0;
  var i = s.length, mi = false, sh = 0;
  while(--i >= 0) {
    var x = (k==8)?s[i]&0xff:intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-") mi = true;
      continue;
    }
    mi = false;
    if(sh == 0)
      self[self.t++] = x;
    else if(sh+k > self.DB) {
      self[self.t-1] |= (x&((1<<(self.DB-sh))-1))<<sh;
      self[self.t++] = (x>>(self.DB-sh));
    }
    else
      self[self.t-1] |= x<<sh;
    sh += k;
    if(sh >= self.DB) sh -= self.DB;
  }
  if(k == 8 && (s[0]&0x80) != 0) {
    self.s = -1;
    if(sh > 0) self[self.t-1] |= ((1<<(self.DB-sh))-1)<<sh;
  }
  self.clamp();
  if(mi) BigInteger.ZERO.subTo(self,self);
}

// (protected) clamp off excess high words
function bnpClamp() {
  var c = this.s&this.DM;
  while(this.t > 0 && this[this.t-1] == c) --this.t;
}

// (public) return string representation in given radix
function bnToString(b) {
  var self = this;
  if(self.s < 0) return "-"+self.negate().toString(b);
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else return self.toRadix(b);
  var km = (1<<k)-1, d, m = false, r = "", i = self.t;
  var p = self.DB-(i*self.DB)%k;
  if(i-- > 0) {
    if(p < self.DB && (d = self[i]>>p) > 0) { m = true; r = int2char(d); }
    while(i >= 0) {
      if(p < k) {
        d = (self[i]&((1<<p)-1))<<(k-p);
        d |= self[--i]>>(p+=self.DB-k);
      }
      else {
        d = (self[i]>>(p-=k))&km;
        if(p <= 0) { p += self.DB; --i; }
      }
      if(d > 0) m = true;
      if(m) r += int2char(d);
    }
  }
  return m?r:"0";
}

// (public) -this
function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this,r); return r; }

// (public) |this|
function bnAbs() { return (this.s<0)?this.negate():this; }

// (public) return + if this > a, - if this < a, 0 if equal
function bnCompareTo(a) {
  var r = this.s-a.s;
  if(r != 0) return r;
  var i = this.t;
  r = i-a.t;
  if(r != 0) return (this.s<0)?-r:r;
  while(--i >= 0) if((r=this[i]-a[i]) != 0) return r;
  return 0;
}

// returns bit length of the integer x
function nbits(x) {
  var r = 1, t;
  if((t=x>>>16) != 0) { x = t; r += 16; }
  if((t=x>>8) != 0) { x = t; r += 8; }
  if((t=x>>4) != 0) { x = t; r += 4; }
  if((t=x>>2) != 0) { x = t; r += 2; }
  if((t=x>>1) != 0) { x = t; r += 1; }
  return r;
}

// (public) return the number of bits in "this"
function bnBitLength() {
  if(this.t <= 0) return 0;
  return this.DB*(this.t-1)+nbits(this[this.t-1]^(this.s&this.DM));
}

// (protected) r = this << n*DB
function bnpDLShiftTo(n,r) {
  var i;
  for(i = this.t-1; i >= 0; --i) r[i+n] = this[i];
  for(i = n-1; i >= 0; --i) r[i] = 0;
  r.t = this.t+n;
  r.s = this.s;
}

// (protected) r = this >> n*DB
function bnpDRShiftTo(n,r) {
  for(var i = n; i < this.t; ++i) r[i-n] = this[i];
  r.t = Math.max(this.t-n,0);
  r.s = this.s;
}

// (protected) r = this << n
function bnpLShiftTo(n,r) {
  var self = this;
  var bs = n%self.DB;
  var cbs = self.DB-bs;
  var bm = (1<<cbs)-1;
  var ds = Math.floor(n/self.DB), c = (self.s<<bs)&self.DM, i;
  for(i = self.t-1; i >= 0; --i) {
    r[i+ds+1] = (self[i]>>cbs)|c;
    c = (self[i]&bm)<<bs;
  }
  for(i = ds-1; i >= 0; --i) r[i] = 0;
  r[ds] = c;
  r.t = self.t+ds+1;
  r.s = self.s;
  r.clamp();
}

// (protected) r = this >> n
function bnpRShiftTo(n,r) {
  var self = this;
  r.s = self.s;
  var ds = Math.floor(n/self.DB);
  if(ds >= self.t) { r.t = 0; return; }
  var bs = n%self.DB;
  var cbs = self.DB-bs;
  var bm = (1<<bs)-1;
  r[0] = self[ds]>>bs;
  for(var i = ds+1; i < self.t; ++i) {
    r[i-ds-1] |= (self[i]&bm)<<cbs;
    r[i-ds] = self[i]>>bs;
  }
  if(bs > 0) r[self.t-ds-1] |= (self.s&bm)<<cbs;
  r.t = self.t-ds;
  r.clamp();
}

// (protected) r = this - a
function bnpSubTo(a,r) {
  var self = this;
  var i = 0, c = 0, m = Math.min(a.t,self.t);
  while(i < m) {
    c += self[i]-a[i];
    r[i++] = c&self.DM;
    c >>= self.DB;
  }
  if(a.t < self.t) {
    c -= a.s;
    while(i < self.t) {
      c += self[i];
      r[i++] = c&self.DM;
      c >>= self.DB;
    }
    c += self.s;
  }
  else {
    c += self.s;
    while(i < a.t) {
      c -= a[i];
      r[i++] = c&self.DM;
      c >>= self.DB;
    }
    c -= a.s;
  }
  r.s = (c<0)?-1:0;
  if(c < -1) r[i++] = self.DV+c;
  else if(c > 0) r[i++] = c;
  r.t = i;
  r.clamp();
}

// (protected) r = this * a, r != this,a (HAC 14.12)
// "this" should be the larger one if appropriate.
function bnpMultiplyTo(a,r) {
  var x = this.abs(), y = a.abs();
  var i = x.t;
  r.t = i+y.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < y.t; ++i) r[i+x.t] = x.am(0,y[i],r,i,0,x.t);
  r.s = 0;
  r.clamp();
  if(this.s != a.s) BigInteger.ZERO.subTo(r,r);
}

// (protected) r = this^2, r != this (HAC 14.16)
function bnpSquareTo(r) {
  var x = this.abs();
  var i = r.t = 2*x.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < x.t-1; ++i) {
    var c = x.am(i,x[i],r,2*i,0,1);
    if((r[i+x.t]+=x.am(i+1,2*x[i],r,2*i+1,c,x.t-i-1)) >= x.DV) {
      r[i+x.t] -= x.DV;
      r[i+x.t+1] = 1;
    }
  }
  if(r.t > 0) r[r.t-1] += x.am(i,x[i],r,2*i,0,1);
  r.s = 0;
  r.clamp();
}

// (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
// r != q, this != m.  q or r may be null.
function bnpDivRemTo(m,q,r) {
  var self = this;
  var pm = m.abs();
  if(pm.t <= 0) return;
  var pt = self.abs();
  if(pt.t < pm.t) {
    if(q != null) q.fromInt(0);
    if(r != null) self.copyTo(r);
    return;
  }
  if(r == null) r = nbi();
  var y = nbi(), ts = self.s, ms = m.s;
  var nsh = self.DB-nbits(pm[pm.t-1]);  // normalize modulus
  if(nsh > 0) { pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
  else { pm.copyTo(y); pt.copyTo(r); }
  var ys = y.t;
  var y0 = y[ys-1];
  if(y0 == 0) return;
  var yt = y0*(1<<self.F1)+((ys>1)?y[ys-2]>>self.F2:0);
  var d1 = self.FV/yt, d2 = (1<<self.F1)/yt, e = 1<<self.F2;
  var i = r.t, j = i-ys, t = (q==null)?nbi():q;
  y.dlShiftTo(j,t);
  if(r.compareTo(t) >= 0) {
    r[r.t++] = 1;
    r.subTo(t,r);
  }
  BigInteger.ONE.dlShiftTo(ys,t);
  t.subTo(y,y); // "negative" y so we can replace sub with am later
  while(y.t < ys) y[y.t++] = 0;
  while(--j >= 0) {
    // Estimate quotient digit
    var qd = (r[--i]==y0)?self.DM:Math.floor(r[i]*d1+(r[i-1]+e)*d2);
    if((r[i]+=y.am(0,qd,r,j,0,ys)) < qd) {  // Try it out
      y.dlShiftTo(j,t);
      r.subTo(t,r);
      while(r[i] < --qd) r.subTo(t,r);
    }
  }
  if(q != null) {
    r.drShiftTo(ys,q);
    if(ts != ms) BigInteger.ZERO.subTo(q,q);
  }
  r.t = ys;
  r.clamp();
  if(nsh > 0) r.rShiftTo(nsh,r);    // Denormalize remainder
  if(ts < 0) BigInteger.ZERO.subTo(r,r);
}

// (public) this mod a
function bnMod(a) {
  var r = nbi();
  this.abs().divRemTo(a,null,r);
  if(this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r,r);
  return r;
}

// Modular reduction using "classic" algorithm
function Classic(m) { this.m = m; }
function cConvert(x) {
  if(x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
  else return x;
}
function cRevert(x) { return x; }
function cReduce(x) { x.divRemTo(this.m,null,x); }
function cMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
function cSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;

// (protected) return "-1/this % 2^DB"; useful for Mont. reduction
// justification:
//         xy == 1 (mod m)
//         xy =  1+km
//   xy(2-xy) = (1+km)(1-km)
// x[y(2-xy)] = 1-k^2m^2
// x[y(2-xy)] == 1 (mod m^2)
// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
// JS multiply "overflows" differently from C/C++, so care is needed here.
function bnpInvDigit() {
  if(this.t < 1) return 0;
  var x = this[0];
  if((x&1) == 0) return 0;
  var y = x&3;      // y == 1/x mod 2^2
  y = (y*(2-(x&0xf)*y))&0xf;    // y == 1/x mod 2^4
  y = (y*(2-(x&0xff)*y))&0xff;  // y == 1/x mod 2^8
  y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff;   // y == 1/x mod 2^16
  // last step - calculate inverse mod DV directly;
  // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
  y = (y*(2-x*y%this.DV))%this.DV;      // y == 1/x mod 2^dbits
  // we really want the negative inverse, and -DV < y < DV
  return (y>0)?this.DV-y:-y;
}

// Montgomery reduction
function Montgomery(m) {
  this.m = m;
  this.mp = m.invDigit();
  this.mpl = this.mp&0x7fff;
  this.mph = this.mp>>15;
  this.um = (1<<(m.DB-15))-1;
  this.mt2 = 2*m.t;
}

// xR mod m
function montConvert(x) {
  var r = nbi();
  x.abs().dlShiftTo(this.m.t,r);
  r.divRemTo(this.m,null,r);
  if(x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r,r);
  return r;
}

// x/R mod m
function montRevert(x) {
  var r = nbi();
  x.copyTo(r);
  this.reduce(r);
  return r;
}

// x = x/R mod m (HAC 14.32)
function montReduce(x) {
  while(x.t <= this.mt2)    // pad x so am has enough room later
    x[x.t++] = 0;
  for(var i = 0; i < this.m.t; ++i) {
    // faster way of calculating u0 = x[i]*mp mod DV
    var j = x[i]&0x7fff;
    var u0 = (j*this.mpl+(((j*this.mph+(x[i]>>15)*this.mpl)&this.um)<<15))&x.DM;
    // use am to combine the multiply-shift-add into one call
    j = i+this.m.t;
    x[j] += this.m.am(0,u0,x,i,0,this.m.t);
    // propagate carry
    while(x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
  }
  x.clamp();
  x.drShiftTo(this.m.t,x);
  if(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = "x^2/R mod m"; x != r
function montSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = "xy/R mod m"; x,y != r
function montMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;

// (protected) true iff this is even
function bnpIsEven() { return ((this.t>0)?(this[0]&1):this.s) == 0; }

// (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
function bnpExp(e,z) {
  if(e > 0xffffffff || e < 1) return BigInteger.ONE;
  var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e)-1;
  g.copyTo(r);
  while(--i >= 0) {
    z.sqrTo(r,r2);
    if((e&(1<<i)) > 0) z.mulTo(r2,g,r);
    else { var t = r; r = r2; r2 = t; }
  }
  return z.revert(r);
}

// (public) this^e % m, 0 <= e < 2^32
function bnModPowInt(e,m) {
  var z;
  if(e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
  return this.exp(e,z);
}

// protected
proto.copyTo = bnpCopyTo;
proto.fromInt = bnpFromInt;
proto.fromString = bnpFromString;
proto.clamp = bnpClamp;
proto.dlShiftTo = bnpDLShiftTo;
proto.drShiftTo = bnpDRShiftTo;
proto.lShiftTo = bnpLShiftTo;
proto.rShiftTo = bnpRShiftTo;
proto.subTo = bnpSubTo;
proto.multiplyTo = bnpMultiplyTo;
proto.squareTo = bnpSquareTo;
proto.divRemTo = bnpDivRemTo;
proto.invDigit = bnpInvDigit;
proto.isEven = bnpIsEven;
proto.exp = bnpExp;

// public
proto.toString = bnToString;
proto.negate = bnNegate;
proto.abs = bnAbs;
proto.compareTo = bnCompareTo;
proto.bitLength = bnBitLength;
proto.mod = bnMod;
proto.modPowInt = bnModPowInt;

//// jsbn2

function nbi() { return new BigInteger(null); }

// (public)
function bnClone() { var r = nbi(); this.copyTo(r); return r; }

// (public) return value as integer
function bnIntValue() {
  if(this.s < 0) {
    if(this.t == 1) return this[0]-this.DV;
    else if(this.t == 0) return -1;
  }
  else if(this.t == 1) return this[0];
  else if(this.t == 0) return 0;
  // assumes 16 < DB < 32
  return ((this[1]&((1<<(32-this.DB))-1))<<this.DB)|this[0];
}

// (public) return value as byte
function bnByteValue() { return (this.t==0)?this.s:(this[0]<<24)>>24; }

// (public) return value as short (assumes DB>=16)
function bnShortValue() { return (this.t==0)?this.s:(this[0]<<16)>>16; }

// (protected) return x s.t. r^x < DV
function bnpChunkSize(r) { return Math.floor(Math.LN2*this.DB/Math.log(r)); }

// (public) 0 if this == 0, 1 if this > 0
function bnSigNum() {
  if(this.s < 0) return -1;
  else if(this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
  else return 1;
}

// (protected) convert to radix string
function bnpToRadix(b) {
  if(b == null) b = 10;
  if(this.signum() == 0 || b < 2 || b > 36) return "0";
  var cs = this.chunkSize(b);
  var a = Math.pow(b,cs);
  var d = nbv(a), y = nbi(), z = nbi(), r = "";
  this.divRemTo(d,y,z);
  while(y.signum() > 0) {
    r = (a+z.intValue()).toString(b).substr(1) + r;
    y.divRemTo(d,y,z);
  }
  return z.intValue().toString(b) + r;
}

// (protected) convert from radix string
function bnpFromRadix(s,b) {
  var self = this;
  self.fromInt(0);
  if(b == null) b = 10;
  var cs = self.chunkSize(b);
  var d = Math.pow(b,cs), mi = false, j = 0, w = 0;
  for(var i = 0; i < s.length; ++i) {
    var x = intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-" && self.signum() == 0) mi = true;
      continue;
    }
    w = b*w+x;
    if(++j >= cs) {
      self.dMultiply(d);
      self.dAddOffset(w,0);
      j = 0;
      w = 0;
    }
  }
  if(j > 0) {
    self.dMultiply(Math.pow(b,j));
    self.dAddOffset(w,0);
  }
  if(mi) BigInteger.ZERO.subTo(self,self);
}

// (protected) alternate constructor
function bnpFromNumber(a,b,c) {
  var self = this;
  if("number" == typeof b) {
    // new BigInteger(int,int,RNG)
    if(a < 2) self.fromInt(1);
    else {
      self.fromNumber(a,c);
      if(!self.testBit(a-1))    // force MSB set
        self.bitwiseTo(BigInteger.ONE.shiftLeft(a-1),op_or,self);
      if(self.isEven()) self.dAddOffset(1,0); // force odd
      while(!self.isProbablePrime(b)) {
        self.dAddOffset(2,0);
        if(self.bitLength() > a) self.subTo(BigInteger.ONE.shiftLeft(a-1),self);
      }
    }
  }
  else {
    // new BigInteger(int,RNG)
    var x = new Array(), t = a&7;
    x.length = (a>>3)+1;
    b.nextBytes(x);
    if(t > 0) x[0] &= ((1<<t)-1); else x[0] = 0;
    self.fromString(x,256);
  }
}

// (public) convert to bigendian byte array
function bnToByteArray() {
  var self = this;
  var i = self.t, r = new Array();
  r[0] = self.s;
  var p = self.DB-(i*self.DB)%8, d, k = 0;
  if(i-- > 0) {
    if(p < self.DB && (d = self[i]>>p) != (self.s&self.DM)>>p)
      r[k++] = d|(self.s<<(self.DB-p));
    while(i >= 0) {
      if(p < 8) {
        d = (self[i]&((1<<p)-1))<<(8-p);
        d |= self[--i]>>(p+=self.DB-8);
      }
      else {
        d = (self[i]>>(p-=8))&0xff;
        if(p <= 0) { p += self.DB; --i; }
      }
      if((d&0x80) != 0) d |= -256;
      if(k === 0 && (self.s&0x80) != (d&0x80)) ++k;
      if(k > 0 || d != self.s) r[k++] = d;
    }
  }
  return r;
}

function bnEquals(a) { return(this.compareTo(a)==0); }
function bnMin(a) { return(this.compareTo(a)<0)?this:a; }
function bnMax(a) { return(this.compareTo(a)>0)?this:a; }

// (protected) r = this op a (bitwise)
function bnpBitwiseTo(a,op,r) {
  var self = this;
  var i, f, m = Math.min(a.t,self.t);
  for(i = 0; i < m; ++i) r[i] = op(self[i],a[i]);
  if(a.t < self.t) {
    f = a.s&self.DM;
    for(i = m; i < self.t; ++i) r[i] = op(self[i],f);
    r.t = self.t;
  }
  else {
    f = self.s&self.DM;
    for(i = m; i < a.t; ++i) r[i] = op(f,a[i]);
    r.t = a.t;
  }
  r.s = op(self.s,a.s);
  r.clamp();
}

// (public) this & a
function op_and(x,y) { return x&y; }
function bnAnd(a) { var r = nbi(); this.bitwiseTo(a,op_and,r); return r; }

// (public) this | a
function op_or(x,y) { return x|y; }
function bnOr(a) { var r = nbi(); this.bitwiseTo(a,op_or,r); return r; }

// (public) this ^ a
function op_xor(x,y) { return x^y; }
function bnXor(a) { var r = nbi(); this.bitwiseTo(a,op_xor,r); return r; }

// (public) this & ~a
function op_andnot(x,y) { return x&~y; }
function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a,op_andnot,r); return r; }

// (public) ~this
function bnNot() {
  var r = nbi();
  for(var i = 0; i < this.t; ++i) r[i] = this.DM&~this[i];
  r.t = this.t;
  r.s = ~this.s;
  return r;
}

// (public) this << n
function bnShiftLeft(n) {
  var r = nbi();
  if(n < 0) this.rShiftTo(-n,r); else this.lShiftTo(n,r);
  return r;
}

// (public) this >> n
function bnShiftRight(n) {
  var r = nbi();
  if(n < 0) this.lShiftTo(-n,r); else this.rShiftTo(n,r);
  return r;
}

// return index of lowest 1-bit in x, x < 2^31
function lbit(x) {
  if(x == 0) return -1;
  var r = 0;
  if((x&0xffff) == 0) { x >>= 16; r += 16; }
  if((x&0xff) == 0) { x >>= 8; r += 8; }
  if((x&0xf) == 0) { x >>= 4; r += 4; }
  if((x&3) == 0) { x >>= 2; r += 2; }
  if((x&1) == 0) ++r;
  return r;
}

// (public) returns index of lowest 1-bit (or -1 if none)
function bnGetLowestSetBit() {
  for(var i = 0; i < this.t; ++i)
    if(this[i] != 0) return i*this.DB+lbit(this[i]);
  if(this.s < 0) return this.t*this.DB;
  return -1;
}

// return number of 1 bits in x
function cbit(x) {
  var r = 0;
  while(x != 0) { x &= x-1; ++r; }
  return r;
}

// (public) return number of set bits
function bnBitCount() {
  var r = 0, x = this.s&this.DM;
  for(var i = 0; i < this.t; ++i) r += cbit(this[i]^x);
  return r;
}

// (public) true iff nth bit is set
function bnTestBit(n) {
  var j = Math.floor(n/this.DB);
  if(j >= this.t) return(this.s!=0);
  return((this[j]&(1<<(n%this.DB)))!=0);
}

// (protected) this op (1<<n)
function bnpChangeBit(n,op) {
  var r = BigInteger.ONE.shiftLeft(n);
  this.bitwiseTo(r,op,r);
  return r;
}

// (public) this | (1<<n)
function bnSetBit(n) { return this.changeBit(n,op_or); }

// (public) this & ~(1<<n)
function bnClearBit(n) { return this.changeBit(n,op_andnot); }

// (public) this ^ (1<<n)
function bnFlipBit(n) { return this.changeBit(n,op_xor); }

// (protected) r = this + a
function bnpAddTo(a,r) {
  var self = this;

  var i = 0, c = 0, m = Math.min(a.t,self.t);
  while(i < m) {
    c += self[i]+a[i];
    r[i++] = c&self.DM;
    c >>= self.DB;
  }
  if(a.t < self.t) {
    c += a.s;
    while(i < self.t) {
      c += self[i];
      r[i++] = c&self.DM;
      c >>= self.DB;
    }
    c += self.s;
  }
  else {
    c += self.s;
    while(i < a.t) {
      c += a[i];
      r[i++] = c&self.DM;
      c >>= self.DB;
    }
    c += a.s;
  }
  r.s = (c<0)?-1:0;
  if(c > 0) r[i++] = c;
  else if(c < -1) r[i++] = self.DV+c;
  r.t = i;
  r.clamp();
}

// (public) this + a
function bnAdd(a) { var r = nbi(); this.addTo(a,r); return r; }

// (public) this - a
function bnSubtract(a) { var r = nbi(); this.subTo(a,r); return r; }

// (public) this * a
function bnMultiply(a) { var r = nbi(); this.multiplyTo(a,r); return r; }

// (public) this^2
function bnSquare() { var r = nbi(); this.squareTo(r); return r; }

// (public) this / a
function bnDivide(a) { var r = nbi(); this.divRemTo(a,r,null); return r; }

// (public) this % a
function bnRemainder(a) { var r = nbi(); this.divRemTo(a,null,r); return r; }

// (public) [this/a,this%a]
function bnDivideAndRemainder(a) {
  var q = nbi(), r = nbi();
  this.divRemTo(a,q,r);
  return new Array(q,r);
}

// (protected) this *= n, this >= 0, 1 < n < DV
function bnpDMultiply(n) {
  this[this.t] = this.am(0,n-1,this,0,0,this.t);
  ++this.t;
  this.clamp();
}

// (protected) this += n << w words, this >= 0
function bnpDAddOffset(n,w) {
  if(n == 0) return;
  while(this.t <= w) this[this.t++] = 0;
  this[w] += n;
  while(this[w] >= this.DV) {
    this[w] -= this.DV;
    if(++w >= this.t) this[this.t++] = 0;
    ++this[w];
  }
}

// A "null" reducer
function NullExp() {}
function nNop(x) { return x; }
function nMulTo(x,y,r) { x.multiplyTo(y,r); }
function nSqrTo(x,r) { x.squareTo(r); }

NullExp.prototype.convert = nNop;
NullExp.prototype.revert = nNop;
NullExp.prototype.mulTo = nMulTo;
NullExp.prototype.sqrTo = nSqrTo;

// (public) this^e
function bnPow(e) { return this.exp(e,new NullExp()); }

// (protected) r = lower n words of "this * a", a.t <= n
// "this" should be the larger one if appropriate.
function bnpMultiplyLowerTo(a,n,r) {
  var i = Math.min(this.t+a.t,n);
  r.s = 0; // assumes a,this >= 0
  r.t = i;
  while(i > 0) r[--i] = 0;
  var j;
  for(j = r.t-this.t; i < j; ++i) r[i+this.t] = this.am(0,a[i],r,i,0,this.t);
  for(j = Math.min(a.t,n); i < j; ++i) this.am(0,a[i],r,i,0,n-i);
  r.clamp();
}

// (protected) r = "this * a" without lower n words, n > 0
// "this" should be the larger one if appropriate.
function bnpMultiplyUpperTo(a,n,r) {
  --n;
  var i = r.t = this.t+a.t-n;
  r.s = 0; // assumes a,this >= 0
  while(--i >= 0) r[i] = 0;
  for(i = Math.max(n-this.t,0); i < a.t; ++i)
    r[this.t+i-n] = this.am(n-i,a[i],r,0,0,this.t+i-n);
  r.clamp();
  r.drShiftTo(1,r);
}

// Barrett modular reduction
function Barrett(m) {
  // setup Barrett
  this.r2 = nbi();
  this.q3 = nbi();
  BigInteger.ONE.dlShiftTo(2*m.t,this.r2);
  this.mu = this.r2.divide(m);
  this.m = m;
}

function barrettConvert(x) {
  if(x.s < 0 || x.t > 2*this.m.t) return x.mod(this.m);
  else if(x.compareTo(this.m) < 0) return x;
  else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
}

function barrettRevert(x) { return x; }

// x = x mod m (HAC 14.42)
function barrettReduce(x) {
  var self = this;
  x.drShiftTo(self.m.t-1,self.r2);
  if(x.t > self.m.t+1) { x.t = self.m.t+1; x.clamp(); }
  self.mu.multiplyUpperTo(self.r2,self.m.t+1,self.q3);
  self.m.multiplyLowerTo(self.q3,self.m.t+1,self.r2);
  while(x.compareTo(self.r2) < 0) x.dAddOffset(1,self.m.t+1);
  x.subTo(self.r2,x);
  while(x.compareTo(self.m) >= 0) x.subTo(self.m,x);
}

// r = x^2 mod m; x != r
function barrettSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = x*y mod m; x,y != r
function barrettMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Barrett.prototype.convert = barrettConvert;
Barrett.prototype.revert = barrettRevert;
Barrett.prototype.reduce = barrettReduce;
Barrett.prototype.mulTo = barrettMulTo;
Barrett.prototype.sqrTo = barrettSqrTo;

// (public) this^e % m (HAC 14.85)
function bnModPow(e,m) {
  var i = e.bitLength(), k, r = nbv(1), z;
  if(i <= 0) return r;
  else if(i < 18) k = 1;
  else if(i < 48) k = 3;
  else if(i < 144) k = 4;
  else if(i < 768) k = 5;
  else k = 6;
  if(i < 8)
    z = new Classic(m);
  else if(m.isEven())
    z = new Barrett(m);
  else
    z = new Montgomery(m);

  // precomputation
  var g = new Array(), n = 3, k1 = k-1, km = (1<<k)-1;
  g[1] = z.convert(this);
  if(k > 1) {
    var g2 = nbi();
    z.sqrTo(g[1],g2);
    while(n <= km) {
      g[n] = nbi();
      z.mulTo(g2,g[n-2],g[n]);
      n += 2;
    }
  }

  var j = e.t-1, w, is1 = true, r2 = nbi(), t;
  i = nbits(e[j])-1;
  while(j >= 0) {
    if(i >= k1) w = (e[j]>>(i-k1))&km;
    else {
      w = (e[j]&((1<<(i+1))-1))<<(k1-i);
      if(j > 0) w |= e[j-1]>>(this.DB+i-k1);
    }

    n = k;
    while((w&1) == 0) { w >>= 1; --n; }
    if((i -= n) < 0) { i += this.DB; --j; }
    if(is1) {   // ret == 1, don't bother squaring or multiplying it
      g[w].copyTo(r);
      is1 = false;
    }
    else {
      while(n > 1) { z.sqrTo(r,r2); z.sqrTo(r2,r); n -= 2; }
      if(n > 0) z.sqrTo(r,r2); else { t = r; r = r2; r2 = t; }
      z.mulTo(r2,g[w],r);
    }

    while(j >= 0 && (e[j]&(1<<i)) == 0) {
      z.sqrTo(r,r2); t = r; r = r2; r2 = t;
      if(--i < 0) { i = this.DB-1; --j; }
    }
  }
  return z.revert(r);
}

// (public) gcd(this,a) (HAC 14.54)
function bnGCD(a) {
  var x = (this.s<0)?this.negate():this.clone();
  var y = (a.s<0)?a.negate():a.clone();
  if(x.compareTo(y) < 0) { var t = x; x = y; y = t; }
  var i = x.getLowestSetBit(), g = y.getLowestSetBit();
  if(g < 0) return x;
  if(i < g) g = i;
  if(g > 0) {
    x.rShiftTo(g,x);
    y.rShiftTo(g,y);
  }
  while(x.signum() > 0) {
    if((i = x.getLowestSetBit()) > 0) x.rShiftTo(i,x);
    if((i = y.getLowestSetBit()) > 0) y.rShiftTo(i,y);
    if(x.compareTo(y) >= 0) {
      x.subTo(y,x);
      x.rShiftTo(1,x);
    }
    else {
      y.subTo(x,y);
      y.rShiftTo(1,y);
    }
  }
  if(g > 0) y.lShiftTo(g,y);
  return y;
}

// (protected) this % n, n < 2^26
function bnpModInt(n) {
  if(n <= 0) return 0;
  var d = this.DV%n, r = (this.s<0)?n-1:0;
  if(this.t > 0)
    if(d == 0) r = this[0]%n;
    else for(var i = this.t-1; i >= 0; --i) r = (d*r+this[i])%n;
  return r;
}

// (public) 1/this % m (HAC 14.61)
function bnModInverse(m) {
  var ac = m.isEven();
  if((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
  var u = m.clone(), v = this.clone();
  var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
  while(u.signum() != 0) {
    while(u.isEven()) {
      u.rShiftTo(1,u);
      if(ac) {
        if(!a.isEven() || !b.isEven()) { a.addTo(this,a); b.subTo(m,b); }
        a.rShiftTo(1,a);
      }
      else if(!b.isEven()) b.subTo(m,b);
      b.rShiftTo(1,b);
    }
    while(v.isEven()) {
      v.rShiftTo(1,v);
      if(ac) {
        if(!c.isEven() || !d.isEven()) { c.addTo(this,c); d.subTo(m,d); }
        c.rShiftTo(1,c);
      }
      else if(!d.isEven()) d.subTo(m,d);
      d.rShiftTo(1,d);
    }
    if(u.compareTo(v) >= 0) {
      u.subTo(v,u);
      if(ac) a.subTo(c,a);
      b.subTo(d,b);
    }
    else {
      v.subTo(u,v);
      if(ac) c.subTo(a,c);
      d.subTo(b,d);
    }
  }
  if(v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
  if(d.compareTo(m) >= 0) return d.subtract(m);
  if(d.signum() < 0) d.addTo(m,d); else return d;
  if(d.signum() < 0) return d.add(m); else return d;
}

// protected
proto.chunkSize = bnpChunkSize;
proto.toRadix = bnpToRadix;
proto.fromRadix = bnpFromRadix;
proto.fromNumber = bnpFromNumber;
proto.bitwiseTo = bnpBitwiseTo;
proto.changeBit = bnpChangeBit;
proto.addTo = bnpAddTo;
proto.dMultiply = bnpDMultiply;
proto.dAddOffset = bnpDAddOffset;
proto.multiplyLowerTo = bnpMultiplyLowerTo;
proto.multiplyUpperTo = bnpMultiplyUpperTo;
proto.modInt = bnpModInt;

// public
proto.clone = bnClone;
proto.intValue = bnIntValue;
proto.byteValue = bnByteValue;
proto.shortValue = bnShortValue;
proto.signum = bnSigNum;
proto.toByteArray = bnToByteArray;
proto.equals = bnEquals;
proto.min = bnMin;
proto.max = bnMax;
proto.and = bnAnd;
proto.or = bnOr;
proto.xor = bnXor;
proto.andNot = bnAndNot;
proto.not = bnNot;
proto.shiftLeft = bnShiftLeft;
proto.shiftRight = bnShiftRight;
proto.getLowestSetBit = bnGetLowestSetBit;
proto.bitCount = bnBitCount;
proto.testBit = bnTestBit;
proto.setBit = bnSetBit;
proto.clearBit = bnClearBit;
proto.flipBit = bnFlipBit;
proto.add = bnAdd;
proto.subtract = bnSubtract;
proto.multiply = bnMultiply;
proto.divide = bnDivide;
proto.remainder = bnRemainder;
proto.divideAndRemainder = bnDivideAndRemainder;
proto.modPow = bnModPow;
proto.modInverse = bnModInverse;
proto.pow = bnPow;
proto.gcd = bnGCD;

// JSBN-specific extension
proto.square = bnSquare;

// BigInteger interfaces not implemented in jsbn:

// BigInteger(int signum, byte[] magnitude)
// double doubleValue()
// float floatValue()
// int hashCode()
// long longValue()
// static BigInteger valueOf(long val)

// "constants"
BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);
BigInteger.valueOf = nbv;


/// bitcoinjs addons

/**
 * Turns a byte array into a big integer.
 *
 * This function will interpret a byte array as a big integer in big
 * endian notation and ignore leading zeros.
 */
BigInteger.fromByteArrayUnsigned = function(ba) {
  if (!ba.length) {
    return new BigInteger.valueOf(0);
  } else if (ba[0] & 0x80) {
    // Prepend a zero so the BigInteger class doesn't mistake this
    // for a negative integer.
    return new BigInteger([0].concat(ba));
  } else {
    return new BigInteger(ba);
  }
};

/**
 * Parse a signed big integer byte representation.
 *
 * For details on the format please see BigInteger.toByteArraySigned.
 */
BigInteger.fromByteArraySigned = function(ba) {
  // Check for negative value
  if (ba[0] & 0x80) {
    // Remove sign bit
    ba[0] &= 0x7f;

    return BigInteger.fromByteArrayUnsigned(ba).negate();
  } else {
    return BigInteger.fromByteArrayUnsigned(ba);
  }
};

/**
 * Returns a byte array representation of the big integer.
 *
 * This returns the absolute of the contained value in big endian
 * form. A value of zero results in an empty array.
 */
BigInteger.prototype.toByteArrayUnsigned = function() {
    var ba = this.abs().toByteArray();

    // Empty array, nothing to do
    if (!ba.length) {
        return ba;
    }

    // remove leading 0
    if (ba[0] === 0) {
        ba = ba.slice(1);
    }

    // all values must be positive
    for (var i=0 ; i<ba.length ; ++i) {
      ba[i] = (ba[i] < 0) ? ba[i] + 256 : ba[i];
    }

    return ba;
};

/*
 * Converts big integer to signed byte representation.
 *
 * The format for this value uses the most significant bit as a sign
 * bit. If the most significant bit is already occupied by the
 * absolute value, an extra byte is prepended and the sign bit is set
 * there.
 *
 * Examples:
 *
 *      0 =>     0x00
 *      1 =>     0x01
 *     -1 =>     0x81
 *    127 =>     0x7f
 *   -127 =>     0xff
 *    128 =>   0x0080
 *   -128 =>   0x8080
 *    255 =>   0x00ff
 *   -255 =>   0x80ff
 *  16300 =>   0x3fac
 * -16300 =>   0xbfac
 *  62300 => 0x00f35c
 * -62300 => 0x80f35c
*/
BigInteger.prototype.toByteArraySigned = function() {
  var val = this.toByteArrayUnsigned();
  var neg = this.s < 0;

  // if the first bit is set, we always unshift
  // either unshift 0x80 or 0x00
  if (val[0] & 0x80) {
    val.unshift((neg) ? 0x80 : 0x00);
  }
  // if the first bit isn't set, set it if negative
  else if (neg) {
    val[0] |= 0x80;
  }

  return val;
};


if (typeof module !== 'undefined' && module.exports) { //CommonJS
  module.exports = BigInteger
} else {
  globals.BigInteger = BigInteger
}

}(this);

},{}],3:[function(require,module,exports){
// shim for using process in browser

var process = module.exports = {};

process.nextTick = (function () {
    var canSetImmediate = typeof window !== 'undefined'
    && window.setImmediate;
    var canPost = typeof window !== 'undefined'
    && window.postMessage && window.addEventListener
    ;

    if (canSetImmediate) {
        return function (f) { return window.setImmediate(f) };
    }

    if (canPost) {
        var queue = [];
        window.addEventListener('message', function (ev) {
            if (ev.source === window && ev.data === 'process-tick') {
                ev.stopPropagation();
                if (queue.length > 0) {
                    var fn = queue.shift();
                    fn();
                }
            }
        }, true);

        return function nextTick(fn) {
            queue.push(fn);
            window.postMessage('process-tick', '*');
        };
    }

    return function nextTick(fn) {
        setTimeout(fn, 0);
    };
})();

process.title = 'browser';
process.browser = true;
process.env = {};
process.argv = [];

process.binding = function (name) {
    throw new Error('process.binding is not supported');
}

// TODO(shtylman)
process.cwd = function () { return '/' };
process.chdir = function (dir) {
    throw new Error('process.chdir is not supported');
};

},{}],4:[function(require,module,exports){
!function(globals) {
'use strict'

var BigInteger = null
var base58 = {} //exports

if (typeof module !== 'undefined' && module.exports) { //CommonJS
  BigInteger = require('bigi')
  module.exports = base58
} else {
  BigInteger = globals.BigInteger
  globals.bs58 = base58
}


var alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
var base = BigInteger.valueOf(58);

var positions = {};
for (var i=0 ; i < alphabet.length ; ++i) {
    positions[alphabet[i]] = i;
}

// Convert a byte array to a base58-encoded string.
// Written by Mike Hearn for BitcoinJ.
//   Copyright (c) 2011 Google Inc.
// Ported to JavaScript by Stefan Thomas.
base58.encode = function (input) {
    var bi = BigInteger.fromByteArrayUnsigned(input);
    var chars = [];

    while (bi.compareTo(base) >= 0) {
        var mod = bi.mod(base);
        chars.push(alphabet[mod.intValue()]);
        bi = bi.subtract(mod).divide(base);
    }
    chars.push(alphabet[bi.intValue()]);

    // Convert leading zeros too.
    for (var i = 0; i < input.length; i++) {
        if (input[i] == 0x00) {
            chars.push(alphabet[0]);
        } else break;
    }

    return chars.reverse().join('');
}

// decode a base58 string into a byte array
// input should be a base58 encoded string
// @return Array
base58.decode = function (input) {

  var base = BigInteger.valueOf(58);

  var length = input.length;
  var num = BigInteger.valueOf(0);
  var leading_zero = 0;
  var seen_other = false;
  for (var i=0; i<length ; ++i) {
      var char = input[i];
      var p = positions[char];

      // if we encounter an invalid character, decoding fails
      if (p === undefined) {
          throw new Error('invalid base58 string: ' + input);
      }

      num = num.multiply(base).add(BigInteger.valueOf(p));

      if (char == '1' && !seen_other) {
          ++leading_zero;
      }
      else {
          seen_other = true;
      }
  }

  var bytes = num.toByteArrayUnsigned();

  // remove leading zeros
  while (leading_zero-- > 0) {
      bytes.unshift(0);
  }

  return bytes;
}


}(this);
},{"bigi":2}],5:[function(require,module,exports){
!function(globals) {
'use strict'

var _imports = {}

if (typeof module !== 'undefined' && module.exports) { //CommonJS
  _imports.sha256 = require('sha256')
  _imports.base58 = require('bs58')
  module.exports = Address
} else {
  _imports.sha256 = globals.sha256
  _imports.base58 = globals.bs58
  globals.Address = Address
}


var address_types = {
    prod: 0,
    testnet: 111
};

var p2sh_types = {
    prod: 5,
    testnet: 196
};

function Address (bytes, address_type) {
  if (typeof bytes === 'string') {
    this.decodeString(bytes, address_type);
  } else {
    this.hash = bytes;
    this.version = address_types[address_type || 'prod'];
  }
};

/**
 * Serialize this object as a standard Bitcoin address.
 *
 * Returns the address as a base58-encoded string in the standardized format.
 */
Address.prototype.toString = function () {
  // Get a copy of the hash
  var hash = this.hash.slice(0);

  // Version
  hash.unshift(this.version);

  var checksum = _imports.sha256(_imports.sha256(hash, {asBytes: true}), {asBytes: true});

  var bytes = hash.concat(checksum.slice(0,4));

  return _imports.base58.encode(bytes);
};


Address.validateType = function(version, type) {
  if (type) {
    return (version === address_types[type] || version === p2sh_types[type]);
  }
  for (var type in address_types) {
    if (version == address_types[type]) {
      return true;
    }
  }
  for (var type in p2sh_types) {
    if (version == p2sh_types[type]) {
      return true;
    }
  }
  return false;
};

// TODO(shtylman) isValid?
Address.validate = function(string, type) {
  try {
    var bytes = _imports.base58.decode(string);
  } catch (e) {
    return false;
  }

  var hash = bytes.slice(0, 21);

  var checksum = _imports.sha256(_imports.sha256(hash, {asBytes: true}), {asBytes: true});

  if (checksum[0] != bytes[21] ||
      checksum[1] != bytes[22] ||
      checksum[2] != bytes[23] ||
      checksum[3] != bytes[24]) {
    return false;
  }

  if (!Address.validateType(hash[0], type)) {
    return false;
  }

  return true;
};

/**
 * Parse a Bitcoin address contained in a string.
 */
Address.prototype.decodeString = function(string, address_type) {
  var bytes = _imports.base58.decode(string);

  var hash = bytes.slice(0, 21);

  var checksum = _imports.sha256(_imports.sha256(hash, {asBytes: true}), {asBytes: true});

  if (checksum[0] != bytes[21] ||
      checksum[1] != bytes[22] ||
      checksum[2] != bytes[23] ||
      checksum[3] != bytes[24]) {
    throw new Error('Address Checksum validation failed: ' + string);
  }

  var version = hash.shift();
  if (!Address.validateType(version, address_type)) {
    throw new Error('Address version (' + version + ') not supported: ' + string +
                    ' for ' + address_type);
  }

  this.hash = hash;
  this.version = version;
};

}(this);
},{"bs58":4,"sha256":17}],6:[function(require,module,exports){
!function(globals) {
'use strict'

var convertHex = {
  bytesToHex: function(bytes) {
    /*if (typeof bytes.byteLength != 'undefined') {
      var newBytes = []

      if (typeof bytes.buffer != 'undefined')
        bytes = new DataView(bytes.buffer)
      else
        bytes = new DataView(bytes)

      for (var i = 0; i < bytes.byteLength; ++i) {
        newBytes.push(bytes.getUint8(i))
      }
      bytes = newBytes
    }*/
    return arrBytesToHex(bytes)
  },
  hexToBytes: function(hex) {
    if (hex.length % 2 === 1) throw new Error("hexToBytes can't have a string with an odd number of characters.")
    if (hex.indexOf('0x') === 0) hex = hex.slice(2)
    return hex.match(/../g).map(function(x) { return parseInt(x,16) })
  }
}


// PRIVATE

function arrBytesToHex(bytes) {
  return bytes.map(function(x) { return padLeft(x.toString(16),2) }).join('')
}

function padLeft(orig, len) {
  if (orig.length > len) return orig
  return Array(len - orig.length + 1).join('0') + orig
}


if (typeof module !== 'undefined' && module.exports) { //CommonJS
  module.exports = convertHex
} else {
  globals.convertHex = convertHex
}

}(this);
},{}],7:[function(require,module,exports){
!function(globals) {
'use strict'

//*** IMPORTS
var BigInteger = null
var ECPointFp = null
var ecparams = null
var secureRandom = null
//*** IMPORTS END

//*** EXPORTS
var ECDSA = {}

if (typeof module !== 'undefined' && module.exports) { //CommonJS
  secureRandom = require('secure-random') //same name for both
  ECPointFp = require('ecurve').ECPointFp
  ecparams = require('ecurve-names')('secp256k1')
  BigInteger = require('bigi')
  module.exports = ECDSA
} else {
  BigInteger = globals.BigInteger
  secureRandom = globals.secureRandom
  ECPointFp = globals.ECCurveFp.ECPointFp
  ecparams = globals.getSECCurveByName('secp256k1')
  globals.ECDSA = ECDSA
}



//var SecureRandom = require('./jsbn/rng');
//var rng = new SecureRandom();
var rng = { //for cryptocoin-bigint AKA jsbn
  nextBytes: function(arr) {
    var byteArr = secureRandom(arr.length)
    for (var i = 0; i < byteArr.length; ++i) 
      arr[i] = byteArr[i]
  }
}


var P_OVER_FOUR = null;

function implShamirsTrick(P, k, Q, l)
{
  var m = Math.max(k.bitLength(), l.bitLength());
  var Z = P.add2D(Q);
  var R = P.curve.getInfinity();

  for (var i = m - 1; i >= 0; --i) {
    R = R.twice2D();

    R.z = BigInteger.ONE;

    if (k.testBit(i)) {
      if (l.testBit(i)) {
        R = R.add2D(Z);
      } else {
        R = R.add2D(P);
      }
    } else {
      if (l.testBit(i)) {
        R = R.add2D(Q);
      }
    }
  }

  return R;
};

  
ECDSA.getBigRandom = function (limit) {
    return new BigInteger(limit.bitLength(), rng)
      .mod(limit.subtract(BigInteger.ONE))
      .add(BigInteger.ONE)
    ;
}
  
ECDSA.sign = function (hash, priv) {
    var d = priv;
    var n = ecparams.getN();
    var e = BigInteger.fromByteArrayUnsigned(hash);

    do {
      var k = ECDSA.getBigRandom(n);
      var G = ecparams.getG();
      var Q = G.multiply(k);
      var r = Q.getX().toBigInteger().mod(n);
    } while (r.compareTo(BigInteger.ZERO) <= 0);

    var s = k.modInverse(n).multiply(e.add(d.multiply(r))).mod(n);

    return ECDSA.serializeSig(r, s);
}

ECDSA.verify = function (hash, sig, pubkey) {
    var r,s;
    if (Array.isArray(sig)) {
      var obj = ECDSA.parseSig(sig);
      r = obj.r;
      s = obj.s;
    } else if ("object" === typeof sig && sig.r && sig.s) {
      r = sig.r;
      s = sig.s;
    } else {
      throw new Error("Invalid value for signature");
    }

    var Q;
    if (pubkey instanceof ECPointFp) {
      Q = pubkey;
    } else if (Array.isArray(pubkey)) {
      Q = ECPointFp.decodeFrom(ecparams.getCurve(), pubkey);
    } else {
      throw new Error("Invalid format for pubkey value, must be byte array or ECPointFp");
    }
    var e = BigInteger.fromByteArrayUnsigned(hash);

    return ECDSA.verifyRaw(e, r, s, Q);
}

ECDSA.verifyRaw = function (e, r, s, Q) {
    var n = ecparams.getN();
    var G = ecparams.getG();

    if (r.compareTo(BigInteger.ONE) < 0 ||
        r.compareTo(n) >= 0)
      return false;

    if (s.compareTo(BigInteger.ONE) < 0 ||
        s.compareTo(n) >= 0)
      return false;

    var c = s.modInverse(n);

    var u1 = e.multiply(c).mod(n);
    var u2 = r.multiply(c).mod(n);

    // TODO(!!!): For some reason Shamir's trick isn't working with
    // signed message verification!? Probably an implementation
    // error!
    //var point = implShamirsTrick(G, u1, Q, u2);
    var point = G.multiply(u1).add(Q.multiply(u2));

    var v = point.getX().toBigInteger().mod(n);

    return v.equals(r);
}

  /**
   * Serialize a signature into DER format.
   *
   * Takes two BigIntegers representing r and s and returns a byte array.
   */
ECDSA.serializeSig = function (r, s) {
    var rBa = r.toByteArraySigned();
    var sBa = s.toByteArraySigned();

    var sequence = [];
    sequence.push(0x02); // INTEGER
    sequence.push(rBa.length);
    sequence = sequence.concat(rBa);

    sequence.push(0x02); // INTEGER
    sequence.push(sBa.length);
    sequence = sequence.concat(sBa);

    sequence.unshift(sequence.length);
    sequence.unshift(0x30); // SEQUENCE

    return sequence;
}

  /**
   * Parses a byte array containing a DER-encoded signature.
   *
   * This function will return an object of the form:
   *
   * {
   *   r: BigInteger,
   *   s: BigInteger
   * }
   */
ECDSA.parseSig = function (sig) {
    var cursor;
    if (sig[0] != 0x30)
      throw new Error("Signature not a valid DERSequence");

    cursor = 2;
    if (sig[cursor] != 0x02)
      throw new Error("First element in signature must be a DERInteger");;
    var rBa = sig.slice(cursor+2, cursor+2+sig[cursor+1]);

    cursor += 2+sig[cursor+1];
    if (sig[cursor] != 0x02)
      throw new Error("Second element in signature must be a DERInteger");
    var sBa = sig.slice(cursor+2, cursor+2+sig[cursor+1]);

    cursor += 2+sig[cursor+1];

    //if (cursor != sig.length)
    //  throw new Error("Extra bytes in signature");

    var r = BigInteger.fromByteArrayUnsigned(rBa);
    var s = BigInteger.fromByteArrayUnsigned(sBa);

    return {r: r, s: s};
}

ECDSA.parseSigCompact = function (sig) {
    if (sig.length !== 65) {
      throw new Error("Signature has the wrong length");
    }

    // Signature is prefixed with a type byte storing three bits of
    // information.
    var i = sig[0] - 27;
    if (i < 0 || i > 7) {
      throw new Error("Invalid signature type");
    }

    var n = ecparams.getN();
    var r = BigInteger.fromByteArrayUnsigned(sig.slice(1, 33)).mod(n);
    var s = BigInteger.fromByteArrayUnsigned(sig.slice(33, 65)).mod(n);

    return {r: r, s: s, i: i};
}



  /**
   * Calculate pubkey extraction parameter.
   *
   * When extracting a pubkey from a signature, we have to
   * distinguish four different cases. Rather than putting this
   * burden on the verifier, Bitcoin includes a 2-bit value with the
   * signature.
   *
   * This function simply tries all four cases and returns the value
   * that resulted in a successful pubkey recovery.
   */
ECDSA.calcPubkeyRecoveryParam = function (address, r, s, hash)
  {
    for (var i = 0; i < 4; i++) {
      var pubkey = ECDSA.recoverPubKey(r, s, hash, i);
      if (pubkey.getBitcoinAddress().toString() == address) {
        return i;
      }
    }

    throw new Error("Unable to find valid recovery factor");
  }



}(this);

},{"bigi":2,"ecurve":9,"ecurve-names":8,"secure-random":10}],8:[function(require,module,exports){
!function(globals) {
'use strict'

var BigInteger = null
var ECCurveFp = null

 if (typeof module !== 'undefined' && module.exports) { //CommonJS
  ECCurveFp = require('ecurve')
    BigInteger = require('bigi')
  module.exports = getSECCurveByName
} else {
  BigInteger = globals.BigInteger
  ECCurveFp = globals.ECCurveFp
  globals.getSECCurveByName = getSECCurveByName
}


// Named EC curves

// ----------------
// X9ECParameters

// constructor
function X9ECParameters(curve,g,n,h) {
    this.curve = curve;
    this.g = g;
    this.n = n;
    this.h = h;
}

function x9getCurve() {
    return this.curve;
}

function x9getG() {
    return this.g;
}

function x9getN() {
    return this.n;
}

function x9getH() {
    return this.h;
}

X9ECParameters.prototype.getCurve = x9getCurve;
X9ECParameters.prototype.getG = x9getG;
X9ECParameters.prototype.getN = x9getN;
X9ECParameters.prototype.getH = x9getH;

// ----------------
// SECNamedCurves

function fromHex(s) { return new BigInteger(s, 16); }

function secp128r1() {
    // p = 2^128 - 2^97 - 1
    var p = fromHex("FFFFFFFDFFFFFFFFFFFFFFFFFFFFFFFF");
    var a = fromHex("FFFFFFFDFFFFFFFFFFFFFFFFFFFFFFFC");
    var b = fromHex("E87579C11079F43DD824993C2CEE5ED3");
    //byte[] S = Hex.decode("000E0D4D696E6768756151750CC03A4473D03679");
    var n = fromHex("FFFFFFFE0000000075A30D1B9038A115");
    var h = BigInteger.ONE;
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04"
                + "161FF7528B899B2D0C28607CA52C5B86"
    + "CF5AC8395BAFEB13C02DA292DDED7A83");
    return new X9ECParameters(curve, G, n, h);
}

function secp160k1() {
    // p = 2^160 - 2^32 - 2^14 - 2^12 - 2^9 - 2^8 - 2^7 - 2^3 - 2^2 - 1
    var p = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFAC73");
    var a = BigInteger.ZERO;
    var b = fromHex("7");
    //byte[] S = null;
    var n = fromHex("0100000000000000000001B8FA16DFAB9ACA16B6B3");
    var h = BigInteger.ONE;
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04"
                + "3B4C382CE37AA192A4019E763036F4F5DD4D7EBB"
                + "938CF935318FDCED6BC28286531733C3F03C4FEE");
    return new X9ECParameters(curve, G, n, h);
}

function secp160r1() {
    // p = 2^160 - 2^31 - 1
    var p = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7FFFFFFF");
    var a = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF7FFFFFFC");
    var b = fromHex("1C97BEFC54BD7A8B65ACF89F81D4D4ADC565FA45");
    //byte[] S = Hex.decode("1053CDE42C14D696E67687561517533BF3F83345");
    var n = fromHex("0100000000000000000001F4C8F927AED3CA752257");
    var h = BigInteger.ONE;
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04"
    + "4A96B5688EF573284664698968C38BB913CBFC82"
    + "23A628553168947D59DCC912042351377AC5FB32");
    return new X9ECParameters(curve, G, n, h);
}

function secp192k1() {
    // p = 2^192 - 2^32 - 2^12 - 2^8 - 2^7 - 2^6 - 2^3 - 1
    var p = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFEE37");
    var a = BigInteger.ZERO;
    var b = fromHex("3");
    //byte[] S = null;
    var n = fromHex("FFFFFFFFFFFFFFFFFFFFFFFE26F2FC170F69466A74DEFD8D");
    var h = BigInteger.ONE;
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04"
                + "DB4FF10EC057E9AE26B07D0280B7F4341DA5D1B1EAE06C7D"
                + "9B2F2F6D9C5628A7844163D015BE86344082AA88D95E2F9D");
    return new X9ECParameters(curve, G, n, h);
}

function secp192r1() {
    // p = 2^192 - 2^64 - 1
    var p = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFF");
    var a = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFC");
    var b = fromHex("64210519E59C80E70FA7E9AB72243049FEB8DEECC146B9B1");
    //byte[] S = Hex.decode("3045AE6FC8422F64ED579528D38120EAE12196D5");
    var n = fromHex("FFFFFFFFFFFFFFFFFFFFFFFF99DEF836146BC9B1B4D22831");
    var h = BigInteger.ONE;
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04"
                + "188DA80EB03090F67CBF20EB43A18800F4FF0AFD82FF1012"
                + "07192B95FFC8DA78631011ED6B24CDD573F977A11E794811");
    return new X9ECParameters(curve, G, n, h);
}

function secp224r1() {
    // p = 2^224 - 2^96 + 1
    var p = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF000000000000000000000001");
    var a = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFE");
    var b = fromHex("B4050A850C04B3ABF54132565044B0B7D7BFD8BA270B39432355FFB4");
    //byte[] S = Hex.decode("BD71344799D5C7FCDC45B59FA3B9AB8F6A948BC5");
    var n = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFF16A2E0B8F03E13DD29455C5C2A3D");
    var h = BigInteger.ONE;
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04"
                + "B70E0CBD6BB4BF7F321390B94A03C1D356C21122343280D6115C1D21"
                + "BD376388B5F723FB4C22DFE6CD4375A05A07476444D5819985007E34");
    return new X9ECParameters(curve, G, n, h);
}

function secp256k1() {
    // p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
    var p = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F");
    var a = BigInteger.ZERO;
    var b = fromHex("7");
    //byte[] S = null;
    var n = fromHex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
    var h = BigInteger.ONE;
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04"
                + "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"
              + "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8");
    return new X9ECParameters(curve, G, n, h);
}

function secp256r1() {
    // p = 2^224 (2^32 - 1) + 2^192 + 2^96 - 1
    var p = fromHex("FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF");
    var a = fromHex("FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFC");
    var b = fromHex("5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B");
    //byte[] S = Hex.decode("C49D360886E704936A6678E1139D26B7819F7E90");
    var n = fromHex("FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551");
    var h = BigInteger.ONE;
    var curve = new ECCurveFp(p, a, b);
    var G = curve.decodePointHex("04"
                + "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"
    + "4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5");
    return new X9ECParameters(curve, G, n, h);
}

// TODO: make this into a proper hashtable
function getSECCurveByName(name) {
    if(name == "secp128r1") return secp128r1();
    if(name == "secp160k1") return secp160k1();
    if(name == "secp160r1") return secp160r1();
    if(name == "secp192k1") return secp192k1();
    if(name == "secp192r1") return secp192r1();
    if(name == "secp224r1") return secp224r1();
    if(name == "secp256k1") return secp256k1();
    if(name == "secp256r1") return secp256r1();
    return null;
}

}(this);

},{"bigi":2,"ecurve":9}],9:[function(require,module,exports){
!function(globals) {
'use strict'

var BigInteger = null

if (typeof module !== 'undefined' && module.exports) { //CommonJS
  BigInteger = require('bigi')
  module.exports = ECCurveFp
} else {
  BigInteger = globals.BigInteger
  globals.ECCurveFp = ECCurveFp
}


// Basic Javascript Elliptic Curve implementation
// Ported loosely from BouncyCastle's Java EC code
// Only Fp curves implemented for now

// ----------------
// ECFieldElementFp

// constructor
function ECFieldElementFp(q,x) {
    this.x = x;
    // TODO if(x.compareTo(q) >= 0) error
    this.q = q;
}

function feFpEquals(other) {
    if(other == this) return true;
    return (this.q.equals(other.q) && this.x.equals(other.x));
}

function feFpToBigInteger() {
    return this.x;
}

function feFpNegate() {
    return new ECFieldElementFp(this.q, this.x.negate().mod(this.q));
}

function feFpAdd(b) {
    return new ECFieldElementFp(this.q, this.x.add(b.toBigInteger()).mod(this.q));
}

function feFpSubtract(b) {
    return new ECFieldElementFp(this.q, this.x.subtract(b.toBigInteger()).mod(this.q));
}

function feFpMultiply(b) {
    return new ECFieldElementFp(this.q, this.x.multiply(b.toBigInteger()).mod(this.q));
}

function feFpSquare() {
    return new ECFieldElementFp(this.q, this.x.square().mod(this.q));
}

function feFpDivide(b) {
    return new ECFieldElementFp(this.q, this.x.multiply(b.toBigInteger().modInverse(this.q)).mod(this.q));
}

ECFieldElementFp.prototype.equals = feFpEquals;
ECFieldElementFp.prototype.toBigInteger = feFpToBigInteger;
ECFieldElementFp.prototype.negate = feFpNegate;
ECFieldElementFp.prototype.add = feFpAdd;
ECFieldElementFp.prototype.subtract = feFpSubtract;
ECFieldElementFp.prototype.multiply = feFpMultiply;
ECFieldElementFp.prototype.square = feFpSquare;
ECFieldElementFp.prototype.divide = feFpDivide;

// ----------------
// ECPointFp

// constructor
function ECPointFp(curve,x,y,z) {
    this.curve = curve;
    this.x = x;
    this.y = y;
    // Projective coordinates: either zinv == null or z * zinv == 1
    // z and zinv are just BigIntegers, not fieldElements
    if(z == null) {
      this.z = BigInteger.ONE;
    }
    else {
      this.z = z;
    }
    this.zinv = null;
    //TODO: compression flag
}

function pointFpGetX() {
    if(this.zinv == null) {
      this.zinv = this.z.modInverse(this.curve.q);
    }
    return this.curve.fromBigInteger(this.x.toBigInteger().multiply(this.zinv).mod(this.curve.q));
}

function pointFpGetY() {
    if(this.zinv == null) {
      this.zinv = this.z.modInverse(this.curve.q);
    }
    return this.curve.fromBigInteger(this.y.toBigInteger().multiply(this.zinv).mod(this.curve.q));
}

function pointFpEquals(other) {
    if(other == this) return true;
    if(this.isInfinity()) return other.isInfinity();
    if(other.isInfinity()) return this.isInfinity();
    var u, v;
    // u = Y2 * Z1 - Y1 * Z2
    u = other.y.toBigInteger().multiply(this.z).subtract(this.y.toBigInteger().multiply(other.z)).mod(this.curve.q);
    if(!u.equals(BigInteger.ZERO)) return false;
    // v = X2 * Z1 - X1 * Z2
    v = other.x.toBigInteger().multiply(this.z).subtract(this.x.toBigInteger().multiply(other.z)).mod(this.curve.q);
    return v.equals(BigInteger.ZERO);
}

function pointFpIsInfinity() {
    if((this.x == null) && (this.y == null)) return true;
    return this.z.equals(BigInteger.ZERO) && !this.y.toBigInteger().equals(BigInteger.ZERO);
}

function pointFpNegate() {
    return new ECPointFp(this.curve, this.x, this.y.negate(), this.z);
}

function pointFpAdd(b) {
    if(this.isInfinity()) return b;
    if(b.isInfinity()) return this;

    // u = Y2 * Z1 - Y1 * Z2
    var u = b.y.toBigInteger().multiply(this.z).subtract(this.y.toBigInteger().multiply(b.z)).mod(this.curve.q);
    // v = X2 * Z1 - X1 * Z2
    var v = b.x.toBigInteger().multiply(this.z).subtract(this.x.toBigInteger().multiply(b.z)).mod(this.curve.q);

    if(BigInteger.ZERO.equals(v)) {
        if(BigInteger.ZERO.equals(u)) {
            return this.twice(); // this == b, so double
        }
  return this.curve.getInfinity(); // this = -b, so infinity
    }

    var THREE = new BigInteger("3");
    var x1 = this.x.toBigInteger();
    var y1 = this.y.toBigInteger();
    var x2 = b.x.toBigInteger();
    var y2 = b.y.toBigInteger();

    var v2 = v.square();
    var v3 = v2.multiply(v);
    var x1v2 = x1.multiply(v2);
    var zu2 = u.square().multiply(this.z);

    // x3 = v * (z2 * (z1 * u^2 - 2 * x1 * v^2) - v^3)
    var x3 = zu2.subtract(x1v2.shiftLeft(1)).multiply(b.z).subtract(v3).multiply(v).mod(this.curve.q);
    // y3 = z2 * (3 * x1 * u * v^2 - y1 * v^3 - z1 * u^3) + u * v^3
    var y3 = x1v2.multiply(THREE).multiply(u).subtract(y1.multiply(v3)).subtract(zu2.multiply(u)).multiply(b.z).add(u.multiply(v3)).mod(this.curve.q);
    // z3 = v^3 * z1 * z2
    var z3 = v3.multiply(this.z).multiply(b.z).mod(this.curve.q);

    return new ECPointFp(this.curve, this.curve.fromBigInteger(x3), this.curve.fromBigInteger(y3), z3);
}

function pointFpTwice() {
    if(this.isInfinity()) return this;
    if(this.y.toBigInteger().signum() == 0) return this.curve.getInfinity();

    // TODO: optimized handling of constants
    var THREE = new BigInteger("3");
    var x1 = this.x.toBigInteger();
    var y1 = this.y.toBigInteger();

    var y1z1 = y1.multiply(this.z);
    var y1sqz1 = y1z1.multiply(y1).mod(this.curve.q);
    var a = this.curve.a.toBigInteger();

    // w = 3 * x1^2 + a * z1^2
    var w = x1.square().multiply(THREE);
    if(!BigInteger.ZERO.equals(a)) {
      w = w.add(this.z.square().multiply(a));
    }
    w = w.mod(this.curve.q);
    // x3 = 2 * y1 * z1 * (w^2 - 8 * x1 * y1^2 * z1)
    var x3 = w.square().subtract(x1.shiftLeft(3).multiply(y1sqz1)).shiftLeft(1).multiply(y1z1).mod(this.curve.q);
    // y3 = 4 * y1^2 * z1 * (3 * w * x1 - 2 * y1^2 * z1) - w^3
    var y3 = w.multiply(THREE).multiply(x1).subtract(y1sqz1.shiftLeft(1)).shiftLeft(2).multiply(y1sqz1).subtract(w.square().multiply(w)).mod(this.curve.q);
    // z3 = 8 * (y1 * z1)^3
    var z3 = y1z1.square().multiply(y1z1).shiftLeft(3).mod(this.curve.q);

    return new ECPointFp(this.curve, this.curve.fromBigInteger(x3), this.curve.fromBigInteger(y3), z3);
}

// Simple NAF (Non-Adjacent Form) multiplication algorithm
// TODO: modularize the multiplication algorithm
function pointFpMultiply(k) {
    if(this.isInfinity()) return this;
    if(k.signum() == 0) return this.curve.getInfinity();

    var e = k;
    var h = e.multiply(new BigInteger("3"));

    var neg = this.negate();
    var R = this;

    var i;
    for(i = h.bitLength() - 2; i > 0; --i) {
  R = R.twice();

  var hBit = h.testBit(i);
  var eBit = e.testBit(i);

  if (hBit != eBit) {
      R = R.add(hBit ? this : neg);
  }
    }

    return R;
}

// Compute this*j + x*k (simultaneous multiplication)
function pointFpMultiplyTwo(j,x,k) {
  var i;
  if(j.bitLength() > k.bitLength())
    i = j.bitLength() - 1;
  else
    i = k.bitLength() - 1;

  var R = this.curve.getInfinity();
  var both = this.add(x);
  while(i >= 0) {
    R = R.twice();
    if(j.testBit(i)) {
      if(k.testBit(i)) {
        R = R.add(both);
      }
      else {
        R = R.add(this);
      }
    }
    else {
      if(k.testBit(i)) {
        R = R.add(x);
      }
    }
    --i;
  }

  return R;
}

ECPointFp.prototype.getX = pointFpGetX;
ECPointFp.prototype.getY = pointFpGetY;
ECPointFp.prototype.equals = pointFpEquals;
ECPointFp.prototype.isInfinity = pointFpIsInfinity;
ECPointFp.prototype.negate = pointFpNegate;
ECPointFp.prototype.add = pointFpAdd;
ECPointFp.prototype.twice = pointFpTwice;
ECPointFp.prototype.multiply = pointFpMultiply;
ECPointFp.prototype.multiplyTwo = pointFpMultiplyTwo;

// ----------------
// ECCurveFp

// constructor
function ECCurveFp(q,a,b) {
    this.q = q;
    this.a = this.fromBigInteger(a);
    this.b = this.fromBigInteger(b);
    this.infinity = new ECPointFp(this, null, null);
}

function curveFpGetQ() {
    return this.q;
}

function curveFpGetA() {
    return this.a;
}

function curveFpGetB() {
    return this.b;
}

function curveFpEquals(other) {
    if(other == this) return true;
    return(this.q.equals(other.q) && this.a.equals(other.a) && this.b.equals(other.b));
}

function curveFpGetInfinity() {
    return this.infinity;
}

function curveFpFromBigInteger(x) {
    return new ECFieldElementFp(this.q, x);
}

// for now, work with hex strings because they're easier in JS
function curveFpDecodePointHex(s) {
    switch(parseInt(s.substr(0,2), 16)) { // first byte
    case 0:
  return this.infinity;
    case 2:
    case 3:
  // point compression not supported yet
  return null;
    case 4:
    case 6:
    case 7:
  var len = (s.length - 2) / 2;
  var xHex = s.substr(2, len);
  var yHex = s.substr(len+2, len);

  return new ECPointFp(this,
           this.fromBigInteger(new BigInteger(xHex, 16)),
           this.fromBigInteger(new BigInteger(yHex, 16)));

    default: // unsupported
  return null;
    }
}

ECCurveFp.prototype.getQ = curveFpGetQ;
ECCurveFp.prototype.getA = curveFpGetA;
ECCurveFp.prototype.getB = curveFpGetB;
ECCurveFp.prototype.equals = curveFpEquals;
ECCurveFp.prototype.getInfinity = curveFpGetInfinity;
ECCurveFp.prototype.fromBigInteger = curveFpFromBigInteger;
ECCurveFp.prototype.decodePointHex = curveFpDecodePointHex;

// prepends 0 if bytes < len
// cuts off start if bytes > len
function integerToBytes(i, len) {
  var bytes = i.toByteArrayUnsigned();

  if (len < bytes.length) {
    bytes = bytes.slice(bytes.length-len);
  } else while (len > bytes.length) {
    bytes.unshift(0);
  }

  return bytes;
};

ECFieldElementFp.prototype.getByteLength = function () {
  return Math.floor((this.toBigInteger().bitLength() + 7) / 8);
};

ECPointFp.prototype.getEncoded = function (compressed) {
  var x = this.getX().toBigInteger();
  var y = this.getY().toBigInteger();

  // Get value as a 32-byte Buffer
  // Fixed length based on a patch by bitaddress.org and Casascius
  var enc = integerToBytes(x, 32);

  if (compressed) {
    if (y.isEven()) {
      // Compressed even pubkey
      // M = 02 || X
      enc.unshift(0x02);
    } else {
      // Compressed uneven pubkey
      // M = 03 || X
      enc.unshift(0x03);
    }
  } else {
    // Uncompressed pubkey
    // M = 04 || X || Y
    enc.unshift(0x04);
    enc = enc.concat(integerToBytes(y, 32));
  }
  return enc;
};

ECPointFp.decodeFrom = function (curve, enc) {
  var type = enc[0];
  var dataLen = enc.length-1;

  // Extract x and y as byte arrays
  var xBa = enc.slice(1, 1 + dataLen/2);
  var yBa = enc.slice(1 + dataLen/2, 1 + dataLen);

  // Prepend zero byte to prevent interpretation as negative integer
  xBa.unshift(0);
  yBa.unshift(0);

  // Convert to BigIntegers
  var x = new BigInteger(xBa);
  var y = new BigInteger(yBa);

  // Return point
  return new ECPointFp(curve, curve.fromBigInteger(x), curve.fromBigInteger(y));
};

ECPointFp.prototype.add2D = function (b) {
  if(this.isInfinity()) return b;
  if(b.isInfinity()) return this;

  if (this.x.equals(b.x)) {
    if (this.y.equals(b.y)) {
      // this = b, i.e. this must be doubled
      return this.twice();
    }
    // this = -b, i.e. the result is the point at infinity
    return this.curve.getInfinity();
  }

  var x_x = b.x.subtract(this.x);
  var y_y = b.y.subtract(this.y);
  var gamma = y_y.divide(x_x);

  var x3 = gamma.square().subtract(this.x).subtract(b.x);
  var y3 = gamma.multiply(this.x.subtract(x3)).subtract(this.y);

  return new ECPointFp(this.curve, x3, y3);
};

ECPointFp.prototype.twice2D = function () {
  if (this.isInfinity()) return this;
  if (this.y.toBigInteger().signum() == 0) {
    // if y1 == 0, then (x1, y1) == (x1, -y1)
    // and hence this = -this and thus 2(x1, y1) == infinity
    return this.curve.getInfinity();
  }

  var TWO = this.curve.fromBigInteger(BigInteger.valueOf(2));
  var THREE = this.curve.fromBigInteger(BigInteger.valueOf(3));
  var gamma = this.x.square().multiply(THREE).add(this.curve.a).divide(this.y.multiply(TWO));

  var x3 = gamma.square().subtract(this.x.multiply(TWO));
  var y3 = gamma.multiply(this.x.subtract(x3)).subtract(this.y);

  return new ECPointFp(this.curve, x3, y3);
};

ECPointFp.prototype.multiply2D = function (k) {
  if(this.isInfinity()) return this;
  if(k.signum() == 0) return this.curve.getInfinity();

  var e = k;
  var h = e.multiply(new BigInteger("3"));

  var neg = this.negate();
  var R = this;

  var i;
  for (i = h.bitLength() - 2; i > 0; --i) {
    R = R.twice();

    var hBit = h.testBit(i);
    var eBit = e.testBit(i);

    if (hBit != eBit) {
      R = R.add2D(hBit ? this : neg);
    }
  }

  return R;
};

ECPointFp.prototype.isOnCurve = function () {
  var x = this.getX().toBigInteger();
  var y = this.getY().toBigInteger();
  var a = this.curve.getA().toBigInteger();
  var b = this.curve.getB().toBigInteger();
  var n = this.curve.getQ();
  var lhs = y.multiply(y).mod(n);
  var rhs = x.multiply(x).multiply(x)
    .add(a.multiply(x)).add(b).mod(n);
  return lhs.equals(rhs);
};

ECPointFp.prototype.toString = function () {
  return '('+this.getX().toBigInteger().toString()+','+
    this.getY().toBigInteger().toString()+')';
};

/**
 * Validate an elliptic curve point.
 *
 * See SEC 1, section 3.2.2.1: Elliptic Curve Public Key Validation Primitive
 */
ECPointFp.prototype.validate = function () {
  var n = this.curve.getQ();

  // Check Q != O
  if (this.isInfinity()) {
    throw new Error("Point is at infinity.");
  }

  // Check coordinate bounds
  var x = this.getX().toBigInteger();
  var y = this.getY().toBigInteger();
  if (x.compareTo(BigInteger.ONE) < 0 ||
      x.compareTo(n.subtract(BigInteger.ONE)) > 0) {
    throw new Error('x coordinate out of bounds');
  }
  if (y.compareTo(BigInteger.ONE) < 0 ||
      y.compareTo(n.subtract(BigInteger.ONE)) > 0) {
    throw new Error('y coordinate out of bounds');
  }

  // Check y^2 = x^3 + ax + b (mod n)
  if (!this.isOnCurve()) {
    throw new Error("Point is not on the curve.");
  }

  // Check nQ = 0 (Q is a scalar multiple of G)
  if (this.multiply(n).isInfinity()) {
    // TODO: This check doesn't work - fix.
    throw new Error("Point is not a scalar multiple of G.");
  }

  return true;
};

//for easy exporting
ECCurveFp.ECPointFp = ECPointFp

}(this);

},{"bigi":2}],10:[function(require,module,exports){
var process=require("__browserify_process");!function(globals){
'use strict'

//*** UMD BEGIN
if (typeof define !== 'undefined' && define.amd) { //require.js / AMD
  define([], function() {
    return secureRandom
  })
} else if (typeof module !== 'undefined' && module.exports) { //CommonJS
  module.exports = secureRandom
} else { //script / browser
  globals.secureRandom = secureRandom
}
//*** UMD END

//options.array is the only valid option
function secureRandom(count, options) {
  options = options || {}
  //we check for process.pid to prevent browserify from tricking us
  if (typeof process != 'undefined' && typeof process.pid == 'number') {
    return nodeRandom(count, options)
  } else {
    if (!globals.crypto) throw new Error("Your browser does not support window.crypto.")
    return browserRandom(count, options)
  }
}

function nodeRandom(count, options) {
  var req = require //the intent here is to trick browserify
  var crypto = req('crypto') //trick browserify, => if we didn't do this, browserify would put crypto pkg in the bundle
  var buf = crypto.randomBytes(count)

  if (options.array) 
    var ret = []
  else
    var ret = new Uint8Array(count)

  for (var i = 0; i < count; ++i) {
    ret[i] = buf.readUInt8(i)
  }

  return ret
}

function browserRandom(count, options) {
  var nativeArr = new Uint8Array(count)
  globals.crypto.getRandomValues(nativeArr)

  if (options.array) {
    var ret = []
    for (var i = 0; i < nativeArr.length; ++i) {
      ret[i] = nativeArr[i]
    }
  } else {
    ret = nativeArr
  }

  return ret
}

}(this);

},{"__browserify_process":3}],11:[function(require,module,exports){
!function(globals) {
'use strict'

//*** IMPORTS
var BigInteger = null
var ECPointFp = null
var ecparams = null
var base58 = null
var sha256 = null
var ripe160 = null
var convertHex = null
var Address = null
var ecdsa = null
//*** IMPORTS END

if (typeof module !== 'undefined' && module.exports) { //CommonJS
  ECPointFp = require('ecurve').ECPointFp
  ecparams = require('ecurve-names')('secp256k1')
  sha256 = require('sha256')
  ripe160 = require('ripemd160')
  convertHex = require('convert-hex')
  Address = require('btc-address')
  ecdsa = require('ecdsa')
  BigInteger = require('bigi')
  base58 = require('bs58')
  module.exports = ECKey
} else {
  BigInteger = globals.BigInteger
  ECPointFp = globals.ECCurveFp.ECPointFp
  ecparams = globals.getSECCurveByName('secp256k1')
  base58 = globals.bs58
  sha256 = globals.sha256
  ripe160 = globals.ripemd160
  convertHex = globals.convertHex
  Address = globals.Address
  ecdsa = globals.ECDSA
  globals.ECKey = ECKey
}
//*** UMD END

var util = {
  sha256ripe160: function(bytes) {
    return ripe160(sha256(bytes, {asBytes: true}), {asBytes: true})
  }
}


var networkTypes = {
  prod: 128,
  testnet: 239
};

// input can be nothing, array of bytes, hex string, or base58 string
function ECKey (input) {
  if (!(this instanceof ECKey)) {
    return new ECKey(input);
  }

  this.compressed = !!ECKey.compressByDefault;

  if (!input) {
    // Generate new key
    var n = ecparams.getN();
    this.priv = ecdsa.getBigRandom(n);
  } else if (input instanceof BigInteger) {
    // Input is a private key value
    this.priv = input;
  } else if (Array.isArray(input)) {
    // Prepend zero byte to prevent interpretation as negative integer
    this.priv = BigInteger.fromByteArrayUnsigned(input);
    this.compressed = false;
  } else if ("string" == typeof input) {
    // A list of base58 encoded prefixes is at https://en.bitcoin.it/wiki/List_of_address_prefixes.
    if (input.length == 51 && input[0] == '5') {
      // Base58 encoded private key
      this.priv = BigInteger.fromByteArrayUnsigned(ECKey.decodeString(input, networkTypes.prod));
      this.compressed = false;
    }
    else if (input.length == 51 && input[0] == '9') {
      this.priv = BigInteger.fromByteArrayUnsigned(ECKey.decodeString(input, networkTypes.testnet));
      this.compressed = false;
    }
    else if (input.length == 52 && (input[0] === 'K' || input[0] === 'L')) {
      // Base58 encoded private key
      this.priv = BigInteger.fromByteArrayUnsigned(ECKey.decodeString(input, networkTypes.prod));
      this.compressed = true;
    }
    else if (input.length == 52 && input[0] === 'c') {
      // Base58 encoded private key
      this.priv = BigInteger.fromByteArrayUnsigned(ECKey.decodeString(input, networkTypes.testnet));
      this.compressed = true;
    } 
  }
};

// TODO(shtylman) methods
// wallet import format (base58 check with meta info)
// fromWIF
// toWIF
// fromBytes
// toBytes
// fromHex
// toHex

/**
 * Whether public keys should be returned compressed by default.
 */
ECKey.compressByDefault = false;

/**
 * Set whether the public key should be returned compressed or not.
 */
ECKey.prototype.setCompressed = function (v) {
  this.compressed = !!v;
};

/**
 * Return public key in DER encoding.
 */
ECKey.prototype.getPub = function () {
  return this.getPubPoint().getEncoded(this.compressed);
};

/**
 * Return public point as ECPoint object.
 */
ECKey.prototype.getPubPoint = function () {
  if (!this.pub) this.pub = ecparams.getG().multiply(this.priv);

  return this.pub;
};

/**
 * Get the pubKeyHash for this key.
 *
 * This is calculated as RIPE160(SHA256([encoded pubkey])) and returned as
 * a byte array.
 */
ECKey.prototype.getPubKeyHash = function () {
  if (this.pubKeyHash) return this.pubKeyHash;

  return this.pubKeyHash = util.sha256ripe160(this.getPub());
};

ECKey.prototype.getBitcoinAddress = function (address_type) {
  var hash = this.getPubKeyHash();
  var addr = new Address(hash, address_type);
  return addr;
};

ECKey.prototype.getExportedPrivateKey = function (bitcoinNetwork) {
  bitcoinNetwork = bitcoinNetwork || 'prod';
  var hash = this.priv.toByteArrayUnsigned();
  while (hash.length < 32) hash.unshift(0);
  if (this.compressed) hash.push(0x01);
  hash.unshift(networkTypes[bitcoinNetwork]);
  var checksum = sha256.x2(hash, {asBytes: true})
  var bytes = hash.concat(checksum.slice(0,4));
  return base58.encode(bytes);
};

ECKey.prototype.setPub = function (pub) {
  this.pub = ECPointFp.decodeFrom(ecparams.getCurve(), pub);
};

ECKey.prototype.toString = function (format) {
  return convertHex.bytesToHex(this.priv.toByteArrayUnsigned());
};

ECKey.prototype.sign = function (hash) {
  return ecdsa.sign(hash, this.priv);
};

ECKey.prototype.verify = function (hash, sig) {
  return ecdsa.verify(hash, sig, this.getPub());
};


/// THIS METHOD WAS ORIGINALLY IN ECDSA

  /**
   * Recover a public key from a signature.
   *
   * See SEC 1: Elliptic Curve Cryptography, section 4.1.6, "Public
   * Key Recovery Operation".
   *
   * http://www.secg.org/download/aid-780/sec1-v2.pdf
   */
ECKey.recoverPubKey = function (r, s, hash, i) {
    // The recovery parameter i has two bits.
    i = i & 3;

    // The less significant bit specifies whether the y coordinate
    // of the compressed point is even or not.
    var isYEven = i & 1;

    // The more significant bit specifies whether we should use the
    // first or second candidate key.
    var isSecondKey = i >> 1;

    var n = ecparams.getN();
    var G = ecparams.getG();
    var curve = ecparams.getCurve();
    var p = curve.getQ();
    var a = curve.getA().toBigInteger();
    var b = curve.getB().toBigInteger();

    // We precalculate (p + 1) / 4 where p is if the field order
    if (!P_OVER_FOUR) {
      P_OVER_FOUR = p.add(BigInteger.ONE).divide(BigInteger.valueOf(4));
    }

    // 1.1 Compute x
    var x = isSecondKey ? r.add(n) : r;

    // 1.3 Convert x to point
    var alpha = x.multiply(x).multiply(x).add(a.multiply(x)).add(b).mod(p);
    var beta = alpha.modPow(P_OVER_FOUR, p);

    var xorOdd = beta.isEven() ? (i % 2) : ((i+1) % 2);
    // If beta is even, but y isn't or vice versa, then convert it,
    // otherwise we're done and y == beta.
    var y = (beta.isEven() ? !isYEven : isYEven) ? beta : p.subtract(beta);

    // 1.4 Check that nR is at infinity
    var R = new ECPointFp(curve,
                          curve.fromBigInteger(x),
                          curve.fromBigInteger(y));
    R.validate();

    // 1.5 Compute e from M
    var e = BigInteger.fromByteArrayUnsigned(hash);
    var eNeg = BigInteger.ZERO.subtract(e).mod(n);

    // 1.6 Compute Q = r^-1 (sR - eG)
    var rInv = r.modInverse(n);
    var Q = implShamirsTrick(R, s, G, eNeg).multiply(rInv);

    Q.validate();
    if (!ECDSA.verifyRaw(e, r, s, Q)) {
      throw new Error("Pubkey recovery unsuccessful");
    }

    var pubKey = ECKey();
    pubKey.pub = Q;
    return pubKey;
}


/**
 * Parse an exported private key contained in a string.
 */
ECKey.decodeString = function (string, expectedVersion) {
  var bytes = base58.decode(string);

  if (bytes.length !== 37 && bytes.length !== 38) {
    throw new Error('not a valid base58 encoded private key');
  }

  //Format:
  //* uncompressed: 0x80 + [32-byte secret] + [4 bytes of Hash() of
  //previous 33 bytes], base58 encoded
  //* compressed: 0x80 + [32-byte secret] + 0x01 + [4 bytes of Hash()
  //previous 34 bytes], base58 encoded

  if (bytes[33] === 0x01) {
    // compressed
  }

  var hash = bytes.slice(0, 33);

  /*
  var checksum = Crypto.SHA256(Crypto.SHA256(hash, {asBytes: true}), {asBytes: true});

  if (checksum[0] != bytes[33] ||
      checksum[1] != bytes[34] ||
      checksum[2] != bytes[35] ||
      checksum[3] != bytes[36]) {
    throw "Checksum validation failed!";
  }
  */

  var version = hash.shift();

  if (version !== expectedVersion)
    throw "Version "+version+" not expected, expected " + expectedVersion + "!";

  return hash;
};


}(this);

},{"bigi":2,"bs58":4,"btc-address":5,"convert-hex":6,"ecdsa":7,"ecurve":13,"ecurve-names":12,"ripemd160":14,"sha256":17}],12:[function(require,module,exports){
module.exports=require(8)
},{"bigi":2,"ecurve":13}],13:[function(require,module,exports){
module.exports=require(9)
},{"bigi":2}],14:[function(require,module,exports){
!function(globals) {
'use strict'

var _imports = {}

if (typeof module !== 'undefined' && module.exports) { //CommonJS
    _imports.bytesToHex = require('convert-hex').bytesToHex
    _imports.convertString = require('convert-string')
  module.exports = ripemd160
} else {
  _imports.convertString = globals.convertString
  _imports.bytesToHex = globals.convertHex.bytesToHex
  globals.ripemd160 = ripemd160
}


/*
CryptoJS v3.1.2
code.google.com/p/crypto-js
(c) 2009-2013 by Jeff Mott. All rights reserved.
code.google.com/p/crypto-js/wiki/License
*/
/** @preserve
(c) 2012 by Cédric Mesnil. All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

    - Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
    - Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

// Constants table
var zl = [
    0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
    7,  4, 13,  1, 10,  6, 15,  3, 12,  0,  9,  5,  2, 14, 11,  8,
    3, 10, 14,  4,  9, 15,  8,  1,  2,  7,  0,  6, 13, 11,  5, 12,
    1,  9, 11, 10,  0,  8, 12,  4, 13,  3,  7, 15, 14,  5,  6,  2,
    4,  0,  5,  9,  7, 12,  2, 10, 14,  1,  3,  8, 11,  6, 15, 13];
var zr = [
    5, 14,  7,  0,  9,  2, 11,  4, 13,  6, 15,  8,  1, 10,  3, 12,
    6, 11,  3,  7,  0, 13,  5, 10, 14, 15,  8, 12,  4,  9,  1,  2,
    15,  5,  1,  3,  7, 14,  6,  9, 11,  8, 12,  2, 10,  0,  4, 13,
    8,  6,  4,  1,  3, 11, 15,  0,  5, 12,  2, 13,  9,  7, 10, 14,
    12, 15, 10,  4,  1,  5,  8,  7,  6,  2, 13, 14,  0,  3,  9, 11];
var sl = [
     11, 14, 15, 12,  5,  8,  7,  9, 11, 13, 14, 15,  6,  7,  9,  8,
    7, 6,   8, 13, 11,  9,  7, 15,  7, 12, 15,  9, 11,  7, 13, 12,
    11, 13,  6,  7, 14,  9, 13, 15, 14,  8, 13,  6,  5, 12,  7,  5,
      11, 12, 14, 15, 14, 15,  9,  8,  9, 14,  5,  6,  8,  6,  5, 12,
    9, 15,  5, 11,  6,  8, 13, 12,  5, 12, 13, 14, 11,  8,  5,  6 ];
var sr = [
    8,  9,  9, 11, 13, 15, 15,  5,  7,  7,  8, 11, 14, 14, 12,  6,
    9, 13, 15,  7, 12,  8,  9, 11,  7,  7, 12,  7,  6, 15, 13, 11,
    9,  7, 15, 11,  8,  6,  6, 14, 12, 13,  5, 14, 13, 13,  7,  5,
    15,  5,  8, 11, 14, 14,  6, 14,  6,  9, 12,  9, 12,  5, 15,  8,
    8,  5, 12,  9, 12,  5, 14,  6,  8, 13,  6,  5, 15, 13, 11, 11 ];

var hl =  [ 0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E];
var hr =  [ 0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000];

var bytesToWords = function (bytes) {
    var words = [];
    for (var i = 0, b = 0; i < bytes.length; i++, b += 8) {
        words[b >>> 5] |= bytes[i] << (24 - b % 32);
    }
    return words;
};

var wordsToBytes = function (words) {
    var bytes = [];
    for (var b = 0; b < words.length * 32; b += 8) {
        bytes.push((words[b >>> 5] >>> (24 - b % 32)) & 0xFF);
    }
    return bytes;
};

var processBlock = function (H, M, offset) {

    // Swap endian
    for (var i = 0; i < 16; i++) {
        var offset_i = offset + i;
        var M_offset_i = M[offset_i];

        // Swap
        M[offset_i] = (
            (((M_offset_i << 8)  | (M_offset_i >>> 24)) & 0x00ff00ff) |
            (((M_offset_i << 24) | (M_offset_i >>> 8))  & 0xff00ff00)
        );
    }

    // Working variables
    var al, bl, cl, dl, el;
    var ar, br, cr, dr, er;

    ar = al = H[0];
    br = bl = H[1];
    cr = cl = H[2];
    dr = dl = H[3];
    er = el = H[4];
    // Computation
    var t;
    for (var i = 0; i < 80; i += 1) {
        t = (al +  M[offset+zl[i]])|0;
        if (i<16){
            t +=  f1(bl,cl,dl) + hl[0];
        } else if (i<32) {
            t +=  f2(bl,cl,dl) + hl[1];
        } else if (i<48) {
            t +=  f3(bl,cl,dl) + hl[2];
        } else if (i<64) {
            t +=  f4(bl,cl,dl) + hl[3];
        } else {// if (i<80) {
            t +=  f5(bl,cl,dl) + hl[4];
        }
        t = t|0;
        t =  rotl(t,sl[i]);
        t = (t+el)|0;
        al = el;
        el = dl;
        dl = rotl(cl, 10);
        cl = bl;
        bl = t;

        t = (ar + M[offset+zr[i]])|0;
        if (i<16){
            t +=  f5(br,cr,dr) + hr[0];
        } else if (i<32) {
            t +=  f4(br,cr,dr) + hr[1];
        } else if (i<48) {
            t +=  f3(br,cr,dr) + hr[2];
        } else if (i<64) {
            t +=  f2(br,cr,dr) + hr[3];
        } else {// if (i<80) {
            t +=  f1(br,cr,dr) + hr[4];
        }
        t = t|0;
        t =  rotl(t,sr[i]) ;
        t = (t+er)|0;
        ar = er;
        er = dr;
        dr = rotl(cr, 10);
        cr = br;
        br = t;
    }
    // Intermediate hash value
    t    = (H[1] + cl + dr)|0;
    H[1] = (H[2] + dl + er)|0;
    H[2] = (H[3] + el + ar)|0;
    H[3] = (H[4] + al + br)|0;
    H[4] = (H[0] + bl + cr)|0;
    H[0] =  t;
};

function f1(x, y, z) {
    return ((x) ^ (y) ^ (z));

}

function f2(x, y, z) {
    return (((x)&(y)) | ((~x)&(z)));
}

function f3(x, y, z) {
    return (((x) | (~(y))) ^ (z));
}

function f4(x, y, z) {
    return (((x) & (z)) | ((y)&(~(z))));
}

function f5(x, y, z) {
    return ((x) ^ ((y) |(~(z))));

}

function rotl(x,n) {
    return (x<<n) | (x>>>(32-n));
}

function ripemd160(message, options) {

    if (message.constructor === String) {
        message = _imports.convertString.UTF8.stringToBytes(message);
    }

    var H = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0];
    var m = bytesToWords(message);

    var nBitsLeft = message.length * 8;
    var nBitsTotal = message.length * 8;

    // Add padding
    m[nBitsLeft >>> 5] |= 0x80 << (24 - nBitsLeft % 32);
    m[(((nBitsLeft + 64) >>> 9) << 4) + 14] = (
        (((nBitsTotal << 8)  | (nBitsTotal >>> 24)) & 0x00ff00ff) |
        (((nBitsTotal << 24) | (nBitsTotal >>> 8))  & 0xff00ff00)
    );

    for (var i=0 ; i<m.length; i += 16) {
        processBlock(H, m, i);
    }

    // Swap endian
    for (var i = 0; i < 5; i++) {
        // Shortcut
        var H_i = H[i];

        // Swap
        H[i] = (((H_i << 8)  | (H_i >>> 24)) & 0x00ff00ff) |
            (((H_i << 24) | (H_i >>> 8))  & 0xff00ff00);
    }

    var digestbytes = wordsToBytes(H);
    return options && options.asBytes ? digestbytes :
        options && options.asString ? _imports.convertString.bytesToString(digestbytes) :
        _imports.bytesToHex(digestbytes);
};

}(this);
},{"convert-hex":6,"convert-string":15}],15:[function(require,module,exports){
!function(globals) {
'use strict'

var convertString = {
  bytesToString: function(bytes) {
    return bytes.map(function(x){ return String.fromCharCode(x) }).join('')
  },
  stringToBytes: function(str) {
    return str.split('').map(function(x) { return x.charCodeAt(0) })
  }
}

//http://hossa.in/2012/07/20/utf-8-in-javascript.html
convertString.UTF8 = {
   bytesToString: function(bytes) {
    return decodeURIComponent(escape(convertString.bytesToString(bytes)))
  },
  stringToBytes: function(str) {
   return convertString.stringToBytes(unescape(encodeURIComponent(str)))
  }
}

if (typeof module !== 'undefined' && module.exports) { //CommonJS
  module.exports = convertString
} else {
  globals.convertString = convertString
}

}(this);
},{}],16:[function(require,module,exports){
module.exports=require(10)
},{"__browserify_process":3}],17:[function(require,module,exports){
!function(globals) {
'use strict'

var _imports = {}

if (typeof module !== 'undefined' && module.exports) { //CommonJS
  _imports.bytesToHex = require('convert-hex').bytesToHex
  _imports.convertString = require('convert-string')
  module.exports = sha256
} else {
  _imports.bytesToHex = globals.convertHex.bytesToHex
  _imports.convertString = globals.convertString
  globals.sha256 = sha256
}

/*
CryptoJS v3.1.2
code.google.com/p/crypto-js
(c) 2009-2013 by Jeff Mott. All rights reserved.
code.google.com/p/crypto-js/wiki/License
*/

// Initialization round constants tables
var K = []

// Compute constants
!function () {
  function isPrime(n) {
    var sqrtN = Math.sqrt(n);
    for (var factor = 2; factor <= sqrtN; factor++) {
      if (!(n % factor)) return false
    }

    return true
  }

  function getFractionalBits(n) {
    return ((n - (n | 0)) * 0x100000000) | 0
  }

  var n = 2
  var nPrime = 0
  while (nPrime < 64) {
    if (isPrime(n)) {
      K[nPrime] = getFractionalBits(Math.pow(n, 1 / 3))
      nPrime++
    }

    n++
  }
}()

var bytesToWords = function (bytes) {
  var words = []
  for (var i = 0, b = 0; i < bytes.length; i++, b += 8) {
    words[b >>> 5] |= bytes[i] << (24 - b % 32)
  }
  return words
}

var wordsToBytes = function (words) {
  var bytes = []
  for (var b = 0; b < words.length * 32; b += 8) {
    bytes.push((words[b >>> 5] >>> (24 - b % 32)) & 0xFF)
  }
  return bytes
}

// Reusable object
var W = []

var processBlock = function (H, M, offset) {
  // Working variables
  var a = H[0], b = H[1], c = H[2], d = H[3]
  var e = H[4], f = H[5], g = H[6], h = H[7]

    // Computation
  for (var i = 0; i < 64; i++) {
    if (i < 16) {
      W[i] = M[offset + i] | 0
    } else {
      var gamma0x = W[i - 15]
      var gamma0  = ((gamma0x << 25) | (gamma0x >>> 7))  ^
                    ((gamma0x << 14) | (gamma0x >>> 18)) ^
                    (gamma0x >>> 3)

      var gamma1x = W[i - 2];
      var gamma1  = ((gamma1x << 15) | (gamma1x >>> 17)) ^
                    ((gamma1x << 13) | (gamma1x >>> 19)) ^
                    (gamma1x >>> 10)

      W[i] = gamma0 + W[i - 7] + gamma1 + W[i - 16];
    }

    var ch  = (e & f) ^ (~e & g);
    var maj = (a & b) ^ (a & c) ^ (b & c);

    var sigma0 = ((a << 30) | (a >>> 2)) ^ ((a << 19) | (a >>> 13)) ^ ((a << 10) | (a >>> 22));
    var sigma1 = ((e << 26) | (e >>> 6)) ^ ((e << 21) | (e >>> 11)) ^ ((e << 7)  | (e >>> 25));

    var t1 = h + sigma1 + ch + K[i] + W[i];
    var t2 = sigma0 + maj;

    h = g;
    g = f;
    f = e;
    e = (d + t1) | 0;
    d = c;
    c = b;
    b = a;
    a = (t1 + t2) | 0;
  }

  // Intermediate hash value
  H[0] = (H[0] + a) | 0;
  H[1] = (H[1] + b) | 0;
  H[2] = (H[2] + c) | 0;
  H[3] = (H[3] + d) | 0;
  H[4] = (H[4] + e) | 0;
  H[5] = (H[5] + f) | 0;
  H[6] = (H[6] + g) | 0;
  H[7] = (H[7] + h) | 0;
}

function sha256(message, options) {;
  if (message.constructor === String) {
    message = _imports.convertString.UTF8.stringToBytes(message);
  }

  var H =[ 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
           0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19 ];

  var m = bytesToWords(message);
  var l = message.length * 8;

  m[l >> 5] |= 0x80 << (24 - l % 32);
  m[((l + 64 >> 9) << 4) + 15] = l;

  for (var i=0 ; i<m.length; i += 16) {
    processBlock(H, m, i);
  }

  var digestbytes = wordsToBytes(H);
  return options && options.asBytes ? digestbytes :
         options && options.asString ? _imports.convertString.bytesToString(digestbytes) :
         _imports.bytesToHex(digestbytes)
}

sha256.x2 = function(message, options) {
  return sha256(sha256(message, options), options)
}

}(this);
},{"convert-hex":6,"convert-string":18}],18:[function(require,module,exports){
module.exports=require(15)
},{}]},{},[1])
(1)
});
;