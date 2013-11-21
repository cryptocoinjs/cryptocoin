

var Crypto = {
  sha256: require('sha256'),
  ripemd160: require('ripemd160')
}

module.exports = {
  Address: require('btc-address'),
  Key: require('eckey'),
  BigInteger: require('cryptocoin-bigint'),
  Crypto: Crypto,
  base58: require('cryptocoin-base58'),
  convertHex: require('convert-hex')
}
