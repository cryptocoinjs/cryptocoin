

var Crypto = {
  sha256: require('cryptocoin-sha256'),
  ripemd160: require('cryptocoin-ripemd160')
}

module.exports = {
  Address: require('cryptocoin-address-btc'),
  Key: require('cryptocoin-eckey'),
  BigInteger: require('cryptocoin-bigint'),
  Crypto: Crypto,
  base58: require('cryptocoin-base58'),
  convertHex: require('cryptocoin-convert-hex')
}
