

var Crypto = {
  sha256: require('sha256'),
  ripemd160: require('ripemd160')
}

module.exports = {
  Address: require('btc-address'),
  Key: require('eckey'),
  ECDSA: require('ecdsa'),
  BigInteger: require('bigi'),
  Crypto: Crypto,
  base58: require('bs58'),
  convertHex: require('convert-hex')
}
