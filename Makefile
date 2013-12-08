clean:
	rm -f dist/cryptocoin.js
	rm -f dist/cryptocoin.min.js

min: dist
	node_modules/.bin/uglifyjs dist/cryptocoin.js -o dist/cryptocoin.min.js

dist:
	node_modules/.bin/browserify lib/index.js -o dist/cryptocoin.js -s cryptocoin

.PHONY: dist min