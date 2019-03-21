var _InputStream = require('./InputStream');

var isNodeJs = typeof window === 'undefined' && typeof importScripts === 'undefined';
var fs = isNodeJs ? require("fs") : null;

function FileStream(fileName, decodeToUnicodeCodePoints) {
	var data = fs.readFileSync(fileName, "utf8");
	_InputStream.InputStream.call(this, data, decodeToUnicodeCodePoints);
	this.fileName = fileName;
	return this;
}

FileStream.prototype = Object.create(_InputStream.InputStream.prototype);
FileStream.prototype.constructor = FileStream;

exports.FileStream = FileStream;
