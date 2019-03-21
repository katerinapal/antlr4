import { InputStream } from "./InputStream";
var isNodeJs = typeof window === 'undefined' && typeof importScripts === 'undefined';
var fs = isNodeJs ? require("fs") : null;

function FileStream(fileName, decodeToUnicodeCodePoints) {
	var data = fs.readFileSync(fileName, "utf8");
	InputStream.call(this, data, decodeToUnicodeCodePoints);
	this.fileName = fileName;
	return this;
}

FileStream.prototype = Object.create(InputStream.prototype);
FileStream.prototype.constructor = FileStream;

exports.FileStream = FileStream;
