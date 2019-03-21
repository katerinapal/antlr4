var _BufferedTokenStream = require("./BufferedTokenStream");

var _Token = require("./Token");

function CommonTokenStream(lexer, channel) {
    _BufferedTokenStream.BufferedTokenStream.call(this, lexer);
    this.channel = channel === undefined ? _Token.Token.DEFAULT_CHANNEL : channel;
    return this;
}

CommonTokenStream.prototype = Object.create(_BufferedTokenStream.BufferedTokenStream.prototype);
CommonTokenStream.prototype.constructor = CommonTokenStream;

CommonTokenStream.prototype.adjustSeekIndex = function (i) {
    return this.nextTokenOnChannel(i, this.channel);
};

CommonTokenStream.prototype.LB = function (k) {
    if (k === 0 || this.index - k < 0) {
        return null;
    }
    var i = this.index;
    var n = 1;
    // find k good tokens looking backwards
    while (n <= k) {
        // skip off-channel tokens
        i = this.previousTokenOnChannel(i - 1, this.channel);
        n += 1;
    }
    if (i < 0) {
        return null;
    }
    return this.tokens[i];
};

CommonTokenStream.prototype.LT = function (k) {
    this.lazyInit();
    if (k === 0) {
        return null;
    }
    if (k < 0) {
        return this.LB(-k);
    }
    var i = this.index;
    var n = 1; // we know tokens[pos] is a good one
    // find k good tokens
    while (n < k) {
        // skip off-channel tokens, but make sure to not look past EOF
        if (this.sync(i + 1)) {
            i = this.nextTokenOnChannel(i + 1, this.channel);
        }
        n += 1;
    }
    return this.tokens[i];
};

// Count EOF just once.///
CommonTokenStream.prototype.getNumberOfOnChannelTokens = function () {
    var n = 0;
    this.fill();
    for (var i = 0; i < this.tokens.length; i++) {
        var t = this.tokens[i];
        if (t.channel === this.channel) {
            n += 1;
        }
        if (t.type === _Token.Token.EOF) {
            break;
        }
    }
    return n;
};

exports.CommonTokenStream = CommonTokenStream;
