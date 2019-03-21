Object.defineProperty(exports, "__esModule", {
	value: true
});
exports.INVALID_INTERVAL = undefined;
exports.RuleNode = RuleNode;
exports.TerminalNode = TerminalNode;
exports.ErrorNode = ErrorNode;
exports.ParseTreeVisitor = ParseTreeVisitor;
exports.ParseTreeListener = ParseTreeListener;
exports.TerminalNodeImpl = TerminalNodeImpl;
exports.ErrorNodeImpl = ErrorNodeImpl;
exports.ParseTreeWalker = ParseTreeWalker;

var _Utils = require("../Utils.js");

var Utils = _interopRequireWildcard(_Utils);

var _IntervalSet = require("./../IntervalSet");

var _Token = require("./../Token");

function _interopRequireWildcard(obj) { if (obj && obj.__esModule) { return obj; } else { var newObj = {}; if (obj != null) { for (var key in obj) { if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key]; } } newObj.default = obj; return newObj; } }

var INVALID_INTERVAL = exports.INVALID_INTERVAL = new _IntervalSet.Interval(-1, -2);

function Tree() {
	return this;
}

function SyntaxTree() {
	Tree.call(this);
	return this;
}

SyntaxTree.prototype = Object.create(Tree.prototype);
SyntaxTree.prototype.constructor = SyntaxTree;

function ParseTree() {
	SyntaxTree.call(this);
	return this;
}

ParseTree.prototype = Object.create(SyntaxTree.prototype);
ParseTree.prototype.constructor = ParseTree;

function RuleNode() {
	ParseTree.call(this);
	return this;
}

RuleNode.prototype = Object.create(ParseTree.prototype);
RuleNode.prototype.constructor = RuleNode;

function TerminalNode() {
	ParseTree.call(this);
	return this;
}

TerminalNode.prototype = Object.create(ParseTree.prototype);
TerminalNode.prototype.constructor = TerminalNode;

function ErrorNode() {
	TerminalNode.call(this);
	return this;
}

ErrorNode.prototype = Object.create(TerminalNode.prototype);
ErrorNode.prototype.constructor = ErrorNode;

function ParseTreeVisitor() {
	return this;
}

ParseTreeVisitor.prototype.visit = function (ctx) {
	if (Array.isArray(ctx)) {
		return ctx.map(function (child) {
			return child.accept(this);
		}, this);
	} else {
		return ctx.accept(this);
	}
};

ParseTreeVisitor.prototype.visitChildren = function (ctx) {
	if (ctx.children) {
		return this.visit(ctx.children);
	} else {
		return null;
	}
};

ParseTreeVisitor.prototype.visitTerminal = function (node) {};

ParseTreeVisitor.prototype.visitErrorNode = function (node) {};

function ParseTreeListener() {
	return this;
}

ParseTreeListener.prototype.visitTerminal = function (node) {};

ParseTreeListener.prototype.visitErrorNode = function (node) {};

ParseTreeListener.prototype.enterEveryRule = function (node) {};

ParseTreeListener.prototype.exitEveryRule = function (node) {};

function TerminalNodeImpl(symbol) {
	TerminalNode.call(this);
	this.parentCtx = null;
	this.symbol = symbol;
	return this;
}

TerminalNodeImpl.prototype = Object.create(TerminalNode.prototype);
TerminalNodeImpl.prototype.constructor = TerminalNodeImpl;

TerminalNodeImpl.prototype.getChild = function (i) {
	return null;
};

TerminalNodeImpl.prototype.getSymbol = function () {
	return this.symbol;
};

TerminalNodeImpl.prototype.getParent = function () {
	return this.parentCtx;
};

TerminalNodeImpl.prototype.getPayload = function () {
	return this.symbol;
};

TerminalNodeImpl.prototype.getSourceInterval = function () {
	if (this.symbol === null) {
		return INVALID_INTERVAL;
	}
	var tokenIndex = this.symbol.tokenIndex;
	return new _IntervalSet.Interval(tokenIndex, tokenIndex);
};

TerminalNodeImpl.prototype.getChildCount = function () {
	return 0;
};

TerminalNodeImpl.prototype.accept = function (visitor) {
	return visitor.visitTerminal(this);
};

TerminalNodeImpl.prototype.getText = function () {
	return this.symbol.text;
};

TerminalNodeImpl.prototype.toString = function () {
	if (this.symbol.type === _Token.Token.EOF) {
		return "<EOF>";
	} else {
		return this.symbol.text;
	}
};

// Represents a token that was consumed during resynchronization
// rather than during a valid match operation. For example,
// we will create this kind of a node during single token insertion
// and deletion as well as during "consume until error recovery set"
// upon no viable alternative exceptions.

function ErrorNodeImpl(token) {
	TerminalNodeImpl.call(this, token);
	return this;
}

ErrorNodeImpl.prototype = Object.create(TerminalNodeImpl.prototype);
ErrorNodeImpl.prototype.constructor = ErrorNodeImpl;

ErrorNodeImpl.prototype.isErrorNode = function () {
	return true;
};

ErrorNodeImpl.prototype.accept = function (visitor) {
	return visitor.visitErrorNode(this);
};

function ParseTreeWalker() {
	return this;
}

ParseTreeWalker.prototype.walk = function (listener, t) {
	var errorNode = t instanceof ErrorNode || t.isErrorNode !== undefined && t.isErrorNode();
	if (errorNode) {
		listener.visitErrorNode(t);
	} else if (t instanceof TerminalNode) {
		listener.visitTerminal(t);
	} else {
		this.enterRule(listener, t);
		for (var i = 0; i < t.getChildCount(); i++) {
			var child = t.getChild(i);
			this.walk(listener, child);
		}
		this.exitRule(listener, t);
	}
};
//
// The discovery of a rule node, involves sending two events: the generic
// {@link ParseTreeListener//enterEveryRule} and a
// {@link RuleContext}-specific event. First we trigger the generic and then
// the rule specific. We to them in reverse order upon finishing the node.
//
ParseTreeWalker.prototype.enterRule = function (listener, r) {
	var ctx = r.getRuleContext();
	listener.enterEveryRule(ctx);
	ctx.enterRule(listener);
};

ParseTreeWalker.prototype.exitRule = function (listener, r) {
	var ctx = r.getRuleContext();
	ctx.exitRule(listener);
	listener.exitEveryRule(ctx);
};

ParseTreeWalker.DEFAULT = new ParseTreeWalker();
