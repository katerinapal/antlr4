Object.defineProperty(exports, "__esModule", {
    value: true
});
exports.LL1Analyzer = LL1Analyzer;

var _PredictionContext = require("./PredictionContext");

var pc = _interopRequireWildcard(_PredictionContext);

var _Transition = require("./atn/Transition");

var _ATNState = require("./atn/ATNState");

var _IntervalSet = require("./IntervalSet");

var _ATNConfig = require("./atn/ATNConfig");

var _Token = require("./Token");

var _Utils = require("./Utils");

function _interopRequireWildcard(obj) {
    if (obj && obj.__esModule) {
        return obj;
    } else {
        var newObj = {};if (obj != null) {
            for (var key in obj) {
                if (Object.prototype.hasOwnProperty.call(obj, key)) newObj[key] = obj[key];
            }
        }newObj.default = obj;return newObj;
    }
}

var predictionContextFromRuleContext = pc.predictionContextFromRuleContext;
var PredictionContext = pc.PredictionContext;
var SingletonPredictionContext = pc.SingletonPredictionContext;

function LL1Analyzer(atn) {
    this.atn = atn;
}

//* Special value added to the lookahead sets to indicate that we hit
//  a predicate during analysis if {@code seeThruPreds==false}.
///
LL1Analyzer.HIT_PRED = _Token.Token.INVALID_TYPE;

//*
// Calculates the SLL(1) expected lookahead set for each outgoing transition
// of an {@link ATNState}. The returned array has one element for each
// outgoing transition in {@code s}. If the closure from transition
// <em>i</em> leads to a semantic predicate before matching a symbol, the
// element at index <em>i</em> of the result will be {@code null}.
//
// @param s the ATN state
// @return the expected symbols for each outgoing transition of {@code s}.
///
LL1Analyzer.prototype.getDecisionLookahead = function (s) {
    if (s === null) {
        return null;
    }
    var count = s.transitions.length;
    var look = [];
    for (var alt = 0; alt < count; alt++) {
        look[alt] = new _IntervalSet.IntervalSet();
        var lookBusy = new _Utils.Set();
        var seeThruPreds = false; // fail to get lookahead upon pred
        this._LOOK(s.transition(alt).target, null, PredictionContext.EMPTY, look[alt], lookBusy, new _Utils.BitSet(), seeThruPreds, false);
        // Wipe out lookahead for this alternative if we found nothing
        // or we had a predicate when we !seeThruPreds
        if (look[alt].length === 0 || look[alt].contains(LL1Analyzer.HIT_PRED)) {
            look[alt] = null;
        }
    }
    return look;
};

//*
// Compute set of tokens that can follow {@code s} in the ATN in the
// specified {@code ctx}.
//
// <p>If {@code ctx} is {@code null} and the end of the rule containing
// {@code s} is reached, {@link Token//EPSILON} is added to the result set.
// If {@code ctx} is not {@code null} and the end of the outermost rule is
// reached, {@link Token//EOF} is added to the result set.</p>
//
// @param s the ATN state
// @param stopState the ATN state to stop at. This can be a
// {@link BlockEndState} to detect epsilon paths through a closure.
// @param ctx the complete parser context, or {@code null} if the context
// should be ignored
//
// @return The set of tokens that can follow {@code s} in the ATN in the
// specified {@code ctx}.
///
LL1Analyzer.prototype.LOOK = function (s, stopState, ctx) {
    var r = new _IntervalSet.IntervalSet();
    var seeThruPreds = true; // ignore preds; get all lookahead
    ctx = ctx || null;
    var lookContext = ctx !== null ? predictionContextFromRuleContext(s.atn, ctx) : null;
    this._LOOK(s, stopState, lookContext, r, new _Utils.Set(), new _Utils.BitSet(), seeThruPreds, true);
    return r;
};

//*
// Compute set of tokens that can follow {@code s} in the ATN in the
// specified {@code ctx}.
//
// <p>If {@code ctx} is {@code null} and {@code stopState} or the end of the
// rule containing {@code s} is reached, {@link Token//EPSILON} is added to
// the result set. If {@code ctx} is not {@code null} and {@code addEOF} is
// {@code true} and {@code stopState} or the end of the outermost rule is
// reached, {@link Token//EOF} is added to the result set.</p>
//
// @param s the ATN state.
// @param stopState the ATN state to stop at. This can be a
// {@link BlockEndState} to detect epsilon paths through a closure.
// @param ctx The outer context, or {@code null} if the outer context should
// not be used.
// @param look The result lookahead set.
// @param lookBusy A set used for preventing epsilon closures in the ATN
// from causing a stack overflow. Outside code should pass
// {@code new Set<ATNConfig>} for this argument.
// @param calledRuleStack A set used for preventing left recursion in the
// ATN from causing a stack overflow. Outside code should pass
// {@code new BitSet()} for this argument.
// @param seeThruPreds {@code true} to true semantic predicates as
// implicitly {@code true} and "see through them", otherwise {@code false}
// to treat semantic predicates as opaque and add {@link //HIT_PRED} to the
// result if one is encountered.
// @param addEOF Add {@link Token//EOF} to the result if the end of the
// outermost context is reached. This parameter has no effect if {@code ctx}
// is {@code null}.
///
LL1Analyzer.prototype._LOOK = function (s, stopState, ctx, look, lookBusy, calledRuleStack, seeThruPreds, addEOF) {
    var c = new _ATNConfig.ATNConfig({ state: s, alt: 0, context: ctx }, null);
    if (lookBusy.contains(c)) {
        return;
    }
    lookBusy.add(c);
    if (s === stopState) {
        if (ctx === null) {
            look.addOne(_Token.Token.EPSILON);
            return;
        } else if (ctx.isEmpty() && addEOF) {
            look.addOne(_Token.Token.EOF);
            return;
        }
    }
    if (s instanceof _ATNState.RuleStopState) {
        if (ctx === null) {
            look.addOne(_Token.Token.EPSILON);
            return;
        } else if (ctx.isEmpty() && addEOF) {
            look.addOne(_Token.Token.EOF);
            return;
        }
        if (ctx !== PredictionContext.EMPTY) {
            // run thru all possible stack tops in ctx
            for (var i = 0; i < ctx.length; i++) {
                var returnState = this.atn.states[ctx.getReturnState(i)];
                var removed = calledRuleStack.contains(returnState.ruleIndex);
                try {
                    calledRuleStack.remove(returnState.ruleIndex);
                    this._LOOK(returnState, stopState, ctx.getParent(i), look, lookBusy, calledRuleStack, seeThruPreds, addEOF);
                } finally {
                    if (removed) {
                        calledRuleStack.add(returnState.ruleIndex);
                    }
                }
            }
            return;
        }
    }
    for (var j = 0; j < s.transitions.length; j++) {
        var t = s.transitions[j];
        if (t.constructor === _Transition.RuleTransition) {
            if (calledRuleStack.contains(t.target.ruleIndex)) {
                continue;
            }
            var newContext = SingletonPredictionContext.create(ctx, t.followState.stateNumber);
            try {
                calledRuleStack.add(t.target.ruleIndex);
                this._LOOK(t.target, stopState, newContext, look, lookBusy, calledRuleStack, seeThruPreds, addEOF);
            } finally {
                calledRuleStack.remove(t.target.ruleIndex);
            }
        } else if (t instanceof _Transition.AbstractPredicateTransition) {
            if (seeThruPreds) {
                this._LOOK(t.target, stopState, ctx, look, lookBusy, calledRuleStack, seeThruPreds, addEOF);
            } else {
                look.addOne(LL1Analyzer.HIT_PRED);
            }
        } else if (t.isEpsilon) {
            this._LOOK(t.target, stopState, ctx, look, lookBusy, calledRuleStack, seeThruPreds, addEOF);
        } else if (t.constructor === _Transition.WildcardTransition) {
            look.addRange(_Token.Token.MIN_USER_TOKEN_TYPE, this.atn.maxTokenType);
        } else {
            var set = t.label;
            if (set !== null) {
                if (t instanceof _Transition.NotSetTransition) {
                    set = set.complement(_Token.Token.MIN_USER_TOKEN_TYPE, this.atn.maxTokenType);
                }
                look.addSet(set);
            }
        }
    }
};
