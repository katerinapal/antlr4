var _Transition = require("./Transition");

var Transitions = _interopRequireWildcard(_Transition);

var _Utils = require("./../Utils");

var Utils = _interopRequireWildcard(_Utils);

var _PredictionContext = require("./../PredictionContext");

var _Errors = require("./../error/Errors");

var _IntervalSet = require("./../IntervalSet");

var _ATNState = require("./ATNState");

var _SemanticContext = require("./SemanticContext");

var _ParserRuleContext = require("./../ParserRuleContext");

var _RuleContext = require("./../RuleContext");

var _PredictionMode = require("./PredictionMode");

var _ATNSimulator = require("./ATNSimulator");

var _DFAState = require("./../dfa/DFAState");

var _Token = require("./../Token");

var _ATNConfigSet = require("./ATNConfigSet");

var _ATNConfig = require("./ATNConfig");

var _ATN = require("./ATN");

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

var Set = Utils.Set;
var BitSet = Utils.BitSet;
var DoubleDict = Utils.DoubleDict;
var Transition = Transitions.Transition;
var SetTransition = Transitions.SetTransition;
var NotSetTransition = Transitions.NotSetTransition;
var RuleTransition = Transitions.RuleTransition;
var ActionTransition = Transitions.ActionTransition;

function ParserATNSimulator(parser, atn, decisionToDFA, sharedContextCache) {
    _ATNSimulator.ATNSimulator.call(this, atn, sharedContextCache);
    this.parser = parser;
    this.decisionToDFA = decisionToDFA;
    // SLL, LL, or LL + exact ambig detection?//
    this.predictionMode = _PredictionMode.PredictionMode.LL;
    // LAME globals to avoid parameters!!!!! I need these down deep in predTransition
    this._input = null;
    this._startIndex = 0;
    this._outerContext = null;
    this._dfa = null;
    // Each prediction operation uses a cache for merge of prediction contexts.
    //  Don't keep around as it wastes huge amounts of memory. DoubleKeyMap
    //  isn't synchronized but we're ok since two threads shouldn't reuse same
    //  parser/atnsim object because it can only handle one input at a time.
    //  This maps graphs a and b to merged result c. (a,b)&rarr;c. We can avoid
    //  the merge if we ever see a and b again.  Note that (b,a)&rarr;c should
    //  also be examined during cache lookup.
    //
    this.mergeCache = null;
    return this;
}

ParserATNSimulator.prototype = Object.create(_ATNSimulator.ATNSimulator.prototype);
ParserATNSimulator.prototype.constructor = ParserATNSimulator;

ParserATNSimulator.prototype.debug = false;
ParserATNSimulator.prototype.debug_closure = false;
ParserATNSimulator.prototype.debug_add = false;
ParserATNSimulator.prototype.debug_list_atn_decisions = false;
ParserATNSimulator.prototype.dfa_debug = false;
ParserATNSimulator.prototype.retry_debug = false;

ParserATNSimulator.prototype.reset = function () {};

ParserATNSimulator.prototype.adaptivePredict = function (input, decision, outerContext) {
    if (this.debug || this.debug_list_atn_decisions) {
        console.log("adaptivePredict decision " + decision + " exec LA(1)==" + this.getLookaheadName(input) + " line " + input.LT(1).line + ":" + input.LT(1).column);
    }
    this._input = input;
    this._startIndex = input.index;
    this._outerContext = outerContext;

    var dfa = this.decisionToDFA[decision];
    this._dfa = dfa;
    var m = input.mark();
    var index = input.index;

    // Now we are certain to have a specific decision's DFA
    // But, do we still need an initial state?
    try {
        var s0;
        if (dfa.precedenceDfa) {
            // the start state for a precedence DFA depends on the current
            // parser precedence, and is provided by a DFA method.
            s0 = dfa.getPrecedenceStartState(this.parser.getPrecedence());
        } else {
            // the start state for a "regular" DFA is just s0
            s0 = dfa.s0;
        }
        if (s0 === null) {
            if (outerContext === null) {
                outerContext = _RuleContext.RuleContext.EMPTY;
            }
            if (this.debug || this.debug_list_atn_decisions) {
                console.log("predictATN decision " + dfa.decision + " exec LA(1)==" + this.getLookaheadName(input) + ", outerContext=" + outerContext.toString(this.parser.ruleNames));
            }

            var fullCtx = false;
            var s0_closure = this.computeStartState(dfa.atnStartState, _RuleContext.RuleContext.EMPTY, fullCtx);

            if (dfa.precedenceDfa) {
                // If this is a precedence DFA, we use applyPrecedenceFilter
                // to convert the computed start state to a precedence start
                // state. We then use DFA.setPrecedenceStartState to set the
                // appropriate start state for the precedence level rather
                // than simply setting DFA.s0.
                //
                dfa.s0.configs = s0_closure; // not used for prediction but useful to know start configs anyway
                s0_closure = this.applyPrecedenceFilter(s0_closure);
                s0 = this.addDFAState(dfa, new _DFAState.DFAState(null, s0_closure));
                dfa.setPrecedenceStartState(this.parser.getPrecedence(), s0);
            } else {
                s0 = this.addDFAState(dfa, new _DFAState.DFAState(null, s0_closure));
                dfa.s0 = s0;
            }
        }
        var alt = this.execATN(dfa, s0, input, index, outerContext);
        if (this.debug) {
            console.log("DFA after predictATN: " + dfa.toString(this.parser.literalNames));
        }
        return alt;
    } finally {
        this._dfa = null;
        this.mergeCache = null; // wack cache after each prediction
        input.seek(index);
        input.release(m);
    }
};
// Performs ATN simulation to compute a predicted alternative based
//  upon the remaining input, but also updates the DFA cache to avoid
//  having to traverse the ATN again for the same input sequence.

// There are some key conditions we're looking for after computing a new
// set of ATN configs (proposed DFA state):
// if the set is empty, there is no viable alternative for current symbol
// does the state uniquely predict an alternative?
// does the state have a conflict that would prevent us from
//   putting it on the work list?

// We also have some key operations to do:
// add an edge from previous DFA state to potentially new DFA state, D,
//   upon current symbol but only if adding to work list, which means in all
//   cases except no viable alternative (and possibly non-greedy decisions?)
// collecting predicates and adding semantic context to DFA accept states
// adding rule context to context-sensitive DFA accept states
// consuming an input symbol
// reporting a conflict
// reporting an ambiguity
// reporting a context sensitivity
// reporting insufficient predicates

// cover these cases:
//    dead end
//    single alt
//    single alt + preds
//    conflict
//    conflict + preds
//
ParserATNSimulator.prototype.execATN = function (dfa, s0, input, startIndex, outerContext) {
    if (this.debug || this.debug_list_atn_decisions) {
        console.log("execATN decision " + dfa.decision + " exec LA(1)==" + this.getLookaheadName(input) + " line " + input.LT(1).line + ":" + input.LT(1).column);
    }
    var alt;
    var previousD = s0;

    if (this.debug) {
        console.log("s0 = " + s0);
    }
    var t = input.LA(1);
    while (true) {
        // while more work
        var D = this.getExistingTargetState(previousD, t);
        if (D === null) {
            D = this.computeTargetState(dfa, previousD, t);
        }
        if (D === _ATNSimulator.ATNSimulator.ERROR) {
            // if any configs in previous dipped into outer context, that
            // means that input up to t actually finished entry rule
            // at least for SLL decision. Full LL doesn't dip into outer
            // so don't need special case.
            // We will get an error no matter what so delay until after
            // decision; better error message. Also, no reachable target
            // ATN states in SLL implies LL will also get nowhere.
            // If conflict in states that dip out, choose min since we
            // will get error no matter what.
            var e = this.noViableAlt(input, outerContext, previousD.configs, startIndex);
            input.seek(startIndex);
            alt = this.getSynValidOrSemInvalidAltThatFinishedDecisionEntryRule(previousD.configs, outerContext);
            if (alt !== _ATN.ATN.INVALID_ALT_NUMBER) {
                return alt;
            } else {
                throw e;
            }
        }
        if (D.requiresFullContext && this.predictionMode !== _PredictionMode.PredictionMode.SLL) {
            // IF PREDS, MIGHT RESOLVE TO SINGLE ALT => SLL (or syntax error)
            var conflictingAlts = null;
            if (D.predicates !== null) {
                if (this.debug) {
                    console.log("DFA state has preds in DFA sim LL failover");
                }
                var conflictIndex = input.index;
                if (conflictIndex !== startIndex) {
                    input.seek(startIndex);
                }
                conflictingAlts = this.evalSemanticContext(D.predicates, outerContext, true);
                if (conflictingAlts.length === 1) {
                    if (this.debug) {
                        console.log("Full LL avoided");
                    }
                    return conflictingAlts.minValue();
                }
                if (conflictIndex !== startIndex) {
                    // restore the index so reporting the fallback to full
                    // context occurs with the index at the correct spot
                    input.seek(conflictIndex);
                }
            }
            if (this.dfa_debug) {
                console.log("ctx sensitive state " + outerContext + " in " + D);
            }
            var fullCtx = true;
            var s0_closure = this.computeStartState(dfa.atnStartState, outerContext, fullCtx);
            this.reportAttemptingFullContext(dfa, conflictingAlts, D.configs, startIndex, input.index);
            alt = this.execATNWithFullContext(dfa, D, s0_closure, input, startIndex, outerContext);
            return alt;
        }
        if (D.isAcceptState) {
            if (D.predicates === null) {
                return D.prediction;
            }
            var stopIndex = input.index;
            input.seek(startIndex);
            var alts = this.evalSemanticContext(D.predicates, outerContext, true);
            if (alts.length === 0) {
                throw this.noViableAlt(input, outerContext, D.configs, startIndex);
            } else if (alts.length === 1) {
                return alts.minValue();
            } else {
                // report ambiguity after predicate evaluation to make sure the correct set of ambig alts is reported.
                this.reportAmbiguity(dfa, D, startIndex, stopIndex, false, alts, D.configs);
                return alts.minValue();
            }
        }
        previousD = D;

        if (t !== _Token.Token.EOF) {
            input.consume();
            t = input.LA(1);
        }
    }
};
//
// Get an existing target state for an edge in the DFA. If the target state
// for the edge has not yet been computed or is otherwise not available,
// this method returns {@code null}.
//
// @param previousD The current DFA state
// @param t The next input symbol
// @return The existing target DFA state for the given input symbol
// {@code t}, or {@code null} if the target state for this edge is not
// already cached
//
ParserATNSimulator.prototype.getExistingTargetState = function (previousD, t) {
    var edges = previousD.edges;
    if (edges === null) {
        return null;
    } else {
        return edges[t + 1] || null;
    }
};
//
// Compute a target state for an edge in the DFA, and attempt to add the
// computed state and corresponding edge to the DFA.
//
// @param dfa The DFA
// @param previousD The current DFA state
// @param t The next input symbol
//
// @return The computed target DFA state for the given input symbol
// {@code t}. If {@code t} does not lead to a valid DFA state, this method
// returns {@link //ERROR}.
//
ParserATNSimulator.prototype.computeTargetState = function (dfa, previousD, t) {
    var reach = this.computeReachSet(previousD.configs, t, false);
    if (reach === null) {
        this.addDFAEdge(dfa, previousD, t, _ATNSimulator.ATNSimulator.ERROR);
        return _ATNSimulator.ATNSimulator.ERROR;
    }
    // create new target state; we'll add to DFA after it's complete
    var D = new _DFAState.DFAState(null, reach);

    var predictedAlt = this.getUniqueAlt(reach);

    if (this.debug) {
        var altSubSets = _PredictionMode.PredictionMode.getConflictingAltSubsets(reach);
        console.log("SLL altSubSets=" + Utils.arrayToString(altSubSets) + ", previous=" + previousD.configs + ", configs=" + reach + ", predict=" + predictedAlt + ", allSubsetsConflict=" + _PredictionMode.PredictionMode.allSubsetsConflict(altSubSets) + ", conflictingAlts=" + this.getConflictingAlts(reach));
    }
    if (predictedAlt !== _ATN.ATN.INVALID_ALT_NUMBER) {
        // NO CONFLICT, UNIQUELY PREDICTED ALT
        D.isAcceptState = true;
        D.configs.uniqueAlt = predictedAlt;
        D.prediction = predictedAlt;
    } else if (_PredictionMode.PredictionMode.hasSLLConflictTerminatingPrediction(this.predictionMode, reach)) {
        // MORE THAN ONE VIABLE ALTERNATIVE
        D.configs.conflictingAlts = this.getConflictingAlts(reach);
        D.requiresFullContext = true;
        // in SLL-only mode, we will stop at this state and return the minimum alt
        D.isAcceptState = true;
        D.prediction = D.configs.conflictingAlts.minValue();
    }
    if (D.isAcceptState && D.configs.hasSemanticContext) {
        this.predicateDFAState(D, this.atn.getDecisionState(dfa.decision));
        if (D.predicates !== null) {
            D.prediction = _ATN.ATN.INVALID_ALT_NUMBER;
        }
    }
    // all adds to dfa are done after we've created full D state
    D = this.addDFAEdge(dfa, previousD, t, D);
    return D;
};

ParserATNSimulator.prototype.predicateDFAState = function (dfaState, decisionState) {
    // We need to test all predicates, even in DFA states that
    // uniquely predict alternative.
    var nalts = decisionState.transitions.length;
    // Update DFA so reach becomes accept state with (predicate,alt)
    // pairs if preds found for conflicting alts
    var altsToCollectPredsFrom = this.getConflictingAltsOrUniqueAlt(dfaState.configs);
    var altToPred = this.getPredsForAmbigAlts(altsToCollectPredsFrom, dfaState.configs, nalts);
    if (altToPred !== null) {
        dfaState.predicates = this.getPredicatePredictions(altsToCollectPredsFrom, altToPred);
        dfaState.prediction = _ATN.ATN.INVALID_ALT_NUMBER; // make sure we use preds
    } else {
        // There are preds in configs but they might go away
        // when OR'd together like {p}? || NONE == NONE. If neither
        // alt has preds, resolve to min alt
        dfaState.prediction = altsToCollectPredsFrom.minValue();
    }
};

// comes back with reach.uniqueAlt set to a valid alt
ParserATNSimulator.prototype.execATNWithFullContext = function (dfa, D, // how far we got before failing over
s0, input, startIndex, outerContext) {
    if (this.debug || this.debug_list_atn_decisions) {
        console.log("execATNWithFullContext " + s0);
    }
    var fullCtx = true;
    var foundExactAmbig = false;
    var reach = null;
    var previous = s0;
    input.seek(startIndex);
    var t = input.LA(1);
    var predictedAlt = -1;
    while (true) {
        // while more work
        reach = this.computeReachSet(previous, t, fullCtx);
        if (reach === null) {
            // if any configs in previous dipped into outer context, that
            // means that input up to t actually finished entry rule
            // at least for LL decision. Full LL doesn't dip into outer
            // so don't need special case.
            // We will get an error no matter what so delay until after
            // decision; better error message. Also, no reachable target
            // ATN states in SLL implies LL will also get nowhere.
            // If conflict in states that dip out, choose min since we
            // will get error no matter what.
            var e = this.noViableAlt(input, outerContext, previous, startIndex);
            input.seek(startIndex);
            var alt = this.getSynValidOrSemInvalidAltThatFinishedDecisionEntryRule(previous, outerContext);
            if (alt !== _ATN.ATN.INVALID_ALT_NUMBER) {
                return alt;
            } else {
                throw e;
            }
        }
        var altSubSets = _PredictionMode.PredictionMode.getConflictingAltSubsets(reach);
        if (this.debug) {
            console.log("LL altSubSets=" + altSubSets + ", predict=" + _PredictionMode.PredictionMode.getUniqueAlt(altSubSets) + ", resolvesToJustOneViableAlt=" + _PredictionMode.PredictionMode.resolvesToJustOneViableAlt(altSubSets));
        }
        reach.uniqueAlt = this.getUniqueAlt(reach);
        // unique prediction?
        if (reach.uniqueAlt !== _ATN.ATN.INVALID_ALT_NUMBER) {
            predictedAlt = reach.uniqueAlt;
            break;
        } else if (this.predictionMode !== _PredictionMode.PredictionMode.LL_EXACT_AMBIG_DETECTION) {
            predictedAlt = _PredictionMode.PredictionMode.resolvesToJustOneViableAlt(altSubSets);
            if (predictedAlt !== _ATN.ATN.INVALID_ALT_NUMBER) {
                break;
            }
        } else {
            // In exact ambiguity mode, we never try to terminate early.
            // Just keeps scarfing until we know what the conflict is
            if (_PredictionMode.PredictionMode.allSubsetsConflict(altSubSets) && _PredictionMode.PredictionMode.allSubsetsEqual(altSubSets)) {
                foundExactAmbig = true;
                predictedAlt = _PredictionMode.PredictionMode.getSingleViableAlt(altSubSets);
                break;
            }
            // else there are multiple non-conflicting subsets or
            // we're not sure what the ambiguity is yet.
            // So, keep going.
        }
        previous = reach;
        if (t !== _Token.Token.EOF) {
            input.consume();
            t = input.LA(1);
        }
    }
    // If the configuration set uniquely predicts an alternative,
    // without conflict, then we know that it's a full LL decision
    // not SLL.
    if (reach.uniqueAlt !== _ATN.ATN.INVALID_ALT_NUMBER) {
        this.reportContextSensitivity(dfa, predictedAlt, reach, startIndex, input.index);
        return predictedAlt;
    }
    // We do not check predicates here because we have checked them
    // on-the-fly when doing full context prediction.

    //
    // In non-exact ambiguity detection mode, we might	actually be able to
    // detect an exact ambiguity, but I'm not going to spend the cycles
    // needed to check. We only emit ambiguity warnings in exact ambiguity
    // mode.
    //
    // For example, we might know that we have conflicting configurations.
    // But, that does not mean that there is no way forward without a
    // conflict. It's possible to have nonconflicting alt subsets as in:

    // altSubSets=[{1, 2}, {1, 2}, {1}, {1, 2}]

    // from
    //
    //    [(17,1,[5 $]), (13,1,[5 10 $]), (21,1,[5 10 $]), (11,1,[$]),
    //     (13,2,[5 10 $]), (21,2,[5 10 $]), (11,2,[$])]
    //
    // In this case, (17,1,[5 $]) indicates there is some next sequence that
    // would resolve this without conflict to alternative 1. Any other viable
    // next sequence, however, is associated with a conflict.  We stop
    // looking for input because no amount of further lookahead will alter
    // the fact that we should predict alternative 1.  We just can't say for
    // sure that there is an ambiguity without looking further.

    this.reportAmbiguity(dfa, D, startIndex, input.index, foundExactAmbig, null, reach);

    return predictedAlt;
};

ParserATNSimulator.prototype.computeReachSet = function (closure, t, fullCtx) {
    if (this.debug) {
        console.log("in computeReachSet, starting closure: " + closure);
    }
    if (this.mergeCache === null) {
        this.mergeCache = new DoubleDict();
    }
    var intermediate = new _ATNConfigSet.ATNConfigSet(fullCtx);

    // Configurations already in a rule stop state indicate reaching the end
    // of the decision rule (local context) or end of the start rule (full
    // context). Once reached, these configurations are never updated by a
    // closure operation, so they are handled separately for the performance
    // advantage of having a smaller intermediate set when calling closure.
    //
    // For full-context reach operations, separate handling is required to
    // ensure that the alternative matching the longest overall sequence is
    // chosen when multiple such configurations can match the input.

    var skippedStopStates = null;

    // First figure out where we can reach on input t
    for (var i = 0; i < closure.items.length; i++) {
        var c = closure.items[i];
        if (this.debug_add) {
            console.log("testing " + this.getTokenName(t) + " at " + c);
        }
        if (c.state instanceof _ATNState.RuleStopState) {
            if (fullCtx || t === _Token.Token.EOF) {
                if (skippedStopStates === null) {
                    skippedStopStates = [];
                }
                skippedStopStates.push(c);
                if (this.debug_add) {
                    console.log("added " + c + " to skippedStopStates");
                }
            }
            continue;
        }
        for (var j = 0; j < c.state.transitions.length; j++) {
            var trans = c.state.transitions[j];
            var target = this.getReachableTarget(trans, t);
            if (target !== null) {
                var cfg = new _ATNConfig.ATNConfig({ state: target }, c);
                intermediate.add(cfg, this.mergeCache);
                if (this.debug_add) {
                    console.log("added " + cfg + " to intermediate");
                }
            }
        }
    }
    // Now figure out where the reach operation can take us...
    var reach = null;

    // This block optimizes the reach operation for intermediate sets which
    // trivially indicate a termination state for the overall
    // adaptivePredict operation.
    //
    // The conditions assume that intermediate
    // contains all configurations relevant to the reach set, but this
    // condition is not true when one or more configurations have been
    // withheld in skippedStopStates, or when the current symbol is EOF.
    //
    if (skippedStopStates === null && t !== _Token.Token.EOF) {
        if (intermediate.items.length === 1) {
            // Don't pursue the closure if there is just one state.
            // It can only have one alternative; just add to result
            // Also don't pursue the closure if there is unique alternative
            // among the configurations.
            reach = intermediate;
        } else if (this.getUniqueAlt(intermediate) !== _ATN.ATN.INVALID_ALT_NUMBER) {
            // Also don't pursue the closure if there is unique alternative
            // among the configurations.
            reach = intermediate;
        }
    }
    // If the reach set could not be trivially determined, perform a closure
    // operation on the intermediate set to compute its initial value.
    //
    if (reach === null) {
        reach = new _ATNConfigSet.ATNConfigSet(fullCtx);
        var closureBusy = new Set();
        var treatEofAsEpsilon = t === _Token.Token.EOF;
        for (var k = 0; k < intermediate.items.length; k++) {
            this.closure(intermediate.items[k], reach, closureBusy, false, fullCtx, treatEofAsEpsilon);
        }
    }
    if (t === _Token.Token.EOF) {
        // After consuming EOF no additional input is possible, so we are
        // only interested in configurations which reached the end of the
        // decision rule (local context) or end of the start rule (full
        // context). Update reach to contain only these configurations. This
        // handles both explicit EOF transitions in the grammar and implicit
        // EOF transitions following the end of the decision or start rule.
        //
        // When reach==intermediate, no closure operation was performed. In
        // this case, removeAllConfigsNotInRuleStopState needs to check for
        // reachable rule stop states as well as configurations already in
        // a rule stop state.
        //
        // This is handled before the configurations in skippedStopStates,
        // because any configurations potentially added from that list are
        // already guaranteed to meet this condition whether or not it's
        // required.
        //
        reach = this.removeAllConfigsNotInRuleStopState(reach, reach === intermediate);
    }
    // If skippedStopStates!==null, then it contains at least one
    // configuration. For full-context reach operations, these
    // configurations reached the end of the start rule, in which case we
    // only add them back to reach if no configuration during the current
    // closure operation reached such a state. This ensures adaptivePredict
    // chooses an alternative matching the longest overall sequence when
    // multiple alternatives are viable.
    //
    if (skippedStopStates !== null && (!fullCtx || !_PredictionMode.PredictionMode.hasConfigInRuleStopState(reach))) {
        for (var l = 0; l < skippedStopStates.length; l++) {
            reach.add(skippedStopStates[l], this.mergeCache);
        }
    }
    if (reach.items.length === 0) {
        return null;
    } else {
        return reach;
    }
};
//
// Return a configuration set containing only the configurations from
// {@code configs} which are in a {@link RuleStopState}. If all
// configurations in {@code configs} are already in a rule stop state, this
// method simply returns {@code configs}.
//
// <p>When {@code lookToEndOfRule} is true, this method uses
// {@link ATN//nextTokens} for each configuration in {@code configs} which is
// not already in a rule stop state to see if a rule stop state is reachable
// from the configuration via epsilon-only transitions.</p>
//
// @param configs the configuration set to update
// @param lookToEndOfRule when true, this method checks for rule stop states
// reachable by epsilon-only transitions from each configuration in
// {@code configs}.
//
// @return {@code configs} if all configurations in {@code configs} are in a
// rule stop state, otherwise return a new configuration set containing only
// the configurations from {@code configs} which are in a rule stop state
//
ParserATNSimulator.prototype.removeAllConfigsNotInRuleStopState = function (configs, lookToEndOfRule) {
    if (_PredictionMode.PredictionMode.allConfigsInRuleStopStates(configs)) {
        return configs;
    }
    var result = new _ATNConfigSet.ATNConfigSet(configs.fullCtx);
    for (var i = 0; i < configs.items.length; i++) {
        var config = configs.items[i];
        if (config.state instanceof _ATNState.RuleStopState) {
            result.add(config, this.mergeCache);
            continue;
        }
        if (lookToEndOfRule && config.state.epsilonOnlyTransitions) {
            var nextTokens = this.atn.nextTokens(config.state);
            if (nextTokens.contains(_Token.Token.EPSILON)) {
                var endOfRuleState = this.atn.ruleToStopState[config.state.ruleIndex];
                result.add(new _ATNConfig.ATNConfig({ state: endOfRuleState }, config), this.mergeCache);
            }
        }
    }
    return result;
};

ParserATNSimulator.prototype.computeStartState = function (p, ctx, fullCtx) {
    // always at least the implicit call to start rule
    var initialContext = (0, _PredictionContext.predictionContextFromRuleContext)(this.atn, ctx);
    var configs = new _ATNConfigSet.ATNConfigSet(fullCtx);
    for (var i = 0; i < p.transitions.length; i++) {
        var target = p.transitions[i].target;
        var c = new _ATNConfig.ATNConfig({ state: target, alt: i + 1, context: initialContext }, null);
        var closureBusy = new Set();
        this.closure(c, configs, closureBusy, true, fullCtx, false);
    }
    return configs;
};

//
// This method transforms the start state computed by
// {@link //computeStartState} to the special start state used by a
// precedence DFA for a particular precedence value. The transformation
// process applies the following changes to the start state's configuration
// set.
//
// <ol>
// <li>Evaluate the precedence predicates for each configuration using
// {@link SemanticContext//evalPrecedence}.</li>
// <li>Remove all configurations which predict an alternative greater than
// 1, for which another configuration that predicts alternative 1 is in the
// same ATN state with the same prediction context. This transformation is
// valid for the following reasons:
// <ul>
// <li>The closure block cannot contain any epsilon transitions which bypass
// the body of the closure, so all states reachable via alternative 1 are
// part of the precedence alternatives of the transformed left-recursive
// rule.</li>
// <li>The "primary" portion of a left recursive rule cannot contain an
// epsilon transition, so the only way an alternative other than 1 can exist
// in a state that is also reachable via alternative 1 is by nesting calls
// to the left-recursive rule, with the outer calls not being at the
// preferred precedence level.</li>
// </ul>
// </li>
// </ol>
//
// <p>
// The prediction context must be considered by this filter to address
// situations like the following.
// </p>
// <code>
// <pre>
// grammar TA;
// prog: statement* EOF;
// statement: letterA | statement letterA 'b' ;
// letterA: 'a';
// </pre>
// </code>
// <p>
// If the above grammar, the ATN state immediately before the token
// reference {@code 'a'} in {@code letterA} is reachable from the left edge
// of both the primary and closure blocks of the left-recursive rule
// {@code statement}. The prediction context associated with each of these
// configurations distinguishes between them, and prevents the alternative
// which stepped out to {@code prog} (and then back in to {@code statement}
// from being eliminated by the filter.
// </p>
//
// @param configs The configuration set computed by
// {@link //computeStartState} as the start state for the DFA.
// @return The transformed configuration set representing the start state
// for a precedence DFA at a particular precedence level (determined by
// calling {@link Parser//getPrecedence}).
//
ParserATNSimulator.prototype.applyPrecedenceFilter = function (configs) {
    var config;
    var statesFromAlt1 = [];
    var configSet = new _ATNConfigSet.ATNConfigSet(configs.fullCtx);
    for (var i = 0; i < configs.items.length; i++) {
        config = configs.items[i];
        // handle alt 1 first
        if (config.alt !== 1) {
            continue;
        }
        var updatedContext = config.semanticContext.evalPrecedence(this.parser, this._outerContext);
        if (updatedContext === null) {
            // the configuration was eliminated
            continue;
        }
        statesFromAlt1[config.state.stateNumber] = config.context;
        if (updatedContext !== config.semanticContext) {
            configSet.add(new _ATNConfig.ATNConfig({ semanticContext: updatedContext }, config), this.mergeCache);
        } else {
            configSet.add(config, this.mergeCache);
        }
    }
    for (i = 0; i < configs.items.length; i++) {
        config = configs.items[i];
        if (config.alt === 1) {
            // already handled
            continue;
        }
        // In the future, this elimination step could be updated to also
        // filter the prediction context for alternatives predicting alt>1
        // (basically a graph subtraction algorithm).
        if (!config.precedenceFilterSuppressed) {
            var context = statesFromAlt1[config.state.stateNumber] || null;
            if (context !== null && context.equals(config.context)) {
                // eliminated
                continue;
            }
        }
        configSet.add(config, this.mergeCache);
    }
    return configSet;
};

ParserATNSimulator.prototype.getReachableTarget = function (trans, ttype) {
    if (trans.matches(ttype, 0, this.atn.maxTokenType)) {
        return trans.target;
    } else {
        return null;
    }
};

ParserATNSimulator.prototype.getPredsForAmbigAlts = function (ambigAlts, configs, nalts) {
    // REACH=[1|1|[]|0:0, 1|2|[]|0:1]
    // altToPred starts as an array of all null contexts. The entry at index i
    // corresponds to alternative i. altToPred[i] may have one of three values:
    //   1. null: no ATNConfig c is found such that c.alt==i
    //   2. SemanticContext.NONE: At least one ATNConfig c exists such that
    //      c.alt==i and c.semanticContext==SemanticContext.NONE. In other words,
    //      alt i has at least one unpredicated config.
    //   3. Non-NONE Semantic Context: There exists at least one, and for all
    //      ATNConfig c such that c.alt==i, c.semanticContext!=SemanticContext.NONE.
    //
    // From this, it is clear that NONE||anything==NONE.
    //
    var altToPred = [];
    for (var i = 0; i < configs.items.length; i++) {
        var c = configs.items[i];
        if (ambigAlts.contains(c.alt)) {
            altToPred[c.alt] = _SemanticContext.SemanticContext.orContext(altToPred[c.alt] || null, c.semanticContext);
        }
    }
    var nPredAlts = 0;
    for (i = 1; i < nalts + 1; i++) {
        var pred = altToPred[i] || null;
        if (pred === null) {
            altToPred[i] = _SemanticContext.SemanticContext.NONE;
        } else if (pred !== _SemanticContext.SemanticContext.NONE) {
            nPredAlts += 1;
        }
    }
    // nonambig alts are null in altToPred
    if (nPredAlts === 0) {
        altToPred = null;
    }
    if (this.debug) {
        console.log("getPredsForAmbigAlts result " + Utils.arrayToString(altToPred));
    }
    return altToPred;
};

ParserATNSimulator.prototype.getPredicatePredictions = function (ambigAlts, altToPred) {
    var pairs = [];
    var containsPredicate = false;
    for (var i = 1; i < altToPred.length; i++) {
        var pred = altToPred[i];
        // unpredicated is indicated by SemanticContext.NONE
        if (ambigAlts !== null && ambigAlts.contains(i)) {
            pairs.push(new _DFAState.PredPrediction(pred, i));
        }
        if (pred !== _SemanticContext.SemanticContext.NONE) {
            containsPredicate = true;
        }
    }
    if (!containsPredicate) {
        return null;
    }
    return pairs;
};

//
// This method is used to improve the localization of error messages by
// choosing an alternative rather than throwing a
// {@link NoViableAltException} in particular prediction scenarios where the
// {@link //ERROR} state was reached during ATN simulation.
//
// <p>
// The default implementation of this method uses the following
// algorithm to identify an ATN configuration which successfully parsed the
// decision entry rule. Choosing such an alternative ensures that the
// {@link ParserRuleContext} returned by the calling rule will be complete
// and valid, and the syntax error will be reported later at a more
// localized location.</p>
//
// <ul>
// <li>If a syntactically valid path or paths reach the end of the decision rule and
// they are semantically valid if predicated, return the min associated alt.</li>
// <li>Else, if a semantically invalid but syntactically valid path exist
// or paths exist, return the minimum associated alt.
// </li>
// <li>Otherwise, return {@link ATN//INVALID_ALT_NUMBER}.</li>
// </ul>
//
// <p>
// In some scenarios, the algorithm described above could predict an
// alternative which will result in a {@link FailedPredicateException} in
// the parser. Specifically, this could occur if the <em>only</em> configuration
// capable of successfully parsing to the end of the decision rule is
// blocked by a semantic predicate. By choosing this alternative within
// {@link //adaptivePredict} instead of throwing a
// {@link NoViableAltException}, the resulting
// {@link FailedPredicateException} in the parser will identify the specific
// predicate which is preventing the parser from successfully parsing the
// decision rule, which helps developers identify and correct logic errors
// in semantic predicates.
// </p>
//
// @param configs The ATN configurations which were valid immediately before
// the {@link //ERROR} state was reached
// @param outerContext The is the \gamma_0 initial parser context from the paper
// or the parser stack at the instant before prediction commences.
//
// @return The value to return from {@link //adaptivePredict}, or
// {@link ATN//INVALID_ALT_NUMBER} if a suitable alternative was not
// identified and {@link //adaptivePredict} should report an error instead.
//
ParserATNSimulator.prototype.getSynValidOrSemInvalidAltThatFinishedDecisionEntryRule = function (configs, outerContext) {
    var cfgs = this.splitAccordingToSemanticValidity(configs, outerContext);
    var semValidConfigs = cfgs[0];
    var semInvalidConfigs = cfgs[1];
    var alt = this.getAltThatFinishedDecisionEntryRule(semValidConfigs);
    if (alt !== _ATN.ATN.INVALID_ALT_NUMBER) {
        // semantically/syntactically viable path exists
        return alt;
    }
    // Is there a syntactically valid path with a failed pred?
    if (semInvalidConfigs.items.length > 0) {
        alt = this.getAltThatFinishedDecisionEntryRule(semInvalidConfigs);
        if (alt !== _ATN.ATN.INVALID_ALT_NUMBER) {
            // syntactically viable path exists
            return alt;
        }
    }
    return _ATN.ATN.INVALID_ALT_NUMBER;
};

ParserATNSimulator.prototype.getAltThatFinishedDecisionEntryRule = function (configs) {
    var alts = [];
    for (var i = 0; i < configs.items.length; i++) {
        var c = configs.items[i];
        if (c.reachesIntoOuterContext > 0 || c.state instanceof _ATNState.RuleStopState && c.context.hasEmptyPath()) {
            if (alts.indexOf(c.alt) < 0) {
                alts.push(c.alt);
            }
        }
    }
    if (alts.length === 0) {
        return _ATN.ATN.INVALID_ALT_NUMBER;
    } else {
        return Math.min.apply(null, alts);
    }
};
// Walk the list of configurations and split them according to
//  those that have preds evaluating to true/false.  If no pred, assume
//  true pred and include in succeeded set.  Returns Pair of sets.
//
//  Create a new set so as not to alter the incoming parameter.
//
//  Assumption: the input stream has been restored to the starting point
//  prediction, which is where predicates need to evaluate.
//
ParserATNSimulator.prototype.splitAccordingToSemanticValidity = function (configs, outerContext) {
    var succeeded = new _ATNConfigSet.ATNConfigSet(configs.fullCtx);
    var failed = new _ATNConfigSet.ATNConfigSet(configs.fullCtx);
    for (var i = 0; i < configs.items.length; i++) {
        var c = configs.items[i];
        if (c.semanticContext !== _SemanticContext.SemanticContext.NONE) {
            var predicateEvaluationResult = c.semanticContext.evaluate(this.parser, outerContext);
            if (predicateEvaluationResult) {
                succeeded.add(c);
            } else {
                failed.add(c);
            }
        } else {
            succeeded.add(c);
        }
    }
    return [succeeded, failed];
};

// Look through a list of predicate/alt pairs, returning alts for the
//  pairs that win. A {@code NONE} predicate indicates an alt containing an
//  unpredicated config which behaves as "always true." If !complete
//  then we stop at the first predicate that evaluates to true. This
//  includes pairs with null predicates.
//
ParserATNSimulator.prototype.evalSemanticContext = function (predPredictions, outerContext, complete) {
    var predictions = new BitSet();
    for (var i = 0; i < predPredictions.length; i++) {
        var pair = predPredictions[i];
        if (pair.pred === _SemanticContext.SemanticContext.NONE) {
            predictions.add(pair.alt);
            if (!complete) {
                break;
            }
            continue;
        }
        var predicateEvaluationResult = pair.pred.evaluate(this.parser, outerContext);
        if (this.debug || this.dfa_debug) {
            console.log("eval pred " + pair + "=" + predicateEvaluationResult);
        }
        if (predicateEvaluationResult) {
            if (this.debug || this.dfa_debug) {
                console.log("PREDICT " + pair.alt);
            }
            predictions.add(pair.alt);
            if (!complete) {
                break;
            }
        }
    }
    return predictions;
};

// TODO: If we are doing predicates, there is no point in pursuing
//     closure operations if we reach a DFA state that uniquely predicts
//     alternative. We will not be caching that DFA state and it is a
//     waste to pursue the closure. Might have to advance when we do
//     ambig detection thought :(
//

ParserATNSimulator.prototype.closure = function (config, configs, closureBusy, collectPredicates, fullCtx, treatEofAsEpsilon) {
    var initialDepth = 0;
    this.closureCheckingStopState(config, configs, closureBusy, collectPredicates, fullCtx, initialDepth, treatEofAsEpsilon);
};

ParserATNSimulator.prototype.closureCheckingStopState = function (config, configs, closureBusy, collectPredicates, fullCtx, depth, treatEofAsEpsilon) {
    if (this.debug || this.debug_closure) {
        console.log("closure(" + config.toString(this.parser, true) + ")");
        // console.log("configs(" + configs.toString() + ")");
        if (config.reachesIntoOuterContext > 50) {
            throw "problem";
        }
    }
    if (config.state instanceof _ATNState.RuleStopState) {
        // We hit rule end. If we have context info, use it
        // run thru all possible stack tops in ctx
        if (!config.context.isEmpty()) {
            for (var i = 0; i < config.context.length; i++) {
                if (config.context.getReturnState(i) === _PredictionContext.PredictionContext.EMPTY_RETURN_STATE) {
                    if (fullCtx) {
                        configs.add(new _ATNConfig.ATNConfig({ state: config.state, context: _PredictionContext.PredictionContext.EMPTY }, config), this.mergeCache);
                        continue;
                    } else {
                        // we have no context info, just chase follow links (if greedy)
                        if (this.debug) {
                            console.log("FALLING off rule " + this.getRuleName(config.state.ruleIndex));
                        }
                        this.closure_(config, configs, closureBusy, collectPredicates, fullCtx, depth, treatEofAsEpsilon);
                    }
                    continue;
                }
                var returnState = this.atn.states[config.context.getReturnState(i)];
                var newContext = config.context.getParent(i); // "pop" return state
                var parms = { state: returnState, alt: config.alt, context: newContext, semanticContext: config.semanticContext };
                var c = new _ATNConfig.ATNConfig(parms, null);
                // While we have context to pop back from, we may have
                // gotten that context AFTER having falling off a rule.
                // Make sure we track that we are now out of context.
                c.reachesIntoOuterContext = config.reachesIntoOuterContext;
                this.closureCheckingStopState(c, configs, closureBusy, collectPredicates, fullCtx, depth - 1, treatEofAsEpsilon);
            }
            return;
        } else if (fullCtx) {
            // reached end of start rule
            configs.add(config, this.mergeCache);
            return;
        } else {
            // else if we have no context info, just chase follow links (if greedy)
            if (this.debug) {
                console.log("FALLING off rule " + this.getRuleName(config.state.ruleIndex));
            }
        }
    }
    this.closure_(config, configs, closureBusy, collectPredicates, fullCtx, depth, treatEofAsEpsilon);
};

// Do the actual work of walking epsilon edges//
ParserATNSimulator.prototype.closure_ = function (config, configs, closureBusy, collectPredicates, fullCtx, depth, treatEofAsEpsilon) {
    var p = config.state;
    // optimization
    if (!p.epsilonOnlyTransitions) {
        configs.add(config, this.mergeCache);
        // make sure to not return here, because EOF transitions can act as
        // both epsilon transitions and non-epsilon transitions.
    }
    for (var i = 0; i < p.transitions.length; i++) {
        if (i == 0 && this.canDropLoopEntryEdgeInLeftRecursiveRule(config)) continue;

        var t = p.transitions[i];
        var continueCollecting = collectPredicates && !(t instanceof ActionTransition);
        var c = this.getEpsilonTarget(config, t, continueCollecting, depth === 0, fullCtx, treatEofAsEpsilon);
        if (c !== null) {
            var newDepth = depth;
            if (config.state instanceof _ATNState.RuleStopState) {
                // target fell off end of rule; mark resulting c as having dipped into outer context
                // We can't get here if incoming config was rule stop and we had context
                // track how far we dip into outer context.  Might
                // come in handy and we avoid evaluating context dependent
                // preds if this is > 0.
                if (this._dfa !== null && this._dfa.precedenceDfa) {
                    if (t.outermostPrecedenceReturn === this._dfa.atnStartState.ruleIndex) {
                        c.precedenceFilterSuppressed = true;
                    }
                }

                c.reachesIntoOuterContext += 1;
                if (closureBusy.add(c) !== c) {
                    // avoid infinite recursion for right-recursive rules
                    continue;
                }
                configs.dipsIntoOuterContext = true; // TODO: can remove? only care when we add to set per middle of this method
                newDepth -= 1;
                if (this.debug) {
                    console.log("dips into outer ctx: " + c);
                }
            } else {
                if (!t.isEpsilon && closureBusy.add(c) !== c) {
                    // avoid infinite recursion for EOF* and EOF+
                    continue;
                }
                if (t instanceof RuleTransition) {
                    // latch when newDepth goes negative - once we step out of the entry context we can't return
                    if (newDepth >= 0) {
                        newDepth += 1;
                    }
                }
            }
            this.closureCheckingStopState(c, configs, closureBusy, continueCollecting, fullCtx, newDepth, treatEofAsEpsilon);
        }
    }
};

ParserATNSimulator.prototype.canDropLoopEntryEdgeInLeftRecursiveRule = function (config) {
    // return False
    var p = config.state;
    // First check to see if we are in StarLoopEntryState generated during
    // left-recursion elimination. For efficiency, also check if
    // the context has an empty stack case. If so, it would mean
    // global FOLLOW so we can't perform optimization
    // Are we the special loop entry/exit state? or SLL wildcard
    if (p.stateType != _ATNState.ATNState.STAR_LOOP_ENTRY) return false;
    if (p.stateType != _ATNState.ATNState.STAR_LOOP_ENTRY || !p.isPrecedenceDecision || config.context.isEmpty() || config.context.hasEmptyPath()) return false;

    // Require all return states to return back to the same rule that p is in.
    var numCtxs = config.context.length;
    for (var i = 0; i < numCtxs; i++) {
        // for each stack context
        var returnState = this.atn.states[config.context.getReturnState(i)];
        if (returnState.ruleIndex != p.ruleIndex) return false;
    }

    var decisionStartState = p.transitions[0].target;
    var blockEndStateNum = decisionStartState.endState.stateNumber;
    var blockEndState = this.atn.states[blockEndStateNum];

    // Verify that the top of each stack context leads to loop entry/exit
    // state through epsilon edges and w/o leaving rule.
    for (var i = 0; i < numCtxs; i++) {
        // for each stack context
        var returnStateNumber = config.context.getReturnState(i);
        var returnState = this.atn.states[returnStateNumber];
        // all states must have single outgoing epsilon edge
        if (returnState.transitions.length != 1 || !returnState.transitions[0].isEpsilon) return false;

        // Look for prefix op case like 'not expr', (' type ')' expr
        var returnStateTarget = returnState.transitions[0].target;
        if (returnState.stateType == _ATNState.ATNState.BLOCK_END && returnStateTarget == p) continue;

        // Look for 'expr op expr' or case where expr's return state is block end
        // of (...)* internal block; the block end points to loop back
        // which points to p but we don't need to check that
        if (returnState == blockEndState) continue;

        // Look for ternary expr ? expr : expr. The return state points at block end,
        // which points at loop entry state
        if (returnStateTarget == blockEndState) continue;

        // Look for complex prefix 'between expr and expr' case where 2nd expr's
        // return state points at block end state of (...)* internal block
        if (returnStateTarget.stateType == _ATNState.ATNState.BLOCK_END && returnStateTarget.transitions.length == 1 && returnStateTarget.transitions[0].isEpsilon && returnStateTarget.transitions[0].target == p) continue;

        // anything else ain't conforming
        return false;
    }
    return true;
};

ParserATNSimulator.prototype.getRuleName = function (index) {
    if (this.parser !== null && index >= 0) {
        return this.parser.ruleNames[index];
    } else {
        return "<rule " + index + ">";
    }
};

ParserATNSimulator.prototype.getEpsilonTarget = function (config, t, collectPredicates, inContext, fullCtx, treatEofAsEpsilon) {
    switch (t.serializationType) {
        case Transition.RULE:
            return this.ruleTransition(config, t);
        case Transition.PRECEDENCE:
            return this.precedenceTransition(config, t, collectPredicates, inContext, fullCtx);
        case Transition.PREDICATE:
            return this.predTransition(config, t, collectPredicates, inContext, fullCtx);
        case Transition.ACTION:
            return this.actionTransition(config, t);
        case Transition.EPSILON:
            return new _ATNConfig.ATNConfig({ state: t.target }, config);
        case Transition.ATOM:
        case Transition.RANGE:
        case Transition.SET:
            // EOF transitions act like epsilon transitions after the first EOF
            // transition is traversed
            if (treatEofAsEpsilon) {
                if (t.matches(_Token.Token.EOF, 0, 1)) {
                    return new _ATNConfig.ATNConfig({ state: t.target }, config);
                }
            }
            return null;
        default:
            return null;
    }
};

ParserATNSimulator.prototype.actionTransition = function (config, t) {
    if (this.debug) {
        var index = t.actionIndex == -1 ? 65535 : t.actionIndex;
        console.log("ACTION edge " + t.ruleIndex + ":" + index);
    }
    return new _ATNConfig.ATNConfig({ state: t.target }, config);
};

ParserATNSimulator.prototype.precedenceTransition = function (config, pt, collectPredicates, inContext, fullCtx) {
    if (this.debug) {
        console.log("PRED (collectPredicates=" + collectPredicates + ") " + pt.precedence + ">=_p, ctx dependent=true");
        if (this.parser !== null) {
            console.log("context surrounding pred is " + Utils.arrayToString(this.parser.getRuleInvocationStack()));
        }
    }
    var c = null;
    if (collectPredicates && inContext) {
        if (fullCtx) {
            // In full context mode, we can evaluate predicates on-the-fly
            // during closure, which dramatically reduces the size of
            // the config sets. It also obviates the need to test predicates
            // later during conflict resolution.
            var currentPosition = this._input.index;
            this._input.seek(this._startIndex);
            var predSucceeds = pt.getPredicate().evaluate(this.parser, this._outerContext);
            this._input.seek(currentPosition);
            if (predSucceeds) {
                c = new _ATNConfig.ATNConfig({ state: pt.target }, config); // no pred context
            }
        } else {
            var newSemCtx = _SemanticContext.SemanticContext.andContext(config.semanticContext, pt.getPredicate());
            c = new _ATNConfig.ATNConfig({ state: pt.target, semanticContext: newSemCtx }, config);
        }
    } else {
        c = new _ATNConfig.ATNConfig({ state: pt.target }, config);
    }
    if (this.debug) {
        console.log("config from pred transition=" + c);
    }
    return c;
};

ParserATNSimulator.prototype.predTransition = function (config, pt, collectPredicates, inContext, fullCtx) {
    if (this.debug) {
        console.log("PRED (collectPredicates=" + collectPredicates + ") " + pt.ruleIndex + ":" + pt.predIndex + ", ctx dependent=" + pt.isCtxDependent);
        if (this.parser !== null) {
            console.log("context surrounding pred is " + Utils.arrayToString(this.parser.getRuleInvocationStack()));
        }
    }
    var c = null;
    if (collectPredicates && (pt.isCtxDependent && inContext || !pt.isCtxDependent)) {
        if (fullCtx) {
            // In full context mode, we can evaluate predicates on-the-fly
            // during closure, which dramatically reduces the size of
            // the config sets. It also obviates the need to test predicates
            // later during conflict resolution.
            var currentPosition = this._input.index;
            this._input.seek(this._startIndex);
            var predSucceeds = pt.getPredicate().evaluate(this.parser, this._outerContext);
            this._input.seek(currentPosition);
            if (predSucceeds) {
                c = new _ATNConfig.ATNConfig({ state: pt.target }, config); // no pred context
            }
        } else {
            var newSemCtx = _SemanticContext.SemanticContext.andContext(config.semanticContext, pt.getPredicate());
            c = new _ATNConfig.ATNConfig({ state: pt.target, semanticContext: newSemCtx }, config);
        }
    } else {
        c = new _ATNConfig.ATNConfig({ state: pt.target }, config);
    }
    if (this.debug) {
        console.log("config from pred transition=" + c);
    }
    return c;
};

ParserATNSimulator.prototype.ruleTransition = function (config, t) {
    if (this.debug) {
        console.log("CALL rule " + this.getRuleName(t.target.ruleIndex) + ", ctx=" + config.context);
    }
    var returnState = t.followState;
    var newContext = _PredictionContext.SingletonPredictionContext.create(config.context, returnState.stateNumber);
    return new _ATNConfig.ATNConfig({ state: t.target, context: newContext }, config);
};

ParserATNSimulator.prototype.getConflictingAlts = function (configs) {
    var altsets = _PredictionMode.PredictionMode.getConflictingAltSubsets(configs);
    return _PredictionMode.PredictionMode.getAlts(altsets);
};

// Sam pointed out a problem with the previous definition, v3, of
// ambiguous states. If we have another state associated with conflicting
// alternatives, we should keep going. For example, the following grammar
//
// s : (ID | ID ID?) ';' ;
//
// When the ATN simulation reaches the state before ';', it has a DFA
// state that looks like: [12|1|[], 6|2|[], 12|2|[]]. Naturally
// 12|1|[] and 12|2|[] conflict, but we cannot stop processing this node
// because alternative to has another way to continue, via [6|2|[]].
// The key is that we have a single state that has config's only associated
// with a single alternative, 2, and crucially the state transitions
// among the configurations are all non-epsilon transitions. That means
// we don't consider any conflicts that include alternative 2. So, we
// ignore the conflict between alts 1 and 2. We ignore a set of
// conflicting alts when there is an intersection with an alternative
// associated with a single alt state in the state&rarr;config-list map.
//
// It's also the case that we might have two conflicting configurations but
// also a 3rd nonconflicting configuration for a different alternative:
// [1|1|[], 1|2|[], 8|3|[]]. This can come about from grammar:
//
// a : A | A | A B ;
//
// After matching input A, we reach the stop state for rule A, state 1.
// State 8 is the state right before B. Clearly alternatives 1 and 2
// conflict and no amount of further lookahead will separate the two.
// However, alternative 3 will be able to continue and so we do not
// stop working on this state. In the previous example, we're concerned
// with states associated with the conflicting alternatives. Here alt
// 3 is not associated with the conflicting configs, but since we can continue
// looking for input reasonably, I don't declare the state done. We
// ignore a set of conflicting alts when we have an alternative
// that we still need to pursue.
//

ParserATNSimulator.prototype.getConflictingAltsOrUniqueAlt = function (configs) {
    var conflictingAlts = null;
    if (configs.uniqueAlt !== _ATN.ATN.INVALID_ALT_NUMBER) {
        conflictingAlts = new BitSet();
        conflictingAlts.add(configs.uniqueAlt);
    } else {
        conflictingAlts = configs.conflictingAlts;
    }
    return conflictingAlts;
};

ParserATNSimulator.prototype.getTokenName = function (t) {
    if (t === _Token.Token.EOF) {
        return "EOF";
    }
    if (this.parser !== null && this.parser.literalNames !== null) {
        if (t >= this.parser.literalNames.length && t >= this.parser.symbolicNames.length) {
            console.log("" + t + " ttype out of range: " + this.parser.literalNames);
            console.log("" + this.parser.getInputStream().getTokens());
        } else {
            var name = this.parser.literalNames[t] || this.parser.symbolicNames[t];
            return name + "<" + t + ">";
        }
    }
    return "" + t;
};

ParserATNSimulator.prototype.getLookaheadName = function (input) {
    return this.getTokenName(input.LA(1));
};

// Used for debugging in adaptivePredict around execATN but I cut
//  it out for clarity now that alg. works well. We can leave this
//  "dead" code for a bit.
//
ParserATNSimulator.prototype.dumpDeadEndConfigs = function (nvae) {
    console.log("dead end configs: ");
    var decs = nvae.getDeadEndConfigs();
    for (var i = 0; i < decs.length; i++) {
        var c = decs[i];
        var trans = "no edges";
        if (c.state.transitions.length > 0) {
            var t = c.state.transitions[0];
            if (t instanceof AtomTransition) {
                trans = "Atom " + this.getTokenName(t.label);
            } else if (t instanceof SetTransition) {
                var neg = t instanceof NotSetTransition;
                trans = (neg ? "~" : "") + "Set " + t.set;
            }
        }
        console.error(c.toString(this.parser, true) + ":" + trans);
    }
};

ParserATNSimulator.prototype.noViableAlt = function (input, outerContext, configs, startIndex) {
    return new _Errors.NoViableAltException(this.parser, input, input.get(startIndex), input.LT(1), configs, outerContext);
};

ParserATNSimulator.prototype.getUniqueAlt = function (configs) {
    var alt = _ATN.ATN.INVALID_ALT_NUMBER;
    for (var i = 0; i < configs.items.length; i++) {
        var c = configs.items[i];
        if (alt === _ATN.ATN.INVALID_ALT_NUMBER) {
            alt = c.alt; // found first alt
        } else if (c.alt !== alt) {
            return _ATN.ATN.INVALID_ALT_NUMBER;
        }
    }
    return alt;
};

//
// Add an edge to the DFA, if possible. This method calls
// {@link //addDFAState} to ensure the {@code to} state is present in the
// DFA. If {@code from} is {@code null}, or if {@code t} is outside the
// range of edges that can be represented in the DFA tables, this method
// returns without adding the edge to the DFA.
//
// <p>If {@code to} is {@code null}, this method returns {@code null}.
// Otherwise, this method returns the {@link DFAState} returned by calling
// {@link //addDFAState} for the {@code to} state.</p>
//
// @param dfa The DFA
// @param from The source state for the edge
// @param t The input symbol
// @param to The target state for the edge
//
// @return If {@code to} is {@code null}, this method returns {@code null};
// otherwise this method returns the result of calling {@link //addDFAState}
// on {@code to}
//
ParserATNSimulator.prototype.addDFAEdge = function (dfa, from_, t, to) {
    if (this.debug) {
        console.log("EDGE " + from_ + " -> " + to + " upon " + this.getTokenName(t));
    }
    if (to === null) {
        return null;
    }
    to = this.addDFAState(dfa, to); // used existing if possible not incoming
    if (from_ === null || t < -1 || t > this.atn.maxTokenType) {
        return to;
    }
    if (from_.edges === null) {
        from_.edges = [];
    }
    from_.edges[t + 1] = to; // connect

    if (this.debug) {
        var literalNames = this.parser === null ? null : this.parser.literalNames;
        var symbolicNames = this.parser === null ? null : this.parser.symbolicNames;
        console.log("DFA=\n" + dfa.toString(literalNames, symbolicNames));
    }
    return to;
};
//
// Add state {@code D} to the DFA if it is not already present, and return
// the actual instance stored in the DFA. If a state equivalent to {@code D}
// is already in the DFA, the existing state is returned. Otherwise this
// method returns {@code D} after adding it to the DFA.
//
// <p>If {@code D} is {@link //ERROR}, this method returns {@link //ERROR} and
// does not change the DFA.</p>
//
// @param dfa The dfa
// @param D The DFA state to add
// @return The state stored in the DFA. This will be either the existing
// state if {@code D} is already in the DFA, or {@code D} itself if the
// state was not already present.
//
ParserATNSimulator.prototype.addDFAState = function (dfa, D) {
    if (D == _ATNSimulator.ATNSimulator.ERROR) {
        return D;
    }
    var existing = dfa.states.get(D);
    if (existing !== null) {
        return existing;
    }
    D.stateNumber = dfa.states.length;
    if (!D.configs.readOnly) {
        D.configs.optimizeConfigs(this);
        D.configs.setReadonly(true);
    }
    dfa.states.add(D);
    if (this.debug) {
        console.log("adding new DFA state: " + D);
    }
    return D;
};

ParserATNSimulator.prototype.reportAttemptingFullContext = function (dfa, conflictingAlts, configs, startIndex, stopIndex) {
    if (this.debug || this.retry_debug) {
        var interval = new _IntervalSet.Interval(startIndex, stopIndex + 1);
        console.log("reportAttemptingFullContext decision=" + dfa.decision + ":" + configs + ", input=" + this.parser.getTokenStream().getText(interval));
    }
    if (this.parser !== null) {
        this.parser.getErrorListenerDispatch().reportAttemptingFullContext(this.parser, dfa, startIndex, stopIndex, conflictingAlts, configs);
    }
};

ParserATNSimulator.prototype.reportContextSensitivity = function (dfa, prediction, configs, startIndex, stopIndex) {
    if (this.debug || this.retry_debug) {
        var interval = new _IntervalSet.Interval(startIndex, stopIndex + 1);
        console.log("reportContextSensitivity decision=" + dfa.decision + ":" + configs + ", input=" + this.parser.getTokenStream().getText(interval));
    }
    if (this.parser !== null) {
        this.parser.getErrorListenerDispatch().reportContextSensitivity(this.parser, dfa, startIndex, stopIndex, prediction, configs);
    }
};

// If context sensitive parsing, we know it's ambiguity not conflict//
ParserATNSimulator.prototype.reportAmbiguity = function (dfa, D, startIndex, stopIndex, exact, ambigAlts, configs) {
    if (this.debug || this.retry_debug) {
        var interval = new _IntervalSet.Interval(startIndex, stopIndex + 1);
        console.log("reportAmbiguity " + ambigAlts + ":" + configs + ", input=" + this.parser.getTokenStream().getText(interval));
    }
    if (this.parser !== null) {
        this.parser.getErrorListenerDispatch().reportAmbiguity(this.parser, dfa, startIndex, stopIndex, exact, ambigAlts, configs);
    }
};

exports.ParserATNSimulator = ParserATNSimulator;
