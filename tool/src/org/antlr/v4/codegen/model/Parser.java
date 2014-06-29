/*
 * [The "BSD license"]
 *  Copyright (c) 2012 Terence Parr
 *  Copyright (c) 2012 Sam Harwell
 *  All rights reserved.
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *  1. Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *  2. Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *  3. The name of the author may not be used to endorse or promote products
 *     derived from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 *  IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 *  OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 *  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 *  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 *  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 *  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package org.antlr.v4.codegen.model;

import org.antlr.v4.codegen.CodeGenerator;
import org.antlr.v4.codegen.OutputModelFactory;
import org.antlr.v4.codegen.model.chunk.ActionChunk;
import org.antlr.v4.codegen.model.chunk.ActionText;
import org.antlr.v4.tool.Grammar;
import org.antlr.v4.tool.Rule;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Parser extends OutputModelObject {
	public String name;
	public String grammarFileName;
	public String grammarName;
	@ModelElement public ActionChunk superClass;
	public Map<String,Integer> tokens;
	public String[] tokenNames;
	public Set<String> ruleNames;
	public Collection<Rule> rules;
	public ParserFile file;

	@ModelElement public List<RuleFunction> funcs = new ArrayList<RuleFunction>();
	@ModelElement public SerializedATN atn;
	@ModelElement public LinkedHashMap<Rule, RuleSempredFunction> sempredFuncs =
		new LinkedHashMap<Rule, RuleSempredFunction>();

	public Parser(OutputModelFactory factory, ParserFile file) {
		this.factory = factory;
		this.file = file; // who contains us?
		Grammar g = factory.getGrammar();
		grammarFileName = new File(g.fileName).getName();
		grammarName = g.name;
		name = g.getRecognizerName();
		tokens = new LinkedHashMap<String,Integer>();
		for (String t : g.tokenNameToTypeMap.keySet()) {
			Integer ttype = g.tokenNameToTypeMap.get(t);
			if ( ttype>0 ) tokens.put(t, ttype);
		}
		tokenNames = g.getTokenDisplayNames();
		for (int i = 0; i < tokenNames.length; i++) {
			if ( tokenNames[i]==null ) continue;
			if ( tokenNames[i].charAt(0)=='\'' ) {
				boolean addQuotes = false;
				tokenNames[i] =
					factory.getTarget().getTargetStringLiteralFromANTLRStringLiteral(factory.getGenerator(),
																			tokenNames[i],
																			addQuotes);
				tokenNames[i] = "\"'"+tokenNames[i]+"'\"";
			}
			else {
				tokenNames[i] = factory.getTarget().getTargetStringLiteralFromString(tokenNames[i], true);
			}
		}
		ruleNames = g.rules.keySet();
		rules = g.rules.values();
		atn = new SerializedATN(factory, g.atn);
		if (g.getOptionString("superClass") != null) {
			superClass = new ActionText(null, g.getOptionString("superClass"));
		}
	}
}
