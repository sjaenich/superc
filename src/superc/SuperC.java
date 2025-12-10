/*
 * xtc - The eXTensible Compiler
 * Copyright (C) 2009-2012 New York University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * version 2 as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301,
 * USA.
 */
package superc;

import java.lang.StringBuilder;

import java.io.File;
import java.io.Reader;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.StringReader;
import java.io.OutputStreamWriter;
import java.io.IOException;

import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Scanner;
import java.util.Map;
import java.util.IdentityHashMap;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;
import java.util.regex.*;

import superc.core.Lexer;
import superc.core.LexerCreator;
import superc.core.TokenCreator;
import superc.core.HeaderFileManager;
import superc.core.MacroTable;
import superc.core.MacroTable.Entry;  
import superc.core.MacroTable.Macro;
import superc.core.ExpressionParser;
import superc.core.ConditionEvaluator;
import superc.core.StopWatch;
import superc.core.StreamTimer;
import superc.core.Preprocessor;
import superc.core.TokenFilter;
import superc.core.ForkMergeParser;
import superc.core.SemanticValues;
import superc.core.DirectiveParser;

import superc.core.PresenceConditionManager;
import superc.core.PresenceConditionManager.PresenceCondition;

import superc.core.Clauses;

import superc.core.Syntax;
import superc.core.Syntax.Kind;
import superc.core.Syntax.LanguageTag;
import superc.core.Syntax.ConditionalTag;
import superc.core.Syntax.DirectiveTag;
import superc.core.Syntax.Layout;
import superc.core.Syntax.Language;
import superc.core.Syntax.Text;
import superc.core.Syntax.Directive;
import superc.core.Syntax.Conditional;
import superc.core.Syntax.Error;
import superc.core.Syntax.ErrorType;
import superc.core.Syntax.ConditionalBlock;
import superc.expression.ExpressionRats;

import superc.cparser.CParseTables;
import superc.cparser.CValues;
import superc.cparser.CActions;
import superc.cparser.CContext;
import superc.cparser.CLexerCreator;
import superc.cparser.CTokenCreator;

import superc.cparser.CContext.SymbolTable.STField;

import xtc.tree.Node;
import xtc.tree.GNode;
import xtc.tree.Location;

import xtc.Constants;

import xtc.util.Tool;
import xtc.util.Pair;

import xtc.lang.CParser;

import xtc.parser.Result;
import xtc.parser.ParseException;

import net.sf.javabdd.BDD;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

import org.json.simple.JSONObject;

/**
 * The SuperC configuration-preserving preprocessor and parsing.
 *
 * @author Paul Gazzillo
 * @version $Revision: 1.130 $
 */
public class SuperC extends Tool {
  /**
   * A node for tree-like representation of source code for conditional blocks
   * defined by conditional preprocessor directives.
   */
  private static class ConditionalBlock {
    /**
     * Line number where the conditional block starts in the source code. A
     * conditional block starts with a`#if` or `#elif` directive. Thus, the
     * corresponding line in the source code contains one of these directives.
     */
    private int startLine;
    
    /**
     * Line number where the conditional block ends in the source code. A conditional
     * block ends with a `#elif` (the beginning of the next conditional block)
     * or `#endif` directive. Thus, the corresponding line in the source code
     * contains one of these directives.
     */
    private int endLine;

    /**
     * List of sub conditional block groups contained. A conditional block
     * group is a conditional ladder (#if [#elif]* #endif), which might contain
     * one or more conditional blocks.
     */
    private List<List<ConditionalBlock>> subBlocks;

    /**
     * Complete presence condition for the conditional block.
     */
    private PresenceCondition pc;

    /**
     * Parent conditional block.
     */
    private ConditionalBlock parent;

    @Override
    public String toString() {
      // TODO: representation can possibly be optimized to have smaller output files as pcs can be shared
      return String.format( "{\"StartLine\": %s, \"EndLine\": %s, \"PC\": \"%s\", \"Sub\": %s}", startLine, endLine, pc.toSMT2().toString().replaceAll("\n", "\\\\n"), subBlocks);
    }

    /**
     * Read and return conditional block groups from preprocessor. Once returned,
     * the preprocessor will be at EOF token, or at END token of a conditional
     * block if it could not be matched with any START token.
     * @param preprocessor The preprocessor to iterate over.
     * @param pathToFileOfInterest The path to the file of interest.
     * @return A list of condition block groups each represented as a list
     * of conditional blocks.
     */
    public static List<List<ConditionalBlock>> getConditionalBlockGroups(Preprocessor preprocessor, String pathToFileOfInterest) {
      return readConditionalBlockGroups(preprocessor, pathToFileOfInterest);
    }

    /**
     * Constructor.
     */
    private ConditionalBlock() {
      this.subBlocks = new ArrayList<>();
    }

    /**
     * Check if the syntax is located within the file of interest.
     * @param syntax A syntax instance to check for.
     * @param pathToFileOfInterest The path to the file of interest.
     * @return true if syntax is within the file of interest, false otherwise.
     */
    private static boolean isInterestingFile(Syntax syntax, String pathToFileOfInterest) {
      return syntax != null && syntax.hasLocation() && syntax.getLocation() != null && pathToFileOfInterest.endsWith(syntax.getLocation().file);
    }

    /**
     * Read and return a condition block. The preprocessor must be at the beginning
     * token of the conditional block to read, i.e., START or NEXT. Once returned,
     * the preprocessor will be at the end token of the conditional block,
     * i.e., NEXT or END.
     * @param preprocessor The preprocessor to iterate over.
     * @param pathToFileOfInterest The path to the file of interest.
     * @return A condition block.
     */
    private static ConditionalBlock readConditionalBlock(Preprocessor preprocessor, String pathToFileOfInterest) {
      // Token/tag/file checks.
      assert preprocessor != null && preprocessor.token() != null
          && preprocessor.token().kind() == Kind.CONDITIONAL && preprocessor.token().toConditional() != null
          && (preprocessor.token().toConditional().tag() == Syntax.ConditionalTag.START 
              || preprocessor.token().toConditional().tag() == Syntax.ConditionalTag.NEXT);
      assert isInterestingFile(preprocessor.token(), pathToFileOfInterest);

      ConditionalBlock cb = new ConditionalBlock();
      PresenceCondition pc = preprocessor.token().toConditional().presenceCondition();
      cb.pc = pc;
      int startLine = preprocessor.token().getLocation().line;

      // Read any nested ConditionalBlockGroups inside, until the end of
      // the current block.
      cb.subBlocks = readConditionalBlockGroups(preprocessor, pathToFileOfInterest);

      // Assign parents
      for(List<ConditionalBlock> l : cb.subBlocks) {
        for(ConditionalBlock subBlock: l) {
          subBlock.parent = cb;
        }
      }
      // Verify it is the end token of the conditional block.    
      ConditionalTag currentTokenTag = preprocessor.token().toConditional().tag();
      assert currentTokenTag == Syntax.ConditionalTag.NEXT || currentTokenTag == Syntax.ConditionalTag.END;

      // Assign line range.
      int endLine = preprocessor.token().getLocation().line;
      cb.startLine = startLine;
      cb.endLine = endLine;

      // Return.
      return cb;
    }

    /**
     * Read and return a conditional block group. The preprocessor must be
     * at START conditional preprocessor token of the conditional block group
     * to read. Once returned, the preprocessor will be at the END token of
     * the conditional block group read.
     * 
     * @param preprocessor The preprocessor to iterate over.
     * @param pathToFileOfInterest The path to the file of interest.
     * @return A condition block group represented as a list of conditional
     * blocks. null if the condition block group is invalid, i.e., due to macro
     * expansion from a file different than pathToFileOfInterest.
     */
    private static List<ConditionalBlock> readConditionalBlockGroup(Preprocessor preprocessor, String pathToFileOfInterest) {
      // Token/tag/file checks.
      assert preprocessor != null && preprocessor.token() != null
          && preprocessor.token().kind() == Kind.CONDITIONAL && preprocessor.token().toConditional() != null
          && preprocessor.token().toConditional().tag() == Syntax.ConditionalTag.START;
      assert isInterestingFile(preprocessor.token(), pathToFileOfInterest);

      List<ConditionalBlock> cbGroup = new ArrayList<>();
      ConditionalTag currentTag = preprocessor.token().toConditional().tag();
      
      while (currentTag != Syntax.ConditionalTag.END) { // read until the end of the block group
        ConditionalBlock cb = readConditionalBlock(preprocessor, pathToFileOfInterest);
        cbGroup.add(cb);
        currentTag = preprocessor.token().toConditional().tag();
        assert currentTag == Syntax.ConditionalTag.NEXT || currentTag == Syntax.ConditionalTag.END;
      }
      assert currentTag == Syntax.ConditionalTag.END;

      // If the locations of the start and the end of the conditional block
      // group are the same, it is because macro expansion from some other
      // file was occurred, which is not a condition block group within the
      // file of interest.
      if (cbGroup.get(0).startLine == cbGroup.get(0).endLine ) {
        return null;
      }
      return cbGroup;
    }

    /**
     * Read and return conditional block groups from preprocessor. Once returned,
     * the preprocessor will be at EOF token, or at END token of a conditional
     * block if it could not be matched with any START token.
     * @param preprocessor The preprocessor to iterate over.
     * @param pathToFileOfInterest The path to the file of interest.
     * @return A list of condition block groups each represented as a list
     * of conditional blocks.
     */
    private static List<List<ConditionalBlock>> readConditionalBlockGroups(Preprocessor preprocessor, String pathToFileOfInterest) {  
      List<List<ConditionalBlock>> cbGroups = new ArrayList<>();
      preprocessor.next();

      while (preprocessor.token().kind() != Kind.EOF) {
        if (isInterestingFile(preprocessor.token(), pathToFileOfInterest) && preprocessor.token().kind() == Kind.CONDITIONAL) {
          ConditionalTag currentTag = preprocessor.token().toConditional().tag();
          if (currentTag == Syntax.ConditionalTag.NEXT || currentTag == Syntax.ConditionalTag.END) {
            // Dangling NEXT or END: end of this context, return.
            return cbGroups;
          } else if (currentTag == Syntax.ConditionalTag.START) {
            // Start a new conditional block group.
            List<ConditionalBlock> cbGroup = readConditionalBlockGroup(preprocessor, pathToFileOfInterest);
            if (cbGroup != null) { // null means the group was a conditional macro expansion from header -- not really a cb group in the sourcefile
              cbGroups.add(cbGroup);
            }
            assert preprocessor.token().toConditional().tag() == Syntax.ConditionalTag.END;
          } else {
            // Shouldn't be possible.
            assert false;
          }
        }
        preprocessor.next();        
      }
      assert preprocessor.token().kind() == Kind.EOF;
      return cbGroups;
    }
  }

  /** The user defined include paths */
  List<String> I;
  
  /** Additional paths for quoted header file names */
  List<String> iquote;
  
  /** Additional paths for system headers */
  List<String> sysdirs;
  
  /** Command-line macros and includes */
  StringReader commandline;

  /** Plug-in to create a new lexer for a given parser. */
  private final static LexerCreator lexerCreator = new CLexerCreator();

  /** Preprocessor support for token-creation. */
  private final static TokenCreator tokenCreator = new CTokenCreator();

  /** Simplify nested conditionals in preprocessor output. */
  private final static boolean SIMPLIFY_NESTED_CONDITIONALS = true;

  /** Create a new tool. */
  public SuperC() { /* Nothing to do. */ }

  /**
   * Return the name of this object.
   * 
   * @return The name of this object.
   */
  public String getName() {
    return "SuperC";
  }


  /**
   * Return a copy of the Constants used.
   * 
   * @return The copy of the Constants.
   */
  public String getCopy() {
    return "(C) 2009-2012 New York University\n"
      + "Portions Copyright (c) 1989, 1990 James A. Roskind";
  }


  public String getExplanation() {
    return
      "By default, SuperC performs all optimizations besides " +
      "platoffOrdering.  If one or more " +
      "individual optimizations are specified as command line flags, all " +
      "AND ICAN EDIT STUFFother optimizations are automatically disabled.";
        
  }

  public void init() {
    super.init();
    
    runtime.
      // Regular preprocessor arguments.
      word("I", "I", true,
           "Add a directory to the header file search path.").
      word("isystem", "isystem", true,
           "Add a system directory to the header file search path.").
      word("iquote", "iquote", true,
           "Add a quote directory to the header file search path.").
      bool("nostdinc", "nostdinc", false,
           "Don't use the standard include paths.").
      word("D", "D", true, "Define a macro.").
      word("U", "U", true, "Undefine a macro.  Occurs after all -D arguments "
           + "which is a departure from gnu cpp.").
      word("include", "include", true, "Include a header.").
      
      // Extra preprocessor arguments.
      bool("nobuiltins", "nobuiltins", false,
           "Disable gcc built-in macros.").
      bool("nocommandline", "nocommandline", false,
           "Do not process command-line defines (-D), undefines (-U), or " +
           "includes (-include).  Useful for testing the preprocessor.").
      word("mandatory", "mandatory", false,
           "Include the given header file even if nocommandline is on.").
      word("restrictConfigToPrefix", "restrictConfigToPrefix", false,
           "Assume non-config free macros are false when used like "
           + "configuration variables, but keep them free in the macro table").
      word("restrictFreeToPrefix", "restrictFreeToPrefix", false,
           "Restricts free macros to those that have the given prefix").
      bool("singleConfigSysheaders", "singleConfigSysheaders", false,
           "Disables configuration-awareness inside of system headers.").

      // SuperC component selection.
      bool("E", "E", false,
           "Just do configuration-preserving preprocessing.").
      bool("lexer", "lexer", false,
           "Just do lexing and print out the tokens.").
      bool("lexerNoPrint", "lexerNoPrint", false,
           "Lex but don't print.").
      bool("directiveParser", "directiveParser", false,
           "Just do lexing and directive parsing and print out the tokens.").
      bool("preprocessor", "preprocessor", false,
           "Preprocess but don't print.").
      bool("follow-set", "follow-set", false,
           "Compute the FOLLOW sets of each token in the preprocessed input.").
      bool("make-main", "make-main", false,
           "Create a main function to call main variants.").

      // // Desugarer component selection
      // bool("desugar", "desugarer", false,
      //      "Run the desugarer.").

      // Preprocessor optimizations.
      /*bool("Odedup", "optimizeDedup", false,
        "Turn off macro definition deduplication.  Not recommended " +
        "except for analysis.")*/

      // FMLR algorithm optimizations.
      bool("Onone", "doNotOptimize", false,
           "Turn off all optimizations, but still use the follow-set.").
      bool("Oshared", "optimizeSharedReductions", true,
           "Turn on the \"shared reductions\" optimization.").
      bool("Olazy", "optimizeLazyForking", true,
           "Turn on the \"lazy forking\" optimization.").
      bool("Oearly", "optimizeEarlyReduce", true,
           "Turn on the \"early reduce\" optimization.").

      // Platoff ordering has no effect with the other optimizations.
      bool("platoffOrdering", "platoffOrdering", false,
           "Turn on the Platoff ordering optimization.  Off by default.").

      // Deoptimize with early shifts.
      bool("earlyShift", "earlyShift", false,
           "Deoptimize FMLR by putting shifts first.  Incompatible with " +
           "early reduce.").

      // Other optimizations.
      bool("noFollowCaching", "noFollowCaching", false,
           "Turn off follow-set caching.  On by default.").

      // New error handling.
      bool("newErrorHandling", "newErrorHandling", false,
           "Use new error handling that puts errors in the AST.").

      // Naive FMLR.
      bool("naiveFMLR", "naiveFMLR", false,
           "Naive FMLR Turn off all optimizations and don't "
           + "use the follow-set.").

      // Subparser explosion kill switch.
      word("killswitch", "killswitch", false,
           "Stop parsing if subparser set reaches or exceeds the given size. "
           + "This protects against subparser exponential explosion.  An "
           + "error message will be reported.").

      // Type checking and analysis
      bool("checkers", "checkers", false,
           "Turn on semantic checkers.").
      word("featureModel", "featureModel", false,
           "Specify a feature model to use when finding satisfiable bugs.").
      word("modelAssumptions", "modelAssumptions", false,
           "Specify model assumptions to feed the sat solver,e.g., "
           + "unselectable config vars.").
      bool("symbolTable", "symbolTable", false,
           "Print the symbolTable.").
      bool("functionAnalysis", "functionAnalysis", false,
           "Print function definitions, calls, and unresolved calls.  Function "
           + "definitions conditions are already negated for easier bug-finding."). 
      bool("printErrorConditions", "printErrorConditions", false,
           "Print error directive presence conditions, negated for easier use.").
      word("extraConstraints", "extraConstraints", false,
           "Add extra constraints to add to the featureModel.  One per line in "
           + "CNF-style format, e.g., from printErrorConditions.").
      bool("keepErrors", "keepErrors", false,
           "Pass preprocessor error tokens to the parser.  Makes for more "
           + "specific presence conditions.").

      // Statistics, analyses, and timing.
      bool("preprocessorStatistics", "statisticsPreprocessor", false,
           "Dynamic analysis of the preprocessor.").
      bool("languageStatistics", "statisticsLanguage", false,
           "Dynamic analysis of the language usage.").
      bool("parserStatistics", "statisticsParser", false,
           "Parser statistics.").
      bool("configurationVariables", "configurationVariables", false,
           "Report a list of all configuration variables.  A configuration " +
           "variable is a macro used in a conditional expression before or " +
           "without being defined").
      bool("headerGuards", "headerGuards", false,
           "Report a list of all header guard macros.  Header guards are " +
           "found with gcc's idiom: #ifndef MACRO\\n#define MACRO\\n...\\n" +
           "#endif.").
      bool("size", "size", false,
           "Report the size, in bytes, of the compilation unit.  This is " +
           "the size of the main file plus the size of all headers " +
           "for every time each header is included.").
      bool("time", "time", false,
           "Running time in milliseconds broken down: " +
           "(1) lexer, (2) preprocessor and lexer, and " +
           "(3) parser, preprocessor and lexer.").
      bool("presenceConditions", "presenceConditions", false,
           "Show presence conditions for each static conditional.").
      word("headerChain", "headerChain", true,
           "Find, if any, the chain of includes to reach the given header.").
      bool("conditionConfigs", "conditionConfigs", false,
           "Show configs for each static conditional.").
      bool("conditionGranularity", "conditionGranularity", false,
           "Show configs for each static conditional.").

      // Validation
      bool("checkExpressionParser", "checkExpressionParser", false,
           "Check SuperC's expression parser against Rats!'").
      bool("checkAST", "checkAST", false,
           "Check SuperC's C AST against Rats!'").

      // Output and debugging
      bool("printAST", "printAST", false,
           "Print the parsed AST.").
      bool("printSource", "printSource", false,
           "Print the parsed AST in C source form.").
      bool("suppressConditions", "suppressConditions", false,
           "Do not print presence conditions to save space.").
      bool("configureAllYes", "configureAllYes", false,
           "Print all tokens of the all yes configuration of the AST.").
      bool("configureAllNo", "configureAllNo", false,
           "Print all tokens of the all no configuration of the AST.").
      word("configureExceptions", "configureExceptions", false,
           "Add exceptions to the all yes or no configuration.").
      word("configFile", "configFile", false,
           "Add exceptions to the all yes configuration via a linux .config file.").
      /*bool("showCPresenceCondition", "showCPresenceCondition", false,
        "Show scope changes and identifier bindings.").*/
      /*bool("traceIncludes", "traceInclude", false,
        "Show every header entrance and exit.").*/
      bool("hideErrors", "hideErrors", false,
           "Hide preprocessing and parsing errors in standard err.").
      bool("showAccepts", "showAccepts", false,
           "Emit ACCEPT messages when a subparser accepts input.").
      bool("showActions", "showActions", false,
           "Show all parsing actions.").
      bool("showFM", "showFM", false,
           "Show all forks and merges.").
      bool("showHeaders", "showHeaders", false,
           "Show header entry and exit.").
      bool("showLookaheads", "showLookaheads", false,
           "Show lookaheads on each parse loop (warning: very voluminous "
           + "output!)").
      bool("macroTable", "macroTable", false,
           "Show the macro symbol table.").
      word("sourcelinePC", "sourcelinePC", false,
            "Prints presence conditions as a list of conditional block groups "
            + "to the specified file.  Format: file[:line[:macro]]")
      ;
  }
  
  /**
   * Prepare for file processing.  Build header search paths.
   * Include command-line headers. Process command-line and built-in macros.
   */
  public void prepare() {
    // Configure optimizations options.
    boolean explicitOptimizations = runtime.hasPrefixValue("optimize");
    boolean doNotOptimize
      = runtime.hasValue("doNotOptimize")
      && runtime.test("doNotOptimize");
    boolean naiveFMLR
      = runtime.hasValue("naiveFMLR")
      && runtime.test("naiveFMLR");

    // Check optimization options.
    if (explicitOptimizations && doNotOptimize) { 
      runtime.error("no optimizations incompatible with explicitly specified " +
                    "optimizations");
    }
    
    if (naiveFMLR && (explicitOptimizations || doNotOptimize)) {
      runtime.error("naive FMLR is incompatible with all optimizations and "
                    + "with Onone because it does not use the follow set.");
    }

    // Check configure options
    if (runtime.hasValue("configureAllYes") && runtime.test("configureAllYes") &&
        runtime.hasValue("configureAllNo") && runtime.test("configureAllNo")) {
      runtime.error("pick either configureAllYes or configureAllNo, but not " +
                    "both");
    }

    // Now, fill in the defaults.
    if (explicitOptimizations || doNotOptimize || naiveFMLR) {
      runtime.initFlags("optimize", false);
    }

    // Set the command-line argument defaults.
    runtime.initDefaultValues();


    if (runtime.test("optimizeEarlyReduce") && runtime.test("earlyShift")) {
      runtime.error("Cannot have both early reduce and early shift.");
    }


    // Use the Java implementation of JavaBDD. Setting it here means
    // the user doesn't have to set it on the commandline.
    System.setProperty("bdd", "java");

    // Get preprocessor settings.
    iquote = new LinkedList<String>();
    I = new LinkedList<String>();
    sysdirs = new LinkedList<String>();

    // The following shows which command-line options add to ""
    // headers and which add to <> headers.  Additionally, only
    // -isystem are considered system headers.  System headers have a
    // special marker to cpp, but SuperC does not need to use this.

    // currentheaderdirectory iquote I    isystem standardsystem
    // ""                     ""     ""   ""     ""
    //                               <>   <>     <>
    //                                    marked system headers 
    if (!runtime.test("nostdinc")) {
      for (int i = 0; i < Builtins.sysdirs.length; i++) {
        sysdirs.add(Builtins.sysdirs[i]);
      }
    }
    
    for (Object o : runtime.getList("isystem")) {
      if (o instanceof String) {
        String s;
        
        s = (String) o;
        if (sysdirs.indexOf(s) < 0) {
          sysdirs.add(s);
        }
      }
    }

    for (Object o : runtime.getList("I")) {
      if (o instanceof String) {
        String s;

        s = (String) o;

        // Ignore I if already a system path.
        if (sysdirs.indexOf(s) < 0) {
          I.add(s);
        }
      }
    }
    
    for (Object o : runtime.getList("iquote")) {
      if (o instanceof String) {
        String s;
        
        s = (String) o;
        // cpp permits bracket and quote search chains to have
        // duplicate dirs.
        if (iquote.indexOf(s) < 0) {
          iquote.add(s);
        }
      }
    }

    // Make one large file for command-line/builtin stuff.
    StringBuilder commandlinesb;

    commandlinesb = new StringBuilder();
    
    if (! runtime.test("nobuiltins")) {
      commandlinesb.append(Builtins.builtin);
    }
    
    if (! runtime.test("nocommandline")) {
      for (Object o : runtime.getList("D")) {
        if (o instanceof String) {
          String s, name, definition;
          
          s = (String) o;
          
          // Truncate at first newline according to gcc spec.
          if (s.indexOf("\n") >= 0) {
            s = s.substring(0, s.indexOf("\n"));
          }
          if (s.indexOf("=") >= 0) {
            name = s.substring(0, s.indexOf("="));
            definition = s.substring(s.indexOf("=") + 1);
          }
          else {
            name = s;
            // The default for command-line defined guard macros.
            definition = "1";
          }
          commandlinesb.append("#define " + name + " " + definition + "\n");
        }
      }
      
      for (Object o : runtime.getList("U")) {
        if (o instanceof String) {
          String s, name, definition;
          
          s = (String) o;
          // Truncate at first newline according to gcc spec.
          if (s.indexOf("\n") >= 0) {
            s = s.substring(0, s.indexOf("\n"));
          }
          name = s;
          commandlinesb.append("#undef " + name + "\n");
        }
      }
      
      for (Object o : runtime.getList("include")) {
        if (o instanceof String) {
          String filename;
          
          filename = (String) o;
          commandlinesb.append("#include \"" + filename + "\"\n");
        }
      }
    }
    
    if (null != runtime.getString("mandatory")
        && runtime.getString("mandatory").length() > 0) {
      commandlinesb.append("#include \"" + runtime.getString("mandatory")
                           + "\"\n");
    }
    
    if (commandlinesb.length() > 0) {
      commandline = new StringReader(commandlinesb.toString());

    } else {
      commandline = null;
    }
  }

  public Node parse(Reader in, File file) throws IOException, ParseException {
    HeaderFileManager fileManager;
    MacroTable macroTable;
    PresenceConditionManager presenceConditionManager;
    ExpressionParser expressionParser;
    ConditionEvaluator conditionEvaluator;
    Iterator<Syntax> preprocessor;
    Node result = null;
    StopWatch parserTimer = null, preprocessorTimer = null, lexerTimer = null;

    if (runtime.test("time")) {
      parserTimer = new StopWatch();
      preprocessorTimer = new StopWatch();
      lexerTimer = new StopWatch();

      parserTimer.start();
    }

    if (runtime.test("lexer")
        || runtime.test("lexerNoPrint")
        || runtime.test("directiveParser")) {
      // Just do lexing and/or directive parsing, print the tokens and
      // quit if these options are selected.
      final Lexer clexer = lexerCreator.newLexer(in);
      clexer.setFileName(file.getName());

      Iterator<Syntax> stream = new Iterator<Syntax>() {
          Syntax syntax;
    
          public Syntax next() {
            try {
              syntax = clexer.yylex();
            } catch (IOException e) {
              e.printStackTrace();
              throw new RuntimeException();
            }
            return syntax;
          }
    
          public boolean hasNext() {
            return syntax.kind() != Kind.EOF;
          }

          public void remove() {
            throw new UnsupportedOperationException();
          }
        };

      if (runtime.test("directiveParser")) {
        stream = new DirectiveParser(stream, file.getName());
      }

      Syntax syntax = stream.next();

      while (syntax.kind() != Kind.EOF) {
        if (! runtime.test("lexerNoPrint")) {
          System.out.print(syntax.toString());
        }
        syntax = stream.next();
      }

      return null;
    }

    // Initialize the preprocessor with built-ins and command-line
    // macros and includes.
    macroTable = new MacroTable(tokenCreator);
    macroTable
      .getConfigurationVariables(runtime.test("configurationVariables"));
    macroTable.getHeaderGuards(runtime.test("headerGuards"));
    presenceConditionManager = new PresenceConditionManager();
    if (runtime.test("suppressConditions")) {
      presenceConditionManager.suppressConditions(true);
    }
    // if (runtime.test("checkExpressionParser")) {
    //   expressionParser = ExpressionParser.comparator(presenceConditionManager);
    // } else {
    //   // expressionParser = ExpressionParser.fromSuperC(presenceConditionManager);
      expressionParser = ExpressionParser.fromRats();
    // }
    conditionEvaluator = new ConditionEvaluator(expressionParser,
                                                presenceConditionManager,
                                                macroTable);
    if (null != runtime.getString("restrictFreeToPrefix")) {
      macroTable.restrictPrefix(runtime.getString("restrictFreeToPrefix"));
      conditionEvaluator.restrictPrefix(runtime.getString("restrictFreeToPrefix"));
    }

    if (null != runtime.getString("restrictConfigToPrefix")) {
      // let macros be free!  only restrict them when encountered in a
      // conditional
      conditionEvaluator.restrictPrefix(runtime.getString("restrictConfigToPrefix"));
    }

    if (null != commandline) {
      Syntax syntax;
      
      try {
        commandline.reset();
      }
      catch (Exception e) {
        e.printStackTrace();
      }

      fileManager = new HeaderFileManager(commandline,
                                          new File("<command-line>"),
                                          iquote, I, sysdirs,
                                          lexerCreator, tokenCreator,
                                          lexerTimer);
      fileManager.showHeaders(runtime.test("showHeaders"));
      fileManager.collectStatistics(runtime.test("statisticsPreprocessor"));
      fileManager.showErrors(! runtime.test("hideErrors"));
      fileManager.doTiming(runtime.test("time"));

      preprocessor = new Preprocessor(fileManager,
                                      macroTable,
                                      presenceConditionManager,
                                      conditionEvaluator,
                                      tokenCreator);
      ((Preprocessor) preprocessor)
        .collectStatistics(runtime.test("statisticsPreprocessor"));
      ((Preprocessor) preprocessor)
        .showErrors(! runtime.test("hideErrors"));
      ((Preprocessor) preprocessor)
        .singleConfigurationSysheaders(runtime.test("singleConfigSysheaders"));

      if (runtime.test("time")) {
        preprocessor = new StreamTimer<Syntax>(preprocessor, preprocessorTimer);
      }
      
      do {
        syntax = preprocessor.next();
      } while (syntax.kind() != Kind.EOF);

      commandline = null;
    }
    
    fileManager = new HeaderFileManager(in, file, iquote, I, sysdirs,
                                        lexerCreator, tokenCreator, lexerTimer,
                                        runtime.getString(xtc.util.Runtime.INPUT_ENCODING));
    fileManager.showHeaders(runtime.test("showHeaders"));
    fileManager.collectStatistics(runtime.test("statisticsPreprocessor"));
    fileManager.showErrors(! runtime.test("hideErrors"));
    fileManager.doTiming(runtime.test("time"));

    if (null != runtime.getList("headerChain")) {
      List<String> h = new LinkedList<String>();
      for (Object o : runtime.getList("headerChain")) {
        if (o instanceof String) {
          h.add((String) o);
        }
      }
      fileManager.showHeaderChains(h);
    }

    preprocessor = new Preprocessor(fileManager,
                                    macroTable,
                                    presenceConditionManager,
                                    conditionEvaluator,
                                    tokenCreator);
    ((Preprocessor) preprocessor)
      .collectStatistics(runtime.test("statisticsPreprocessor"));
    ((Preprocessor) preprocessor)
      .showErrors(! runtime.test("hideErrors"));
    ((Preprocessor) preprocessor)
      .singleConfigurationSysheaders(runtime.test("singleConfigSysheaders"));
    ((Preprocessor) preprocessor)
      .showPresenceConditions(runtime.test("presenceConditions"));
    ((Preprocessor) preprocessor)
      .showConditionConfigs(runtime.test("conditionConfigs"));

    List<PresenceCondition> printConstraints = ((Preprocessor) preprocessor)
      .printErrorConditions(runtime.test("printErrorConditions"));

    List<String> errorConstraints = new ArrayList<String>();
    ((Preprocessor) preprocessor)
      .saveErrorConstraints(errorConstraints);

    if (runtime.test("time")) {
      preprocessor = new StreamTimer<Syntax>(preprocessor, preprocessorTimer);
    }

    // Run SuperC.
    if (null != runtime.getString("sourcelinePC")) {
      String outputPath = runtime.getString("sourcelinePC");  


    // Parse additional parameters: file[:line[:macro]]  
      String[] parts = outputPath.split(":");  
      String actualOutputPath = parts[0];  
      Integer targetLine = parts.length > 1 ? Integer.parseInt(parts[1]) : null;  
      String targetMacro = parts.length > 2 ? parts[2] : null;  
    // Get presence condition tree  
      List<List<ConditionalBlock>> cbGroups =   
          ConditionalBlock.getConditionalBlockGroups((Preprocessor)preprocessor,   
                                                  file.getAbsolutePath());  
      
    // Count lines for root creation  
      Scanner sc = new Scanner(file);  
      int lineCount = 0;  
      while(sc.hasNextLine()) {  
          lineCount++;  
          sc.nextLine();  
      }   
      sc.close();  
      
    // Create the dummy root  
      ConditionalBlock root = new ConditionalBlock();  
      root.startLine = 0;  
      root.endLine = lineCount + 1;  
      root.subBlocks = cbGroups;  
      for(List<ConditionalBlock> cbGroup : cbGroups) {  
          for(ConditionalBlock cb : cbGroup) {  
              cb.parent = root;  
          }  
      }  
      root.pc = presenceConditionManager.newTrue();  
      root.parent = null;  
      Syntax syntax;
      do {  
        syntax = preprocessor.next();  
      } while (syntax.kind() != Kind.EOF);

     
    // If specific line and macro requested, get macro values  
      Map<String, Object> additionalInfo = new HashMap<>();  
      if (targetLine != null && targetMacro != null) {  
        // Get presence condition for the specific line  
        PresenceCondition linePC = getLinePresenceCondition(root, targetLine);  
        System.out.print(linePC);
        if (linePC != null) {  
            additionalInfo.put("linePresenceCondition", linePC.toSMT2().toString());  
            System.out.print("Oh yeah"+ macroTable.toString());
            // Get macro values from MacroTable  
            List<Entry> macroEntries = macroTable.get(targetMacro, presenceConditionManager);  
            List<Map<String, String>> macroValues = new ArrayList<>();  
              
            for (MacroTable.Entry entry : macroEntries) {  
                Map<String, String> valueInfo = new HashMap<>();  
                valueInfo.put("presenceCondition", entry.presenceCondition.toSMT2().toString());  
                  
                if (entry.macro.state == Macro.State.DEFINED) {  
                    if (entry.macro.isObject()) {  
                        // For object-like macros, get the replacement text  
                        StringBuilder replacement = new StringBuilder();  
                        for (Syntax token : entry.macro.definition) {  
                            replacement.append(token.getTokenText());  
                        }  
                        valueInfo.put("value", replacement.toString());  
                    } else {  
                        valueInfo.put("value", "function-like macro");  
                    }  
                } else {  
                    valueInfo.put("value", "undefined");  
                }  
                macroValues.add(valueInfo);  
            }  
            additionalInfo.put("macroValues", macroValues);  
        }  
      }  
      
    // Write output  
      System.err.println("Writing the presence conditions to \"" + actualOutputPath + "\".");  
      try {  
          FileWriter fr = new FileWriter(actualOutputPath);  
          
        // Write the conditional block tree  
          fr.write(root.toString());  
          
        // Write additional info if requested  
          if (!additionalInfo.isEmpty()) {  
              fr.write("\n\n=== Additional Information ===\n");  
              fr.write("Line " + targetLine + " Presence Condition: " +   
                     additionalInfo.get("linePresenceCondition") + "\n");  
              fr.write("Macro '" + targetMacro + "' Values:\n");  
              
              @SuppressWarnings("unchecked")  
              List<Map<String, String>> values =   
                  (List<Map<String, String>>) additionalInfo.get("macroValues");  
              for (Map<String, String> value : values) {  
                  fr.write("  Under condition " + value.get("presenceCondition") +   
                          ": " + value.get("value") + "\n");  
              }  
          }  
          
          fr.close();  
      } catch(Exception e) {  
          System.err.println("Exception while writing file: " + e);  
      }   
   } else if (runtime.test("follow-set")) {
      // Compute the follow-set of each token of the preprocessed
      // input.

      // Initialize a parser to use it's follow-set method and ordered
      // syntax class.
      CContext initialParsingContext = new CContext();
      initialParsingContext
        .collectStatistics(runtime.test("statisticsLanguage"));
      CActions actions = CActions.getInstance();
      actions.collectStatistics(runtime.test("statisticsLanguage"));
      
      ForkMergeParser parser
        = new ForkMergeParser(CParseTables.getInstance(),
                              CValues.getInstance(), actions,
                              initialParsingContext, preprocessor,
                              presenceConditionManager);
      initialParsingContext.free();

      // Initialize the the token stream.  Only pass ordinary tokens
      // and conditionals to the follow-set.
      preprocessor = new TokenFilter(preprocessor);

      ForkMergeParser.OrderedSyntax ordered
        = parser.new OrderedSyntax(preprocessor);

      // A stack of presence conditions.  Used to store the presence
      // conditions of nested conditionals.
      LinkedList<PresenceCondition> presenceConditions = new LinkedList<PresenceCondition>();

      presenceConditions.addLast(presenceConditionManager.newTrue());

      // Read each token from the token stream until EOF.
      while (true) {
        ordered = ordered.getNext();
        Syntax syntax = ordered.syntax;

        // The presence condition of the current token.  For
        // conditionals, it the presence condition of their parent
        // conditional branch (or true if they are at the top-level of
        // the source code.
        PresenceCondition presenceCondition;

        // Print the token.
        System.out.print("SYNTAX " + syntax.toString().trim());

        if (syntax.kind() == Kind.CONDITIONAL) {
          // Update the presence condition.
          Conditional conditional = syntax.toConditional();

          switch (conditional.tag()) {
          case START:
            presenceCondition = presenceConditions.getLast();
            presenceConditions.addLast(conditional.presenceCondition);
            break;

          case NEXT:
            presenceConditions.removeLast();
            presenceCondition = presenceConditions.getLast();
            presenceConditions.addLast(conditional.presenceCondition);
            break;

          case END:
            presenceConditions.removeLast();
            presenceCondition = presenceConditions.getLast();
            break;

          default:
            throw new UnsupportedOperationException();
          }
        } else {
          // Print the presence condition.
          presenceCondition = presenceConditions.getLast();
          System.out.print(" ::: " + presenceConditions.getLast().toString());
        }
        System.out.print("\n");

        // Print the follow set.
        if (syntax.kind() == Kind.LANGUAGE
            || syntax.kind() == Kind.EOF
            || syntax.kind() == Kind.CONDITIONAL
            && syntax.toConditional().tag() == ConditionalTag.START) {

          Map<Integer, ForkMergeParser.Lookahead> follow
            = parser.follow(ordered, presenceCondition.addRef());

          presenceCondition.delRef();

          System.out.print("FOLLOW [\n");
          for (Integer i : follow.keySet()) {
            ForkMergeParser.Lookahead l = follow.get(i);

            System.out.println("  " + l.token.syntax.toString() + " ::: "
                               + l.presenceCondition);
          }
          System.out.print("]\n\n");
        } else {
          System.out.print("\n");
        }

        if (syntax.kind() == Kind.EOF) break;
      }
    } else if (runtime.test("E") || runtime.test("preprocessor")) {
      // Run the SuperC preprocessor only.
      Syntax syntax;
      boolean seenNewline = true;
      int lineno = 0;
      syntax = preprocessor.next();

      LinkedList<PresenceCondition> parents
        = new LinkedList<PresenceCondition>();
      parents.push(presenceConditionManager.newTrue());
      while (syntax.kind() != Kind.EOF) {
        if (! runtime.test("statisticsPreprocessor")
            && ! runtime.test("preprocessor")) {
          if (syntax.kind() == Kind.LANGUAGE
              || syntax.kind() == Kind.LAYOUT
              || syntax.kind() == Kind.CONDITIONAL
              || (syntax.kind() == Kind.DIRECTIVE
                  && syntax.toDirective().tag() == DirectiveTag.LINEMARKER)
              || syntax.kind() == Kind.ERROR) {

            // Add a newline before a conditional directive or a
            // linemarker to mimic correct preprocessor directive
            // usage.
            if ((syntax.kind() == Kind.CONDITIONAL
                 || syntax.kind() == Kind.DIRECTIVE
                 || syntax.kind() == Kind.ERROR)
                && ! seenNewline) {
              System.out.print("\n");
              seenNewline = true;
            }

            if (syntax.testFlag(Preprocessor.PREV_WHITE)) {
              System.out.print(" ");
            } else {
              System.out.print(" ");
            }
//            System.out.print(syntax.getLocation());
            System.out.print(syntax);
            // Keep track of whether we have seen a newline already.
            if (syntax.kind() == Kind.LAYOUT && ((Layout) syntax).hasNewline()
                && syntax.getTokenText().endsWith("\n")) {
              seenNewline = true;
            } else if (syntax.kind() == Kind.CONDITIONAL
                       || syntax.kind() == Kind.DIRECTIVE) {
              System.out.print("\n");
              seenNewline = true;
            } else {
              seenNewline = false;
            }
          }
        }
        if (syntax.kind() == Kind.CONDITIONAL
            && ( syntax.toConditional().tag == ConditionalTag.START
                 || syntax.toConditional().tag == ConditionalTag.NEXT)) {
          syntax.toConditional().presenceCondition.delRef();
        }
        syntax = preprocessor.next();
      }
    // } else if (runtime.test("desugarer")) {
    } else {
      // Run the SuperC preprocessor and parser.
      ForkMergeParser parser;
      Object translationUnit;
      // Only pass ordinary tokens and conditionals to the parser.
      preprocessor = new TokenFilter(preprocessor, runtime.test("keepErrors"));

      // Create a new semantic values class for C.
      SemanticValues semanticValues;
      if (runtime.test("statisticsLanguage")) {
        // Modify the semantic values class to collect statistics on C
        // statements and declarations.
        final HashSet<String> trackedProductions = new HashSet<String>();

        // Statement and ExternalDeclaration are marked passthrough,
        // so we won't see them.  Instead look for their children.
        trackedProductions.add("Declaration");
        trackedProductions.add("LabeledStatement");    // Statements
        trackedProductions.add("CompoundStatement");
        trackedProductions.add("ExpressionStatement");
        trackedProductions.add("SelectionStatement");
        trackedProductions.add("IterationStatement");
        trackedProductions.add("JumpStatement");
        trackedProductions.add("AssemblyStatement");
        trackedProductions.add("FunctionDefinition");  // ExternalDeclarations
        trackedProductions.add("AssemblyDefinition");
        trackedProductions.add("EmptyDefinition");

        semanticValues = new CValues() {
            public Object getValue(int id, String name, Pair<Object> values) {
              Object value = super.getValue(id, name, values);

              if (trackedProductions.contains(name)) {
                // Get the location of the production.
                Location location = getProductionLocation(value);

                // Emit the marker.
                runtime.errConsole().pln(String.format("c_construct %s %s",
                                                       name, location)).flush();
              }

              return value;
            }
          };
      } else {
        semanticValues = CValues.getInstance();
      }

      CActions actions = CActions.getInstance();
      actions.collectStatistics(runtime.test("statisticsLanguage"));
      actions.enableCheckers(runtime.test("checkers"), errorConstraints);
      if (runtime.test("functionAnalysis")) {
        actions.enableFunctionAnalysis();
      }
      if (runtime.test("checkers") && runtime.getString("featureModel") != null) {
        // convert kconfig model to clauses for sat solver
        Clauses clauses = new Clauses();

        {
          BufferedReader br =
            new BufferedReader(new FileReader(runtime.getString("featureModel")));
          String line = br.readLine();
          while (null != line) {
            StringReader reader = new StringReader(line);
            ExpressionRats clauseParser
              = new ExpressionRats(reader, "CLAUSE", line.length());

            Result clauseTree;
            Node tree = null;
            try {
              clauseTree = clauseParser.pConstantExpression(0);
              // tree = (Node) clauseParser.value(clauseTree);
              if (! clauseTree.hasValue()) {
                tree = null;
                System.err.println(clauseParser.format(clauseTree.parseError()));
              } else {
                tree = clauseTree.semanticValue();
              }
              // System.err.println(tree);
            } catch (java.io.IOException e ) {
              e.printStackTrace();
              throw new RuntimeException("couldn't parse expression");
            }

            if (null != tree) {
              clauses.addClause(tree);
            }

            line = br.readLine();
          }
        }

        if (runtime.getString("extraConstraints") != null) {
          BufferedReader br =
            new BufferedReader(new FileReader(runtime.getString("extraConstraints")));
          String line = br.readLine();
          while (null != line) {
            if (line.startsWith("extra_constraint ")) {
              String[] s = line.split(" ");
              System.err.println(line + s);
              if (s.length > 1) {
                System.err.println("adding extra constraint " + s[1]);
                clauses.addClauses(s[1]);
              }
            }
            line = br.readLine();
          }
        }

        List<Integer> assumptions = new ArrayList<Integer>();
        if (runtime.getString("modelAssumptions") != null) {
          BufferedReader br =
            new BufferedReader(new FileReader(runtime.getString("modelAssumptions")));
          String line = br.readLine();

          // format is one var name per line, ! before it for assume false
          while (null != line) {
            int sign = 1;
            String varname = line;
            if (line.startsWith("!")) {
              sign = -1;
              varname = line.substring(1);
            }
            // if (clauses.varExists(varname)) {
              assumptions.add(sign * clauses.getVarNum(varname));
            // }
            line = br.readLine();
          }
        }
        int[] assumpints = new int[assumptions.size()];
        for (int i = 0; i < assumptions.size(); i++) {
          assumpints[i] = assumptions.get(i);
        }

        ISolver solver = SolverFactory.newDefault();
        solver.newVar(clauses.getNumVars());
        solver.setExpectedNumberOfClauses(clauses.size());

        for (List<Integer> clause : clauses) {
          int[] cint = new int[clause.size()];
          int i = 0;
          for (Integer val : clause) {
            cint[i++] = val;
          }
          try {
            solver.addClause(new VecInt(cint));
          } catch (ContradictionException e) {
            System.err.println("kconfig model is self-contradictory");
            System.exit(1);
          }
        }

        try {
          IProblem problem = new ModelIterator(solver);
          if (problem.isSatisfiable(new VecInt(assumpints))) {
            System.err.println("kconfig model is satisfiable");
          } else {
            System.err.println("kconfig model is not satisfiable");
            System.exit(1);
          }
        } catch (TimeoutException e) {
          e.printStackTrace();
          System.exit(1);
        }

        
        actions.addClauses(clauses, assumpints);
      }

      CContext initialParsingContext = new CContext();
      initialParsingContext.collectStatistics(runtime.test("statisticsLanguage"));

      parser = new ForkMergeParser(CParseTables.getInstance(), semanticValues,
                                   actions, initialParsingContext,
                                   preprocessor, presenceConditionManager);
      parser.saveLayoutTokens(runtime.test("printSource") 
                              || runtime.test("configureAllYes")
                              || runtime.test("configureAllNo")
                              || runtime.getString("configFile") != null);
      parser.setLazyForking(runtime.test("optimizeLazyForking"));
      parser.setSharedReductions(runtime.test("optimizeSharedReductions"));
      parser.setEarlyReduce(runtime.test("optimizeEarlyReduce"));
      parser.setLongestStack(runtime.test("platoffOrdering"));
      parser.setEarlyShift(runtime.test("earlyShift"));
      parser.setFollowSetCaching(! runtime.test("noFollowCaching"));
      parser.collectStatistics(runtime.test("statisticsParser"));
      parser.conditionGranularity(runtime.test("conditionGranularity"));
      parser.showActions(runtime.test("showActions"));
      parser.showErrors(! runtime.test("hideErrors"));
      parser.showAccepts(runtime.test("showAccepts"));
      parser.showFM(runtime.test("showFM"));
      parser.showLookaheads(runtime.test("showLookaheads"));
      if (runtime.test("newErrorHandling")) {
        parser.setNewErrorHandling(true);
        parser.setSaveErrorCond(true);
      }

      if (runtime.hasValue("killswitch")
          && null != runtime.getString("killswitch")) {
        try {
          int cutoff = Integer.parseInt(runtime.getString("killswitch"));

          if (cutoff <= 0) {
            throw new NumberFormatException("the -killswitch flag takes a "
                                            + "positive, non-zero integer");
          }
          parser.setKillSwitch(cutoff);
        } catch (NumberFormatException e) {
          throw new NumberFormatException("the -killswitch flag takes a "
                                          + "positive, non-zero integer");
        }
      }

      if (runtime.test("naiveFMLR")) {
        translationUnit = parser.parseNaively();
      } else {
        translationUnit = parser.parse();
      }

      if (null != translationUnit
          && ! ((Node) translationUnit).getName().equals("TranslationUnit")) {
        GNode tu = GNode.create("TranslationUnit");
        tu.add(translationUnit);
        translationUnit = tu;
      }

           initialParsingContext.free();

           if (runtime.test("printAST")) {
        runtime.console().format((Node) translationUnit).pln().flush();
      }

      if (runtime.test("printSource")) {
        OutputStreamWriter writer = new OutputStreamWriter(System.out);

        System.err.println("Print Source");

        LinkedList<PresenceCondition> parents
          = new LinkedList<PresenceCondition>();

        parents.push(presenceConditionManager.newTrue());

        printSource((Node) translationUnit,
                    presenceConditionManager.newTrue(),
                    parents, writer);

        parents.pop();
        assert(parents.size() == 0);
        
        writer.flush();
      }
      
      if (runtime.test("statisticsParser")) {
        IdentityHashMap<Object, Integer> seen
          = new IdentityHashMap<Object, Integer>();
        int count = dagNodeCount((Node) translationUnit, seen);
        runtime.errConsole().pln(String.format("dag_nodes %d", count));

        int shared = 0;
        for (Integer i : seen.values()) {
          if (i > 1) {
            shared++;
          }
        }
        runtime.errConsole().pln(String.format("dag_nodes_shared %d", shared));
        runtime.errConsole().flush();
      }

      result = (Node) translationUnit;
    }
    
    // Print optional statistics and debugging information.
    if (runtime.test("macroTable")) {
      System.err.println("Macro Table");
      System.err.println(macroTable);
    }

    if (runtime.test("configurationVariables")) {
      for (String name : macroTable.configurationVariables) {
        if (! macroTable.headerGuards.contains(name))  {
          System.err.println("config_var " + name);
        }
      }
    }

    if (runtime.test("headerGuards")) {
      for (String name : macroTable.headerGuards) {
        System.err.println("header_guard " + name);
      }
    }

    if (runtime.test("time")) {
      parserTimer.stop();
      System.err.println(String.format("performance_breakdown %s %f %f %f",
                                       file.toString(),
                                       parserTimer.getTotalSeconds(),
                                       preprocessorTimer.getTotalSeconds(),
                                       lexerTimer.getTotalSeconds()));
    }

    if (runtime.test("size")) {
      System.err.println("size " + fileManager.getSize());
    }

    return result;
  }
  
  /**
   * Get location of a production given its value.
   *
   * @param value The value of the production.
   * @return The location.
   */
  static Location getProductionLocation(Object value) {
    if (value instanceof Node) {
      for (Object o : (Node) value) {
        Location location = getProductionLocation(o);

        if (null != location) {
          return location;
        }
      }

      return ((Node) value).getLocation();
    } else {
      return null;
    }
  }
  
 
  private PresenceCondition getLinePresenceCondition(ConditionalBlock root, int lineNumber) {  
      // Check if the line is within this block  
      System.out.print("This is " +  lineNumber + " Root " + root.startLine + " " + root.endLine);
          // Base case: if this is a leaf node (no sub-blocks), return its PC  
    if (root.subBlocks.isEmpty()) {  
        if (lineNumber >= root.startLine && lineNumber < root.endLine) {  
            return root.pc;  
        }  
        return null;  
    }  
      
    // Check if line is within any sub-block  
    for (List<ConditionalBlock> group : root.subBlocks) {  
        for (ConditionalBlock block : group) {  
            // Check if line is in this sub-block's range OR  
            // if it's between this block and the next one  
            PresenceCondition subPC = getLinePresenceCondition(block, lineNumber);  
            if (subPC != null) {  
                return subPC;  
            }  
        }  
    }  
      
    // If not in any sub-block but in this block's range,   
    // it means this line is regular code within this conditional context  
    if (lineNumber >= root.startLine && lineNumber < root.endLine) {  
        return root.pc;  
    }  
      
    return null;  
}

  /**
   * Print an AST (or a subtree of it) in C source form.
   *
   * @param n An AST or a subtree.
   * @param presenceCondition The current nested presence condition.
   * @param writer The writer.
   * @throws IOException Because it writes to output. 
   */
  private static void printSource(Node n, PresenceCondition presenceCondition,
                                  LinkedList<PresenceCondition> parents,
                                  OutputStreamWriter writer)
    throws IOException {
    if (n.isToken()) {
      writer.write(n.getTokenText());
      writer.write(" ");

    } else if (n instanceof Node) {

      if (n instanceof GNode
          && ((GNode) n).hasName(ForkMergeParser.CHOICE_NODE_NAME)) {

        boolean seenIf = false;
        PresenceCondition branchCondition = null;

        for (Object bo : n) {
          if (bo instanceof PresenceCondition) {
            branchCondition = (PresenceCondition) bo;

            if (! seenIf) {
              writer.write("\n#if ");
              seenIf = true;
            } else {
              // writer.write("\n#elif ");
              writer.write("\n#endif ");
              writer.write("\n#if ");
              parents.pop();
            }

            if (branchCondition.equals(parents.peek())) {
              writer.write("1");
            } else {
              writer.write(branchCondition.toString());
              // branchCondition.print(writer);
            }
            parents.push(branchCondition);
            
            writer.write("\n");
          } else if (bo instanceof Node) {
            printSource((Node) bo, branchCondition, parents, writer);
          }
        }
        writer.write("\n#endif\n");
        parents.pop();

      } else {
        for (Object o : n) {
          printSource((Node) o, presenceCondition, parents, writer);
        }
      }

    } else {
      throw new UnsupportedOperationException("unexpected type");
    } 
  }

  /**
   * Print one configuration of an AST (or a subtree of it) as C
   * source code.
   *
   * @param n An AST or a subtree.
   * @param configuration A BDD containing the configuration settings.
   * @param writer The writer.
   * @throws IOException Because it writes to output. 
   */
  private static void configureAST(Node n,
                                   BDD configuration,
                                   Map<String,String> nonbooleans,
                                   OutputStreamWriter writer)
    throws IOException {
    if (n.isToken()) {
      if (nonbooleans.containsKey(n.getTokenText())) {
        writer.write(nonbooleans.get(n.getTokenText()));
      } else {
        writer.write(n.getTokenText());
      }
      writer.write(" ");

    } else if (n instanceof Node) {

      if (n instanceof GNode
          && ((GNode) n).hasName(ForkMergeParser.CHOICE_NODE_NAME)) {

        // Pick the first choice that satistifies the configuration

        boolean printNextNode = false;
        PresenceCondition branchCondition = null;

        for (Object bo : n) {
          if (bo instanceof PresenceCondition) {
            BDD restricted;
            boolean satisfies;

            branchCondition = (PresenceCondition) bo;

            // restricted = branchCondition.getBDD().restrict(configuration.id());
            // printNextNode = !restricted.isZero();
            // restricted.free();
            printNextNode = true;
          } else if (bo instanceof Node) {
            if (printNextNode) {
              configureAST((Node) bo, configuration, nonbooleans, writer);
            }
          }
        }
        writer.write("\n");
      } else {
        for (Object o : n) {
          configureAST((Node) o, configuration, nonbooleans, writer);
        }
      }

    } else {
      throw new UnsupportedOperationException("unexpected type");
    } 
  }

  /**
   * Count the number of AST nodes.
   *
   * @param n An AST or a subtree.
   */
  private static int astNodeCount(Node n) {
    if (n.isToken()) {
      return 1;

    } else if (n instanceof Node) {
      int count = 0;

      for (Object bo : n) {
        if (bo instanceof Node) {
          count += astNodeCount((Node) bo);
        }
      }

      return count;

    } else {
      throw new UnsupportedOperationException("unexpected type");
    } 
  }
  
  /**
   * Count the number of DAG nodes.
   *
   * @param n A DAG or a subtree.
   * @param seen A hash map to store the seen nodes.
   */
  private static int dagNodeCount(Node n,
                                  IdentityHashMap<Object, Integer> seen) {
    if (seen.containsKey(n)) {
      seen.put(n, seen.get(n) + 1);
      return 0;
    }

    seen.put(n, 1);

    if (n.isToken()) {
      return 1;

    } else if (n instanceof Node) {
      int count = 0;

      for (Object bo : n) {
        if (bo instanceof Node) {
          count += dagNodeCount((Node) bo, seen);
        }
      }

      return count;

    } else {
      throw new UnsupportedOperationException("unexpected type");
    } 
  }

  /**
   * Write the JSONObject instance to a file.
   */
  private void writeJson(JSONObject jsonObj, String filePath) {
    try {
      FileWriter fr = new FileWriter(filePath);
      jsonObj.writeJSONString(fr);
      fr.close();
    } catch(Exception e) {
      // TODO: properly handle this
      System.err.println("Exception while writing file: " + e);
    }
  }

  /**
   * Preprocess the given CPP CST.
   * 
   * @param node The CPP CST
   * @return The preprocessed CPP CST
   */
  public Node preprocess(Node node) {
    return null;
  }

  /**
   * Run the tool with the specified command line arguments.
   *
   * @param args The command line arguments.
   */
  public static void main(String[] args) {
    new SuperC().run(args);
  }
}
