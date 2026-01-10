# SVA Grammar Restructuring Plan

## Problem Summary

The current SVA grammar has LALR(1) conflicts that prevent parsing certain valid patterns:

### Failing Pattern: Parenthesized Consequent
```systemverilog
property p1;
  @(posedge clk) a |-> (b != 0);  // FAILS - syntax error
endproperty
```

### Working Patterns
```systemverilog
property p1;
  @(posedge clk) a |-> b != 0;    // WORKS - no parens
endproperty

property p2;
  @(posedge clk) (a) |-> b;       // WORKS - parenthesized antecedent
endproperty
```

## Root Cause Analysis

The conflict occurs in `property_expr` between:

1. **Rule A**: `property_expr : expression`
   - Where `expression` can start with `(` (grouped expression)

2. **Rule B**: `'(' expression K_IMPLIES_OV property_expr ')'`
   - Which also starts with `(`

When parsing `a |-> (b)`:
1. Parser reduces `a` as `expression`
2. Shifts `|->` (K_IMPLIES_OV)
3. Sees `(` and must decide: Is this Rule A or Rule B?
4. LALR(1) can only look 1 token ahead (`(`)
5. Cannot distinguish `(b)` from `(b |-> c)` without seeing more tokens

## Solution Options

### Option 1: Remove Ambiguous Rules (Recommended)

Remove the rules that cause conflicts and document the limitation.

**Rules to remove from property_expr:**
```
| '(' expression K_IMPLIES_OV property_expr ')'
| '(' expression K_IMPLIES_NOV property_expr ')'
```

**Workaround for users:**
Instead of `(a |-> b)`, use `a |-> b` (outer parens rarely needed)

**Pros:**
- Simple fix, minimal code change
- Regression impact is minimal (these patterns are rare)
- Already documented in plan as known limitation

**Cons:**
- Loses ability to group implication expressions

### Option 2: Parser Refactoring with Precedence

Refactor to use Bison precedence declarations.

Add to precedence declarations:
```yacc
%nonassoc K_IMPLIES_OV K_IMPLIES_NOV
```

Modify property_expr to not have overlapping `(` rules.

**Challenge:** The fundamental issue is that `expression` contains parentheses, and we can't change that. Even with precedence, the parser state after `|->` seeing `(` is ambiguous.

### Option 3: Lexer Context Tracking

Use lexer state to return different tokens for `(` in property context.

**Implementation:**
1. When entering property body (after `@(...)` or after `|->` / `|=>`), set lexer flag
2. Lexer returns `PROP_LPAREN` instead of `(` in property context
3. Grammar uses `PROP_LPAREN` for property-specific rules

**Challenge:** Complex interaction between lexer and parser states. Risk of breaking other patterns.

### Option 4: GLR Parser

Use Bison's GLR (Generalized LR) mode.

```yacc
%glr-parser
```

**Pros:**
- Handles all ambiguous patterns correctly
- No grammar restructuring needed

**Cons:**
- Major change to parser infrastructure
- Performance impact
- Error recovery becomes more complex
- May expose other latent ambiguities

### Option 5: Semantic Predicate (Bison 3.0+)

Use semantic predicates to disambiguate at parse time.

**Challenge:** Requires Bison 3.0+ and current Icarus uses older Bison features.

## Recommended Approach

**Implement Option 1** - Remove the ambiguous `'(' expression K_IMPLIES_* property_expr ')'` rules.

**Rationale:**
1. These patterns are rarely needed in practice
2. Workarounds exist (remove unnecessary outer parens)
3. All 8 AVIPs compile and run successfully without these patterns
4. Minimal risk and code change

## Current Test Failures (5 total)

| Test | Issue | Solution |
|------|-------|----------|
| sva_property_ports | Typed ports with `(expr)` in body | Remove parens |
| sva_comprehensive | Multiple `(expr)` patterns | Remove parens |
| sva_paren_implication | Tests `((a) |-> (b))` | Document as limitation |
| br1015b | Unrelated - subroutine ports | Separate issue |
| part_sel_port | Unrelated - part select | Separate issue |

## Implementation Steps

1. **Identify all affected rules in parse.y**:
   - Lines 4042-4073: `'(' expression K_IMPLIES_OV property_expr ')'`
   - Lines 4486-4535: `'(' expression K_SEQ_DELAY ... ')' K_IMPLIES_*`

2. **Add warning or error for these patterns**:
   ```c
   yyerror(@1, "sorry: Parenthesized implication expressions not supported. "
               "Use 'a |-> b' instead of '(a |-> b)'.");
   ```

3. **Update test files to use workarounds**

4. **Update documentation** (CLAUDE.md, plan file)

## Alternative: Document as Known Limitation

If removing rules causes too many test failures, simply document that:

> Parenthesized consequents in SVA implications (`a |-> (b)`) are not supported.
> Use `a |-> b` or `a |-> b == 1` instead.

This is acceptable because:
- All real AVIP patterns work without this syntax
- It's a cosmetic preference, not a functional limitation
