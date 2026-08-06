use crate::parser::syntax_kind::SyntaxKind;
use crate::parser::grammar::common::parse_optional_settings_clause;
use crate::parser::grammar::select::{
    at_recoverable_clause_start, at_select_statement, parse_select_statement,
};
use crate::parser::grammar::types::parse_column_type;
use crate::parser::interval_unit::IntervalUnit;
use crate::parser::keyword::Keyword;
use crate::parser::marker::CompletedMarker;
use crate::parser::parser::Parser;

/// Binding power for prefix unary minus, above all binary operators.
const UNARY_PREFIX_BP: u8 = 7;

/// Binding power levels for binary operators (higher = tighter).
///
/// Modeled after ClickHouse's operator precedence:
/// https://clickhouse.com/docs/en/sql-reference/operators
#[derive(Clone, Copy)]
enum BinOp {
    // Logical (lowest)
    Or,
    And,
    // Comparison
    Equals,
    NotEquals,
    Less,
    Greater,
    LessOrEquals,
    GreaterOrEquals,
    // Arithmetic
    Plus,
    Minus,
    Asterisk,
    Slash,
    Percent,
    // String concatenation
    Concatenation,
}

impl BinOp {
    /// Try to read a binary operator from the parser's current position.
    /// Handles both token operators (+, -, etc.) and keyword operators (AND, OR).
    fn from_parser(p: &mut Parser) -> Option<BinOp> {
        if p.at_keyword(Keyword::And) {
            return Some(BinOp::And);
        }
        if p.at_keyword(Keyword::Or) {
            return Some(BinOp::Or);
        }
        match p.nth(0) {
            SyntaxKind::Plus => Some(BinOp::Plus),
            SyntaxKind::Minus => Some(BinOp::Minus),
            SyntaxKind::Star => Some(BinOp::Asterisk),
            SyntaxKind::Slash => Some(BinOp::Slash),
            SyntaxKind::Percent => Some(BinOp::Percent),
            SyntaxKind::Equals => Some(BinOp::Equals),
            SyntaxKind::NotEquals => Some(BinOp::NotEquals),
            SyntaxKind::Less => Some(BinOp::Less),
            SyntaxKind::Greater => Some(BinOp::Greater),
            SyntaxKind::LessOrEquals => Some(BinOp::LessOrEquals),
            SyntaxKind::GreaterOrEquals => Some(BinOp::GreaterOrEquals),
            SyntaxKind::Concatenation => Some(BinOp::Concatenation),
            _ => None,
        }
    }

    fn binding_power(self) -> u8 {
        match self {
            BinOp::Or => 1,
            BinOp::And => 2,
            BinOp::Equals | BinOp::NotEquals => 3,
            BinOp::Less | BinOp::Greater | BinOp::LessOrEquals | BinOp::GreaterOrEquals => 4,
            BinOp::Plus | BinOp::Minus | BinOp::Concatenation => 5,
            BinOp::Asterisk | BinOp::Slash | BinOp::Percent => 6,
        }
    }
}

pub fn parse_expression(p: &mut Parser) {
    parse_expression_rec(p, 0);
}

/// Consume an optional `AS alias` that appears inside parenthesized
/// expressions (ClickHouse expression-level aliases).
fn parse_expression_alias(p: &mut Parser) {
    if p.at_keyword(Keyword::As)
        && (p.nth(1) == SyntaxKind::BareWord || p.nth(1) == SyntaxKind::QuotedIdentifier)
    {
        let am = p.start();
        p.eat_keyword(Keyword::As);
        // Consume the alias identifier (skip trivia handled by eat/at)
        if !p.eat(SyntaxKind::BareWord) {
            p.eat(SyntaxKind::QuotedIdentifier);
        }
        p.complete(am, SyntaxKind::ColumnAlias);
    }
}

fn parse_expression_rec(p: &mut Parser, min_bp: u8) {
    // Every expression recursion funnels through here, so bound the nesting
    // depth at this one choke point. Deeply nested expressions (e.g. thousands
    // of parentheses) would otherwise overflow the stack — and on WASM a stack
    // overflow corrupts the whole module instance, poisoning every later parse.
    // Past the limit, emit an error and stop descending; the error-tolerant
    // parse degrades gracefully instead of trapping. Long operator chains are
    // built iteratively (no recursion), so only true nesting is bounded.
    if p.enter_depth() {
        p.advance_with_error("Maximum expression nesting depth exceeded");
        p.leave_depth();
        return;
    }
    parse_expression_rec_inner(p, min_bp);
    p.leave_depth();
}

fn parse_expression_rec_inner(p: &mut Parser, min_bp: u8) {
    // Handle prefix NOT: binding power 3 (between AND=2 and comparisons=3..4)
    // NOT binds tighter than AND/OR but at the same level as comparisons
    if p.at_keyword(Keyword::Not) {
        let m = p.start();
        p.advance(); // consume NOT
        parse_expression_rec(p, 3);
        let lhs = p.complete(m, SyntaxKind::UnaryExpression);
        // Continue with binary operators after the NOT expression
        parse_expression_postfix(p, lhs, min_bp);
        return;
    }

    // Handle prefix unary minus: highest precedence (7)
    if p.at(SyntaxKind::Minus) {
        let m = p.start();
        p.advance(); // consume -
        parse_expression_rec(p, UNARY_PREFIX_BP);
        let lhs = p.complete(m, SyntaxKind::UnaryExpression);
        parse_expression_postfix(p, lhs, min_bp);
        return;
    }

    let Some(mut lhs) = expr_delimited(p) else {
        p.advance_with_error("Expected expression");
        return;
    };

    // Postfix operators that chain: function calls `f(x)` and array access `a[k]`
    loop {
        if p.at(SyntaxKind::OpeningRoundBracket) {
            // The LHS is a function name, not a column reference.
            // Change ColumnReference → Identifier so the tree is semantically accurate.
            if p.kind_of(lhs) == SyntaxKind::ColumnReference {
                p.change_kind(lhs, SyntaxKind::Identifier);
            }
            let m = p.precede(lhs);
            arg_list(p);
            // Parametric functions like quantile(0.5)(x) have two argument
            // lists.  Keep consuming `(...)` groups as siblings inside the
            // same FunctionCall node instead of nesting.
            while p.at(SyntaxKind::OpeningRoundBracket) {
                arg_list(p);
            }
            lhs = p.complete(m, SyntaxKind::FunctionCall);
            // IGNORE NULLS / RESPECT NULLS — aggregate function modifiers
            if p.at_keyword(Keyword::Ignore) || p.at_keyword(Keyword::Respect) {
                // Only treat as modifier if followed by NULLS
                if p.nth_keyword(1, Keyword::Nulls) {
                    let m = p.precede(lhs);
                    p.advance(); // consume IGNORE or RESPECT
                    // `advance` steps over one raw token, whitespace included,
                    // so NULLS has to be consumed through a trivia-skipping
                    // helper rather than a second bare advance.
                    p.expect_keyword(Keyword::Nulls);
                    lhs = p.complete(m, SyntaxKind::NullsModifier);
                }
            }
            // FILTER(WHERE expr) — SQL standard aggregate filter clause
            if p.at_keyword(Keyword::Filter) && p.at_followed_by_paren() {
                let m = p.precede(lhs);
                p.advance(); // consume FILTER
                p.expect(SyntaxKind::OpeningRoundBracket);
                p.expect_keyword(Keyword::Where);
                parse_expression(p);
                p.expect(SyntaxKind::ClosingRoundBracket);
                lhs = p.complete(m, SyntaxKind::FilterClause);
            }
            // Window function: func(...) OVER (...)  or  func(...) OVER name
            if p.at_keyword(Keyword::Over) {
                let m = p.precede(lhs);
                p.advance(); // consume OVER
                if p.at(SyntaxKind::OpeningRoundBracket) {
                    parse_window_spec(p);
                } else if p.at_identifier() {
                    // OVER window_name
                    p.advance();
                } else {
                    p.recover_with_error("Expected window specification or name after OVER");
                }
                lhs = p.complete(m, SyntaxKind::WindowExpression);
            }
        } else if p.at(SyntaxKind::OpeningSquareBracket) {
            let m = p.precede(lhs);
            p.advance(); // consume [
            // Allow empty brackets: json.path[]
            if !p.at(SyntaxKind::ClosingSquareBracket) {
                parse_expression(p);
            }
            p.expect(SyntaxKind::ClosingSquareBracket);
            lhs = p.complete(m, SyntaxKind::ArrayAccessExpression);
        } else if p.at(SyntaxKind::DoubleColon) {
            // Cast: expr::Type
            let m = p.precede(lhs);
            p.advance(); // consume ::
            parse_column_type(p);
            lhs = p.complete(m, SyntaxKind::CastExpression);
        } else if p.at(SyntaxKind::Dot) {
            // Dot access (tuple element / field access).  The ColumnReference
            // loop in expr_delimited already consumed contiguous identifier
            // chains, so any dot we see here is either:
            //   - after a non-identifier expression: func(x).1, (t).name
            //   - a numeric index after an identifier chain: a.b.1
            //   - qualified asterisk: t1.*
            //   - JSON typed path access: json.path.:Type
            if p.nth(1) == SyntaxKind::Colon {
                // JSON typed path access: expr.:Type
                let m = p.precede(lhs);
                p.advance(); // consume .
                p.advance(); // consume :
                parse_column_type(p);
                lhs = p.complete(m, SyntaxKind::TypedJsonAccessExpression);
            } else {
                let m = p.precede(lhs);
                p.advance(); // consume .
                if p.at(SyntaxKind::Star) {
                    // Qualified asterisk: t1.*
                    p.advance(); // consume *
                    lhs = p.complete(m, SyntaxKind::QualifiedAsterisk);
                } else if !p.eat(SyntaxKind::BareWord)
                    && !p.eat(SyntaxKind::QuotedIdentifier)
                    && !p.eat(SyntaxKind::Number)
                {
                    p.advance_with_error("expected field name or tuple index after '.'");
                    lhs = p.complete(m, SyntaxKind::DotAccessExpression);
                } else {
                    lhs = p.complete(m, SyntaxKind::DotAccessExpression);
                }
            }
        } else if (p.kind_of(lhs) == SyntaxKind::Asterisk
            || p.kind_of(lhs) == SyntaxKind::QualifiedAsterisk
            || p.kind_of(lhs) == SyntaxKind::ColumnTransformer)
            && (p.at_keyword(Keyword::Apply)
                || p.at_keyword(Keyword::Except)
                || p.at_keyword(Keyword::Replace))
            && (p.nth(1) == SyntaxKind::OpeningRoundBracket
                // APPLY can also be followed by a bare function name without parens:
                // e.g. `* APPLY toString`, `alias_value.* APPLY toString`
                || (p.at_keyword(Keyword::Apply) && (p.nth(1) == SyntaxKind::BareWord || p.nth(1) == SyntaxKind::QuotedIdentifier))
                // EXCEPT also supports a bare single column: `* EXCEPT col` —
                // unless the next word starts a query, which is the
                // set-operation form (`SELECT * EXCEPT SELECT ...`).
                || (p.at_keyword(Keyword::Except)
                    && (p.nth(1) == SyntaxKind::BareWord || p.nth(1) == SyntaxKind::QuotedIdentifier)
                    && !p.nth_keyword(1, Keyword::Select)
                    && !p.nth_keyword(1, Keyword::With)))
        {
            // Column transformers: * APPLY(func), * EXCEPT(col), * REPLACE(expr AS name)
            // Can chain: * EXCEPT(id) APPLY(toString)
            // APPLY also supports bare form: * APPLY func; EXCEPT supports a
            // bare single column: * EXCEPT col
            let m = p.precede(lhs);
            p.advance(); // consume APPLY/EXCEPT/REPLACE
            if p.at(SyntaxKind::OpeningRoundBracket) {
                parse_column_transformer_args(p);
            } else {
                // Bare function name form: APPLY func
                let args = p.start();
                parse_expression(p);
                p.complete(args, SyntaxKind::ExpressionList);
            }
            lhs = p.complete(m, SyntaxKind::ColumnTransformer);
        } else {
            break;
        }
    }

    parse_expression_postfix(p, lhs, min_bp);
}

/// Handles postfix and infix operators after an initial LHS expression.
fn parse_expression_postfix(p: &mut Parser, mut lhs: CompletedMarker, min_bp: u8) {
    loop {
        // IS [NOT] NULL / IS [NOT] DISTINCT FROM expr — postfix, binding power 4
        if p.at_keyword(Keyword::Is) && 4 > min_bp {
            let m = p.precede(lhs);
            p.advance(); // consume IS
            p.eat_keyword(Keyword::Not); // optional NOT
            if p.at_keyword(Keyword::Distinct) {
                // IS [NOT] DISTINCT FROM expr
                p.advance(); // consume DISTINCT
                p.expect_keyword(Keyword::From);
                parse_expression_rec(p, 4);
                lhs = p.complete(m, SyntaxKind::IsDistinctFromExpression);
            } else {
                p.expect_keyword(Keyword::Null);
                lhs = p.complete(m, SyntaxKind::IsNullExpression);
            }
            continue;
        }

        // [NOT] BETWEEN expr AND expr — infix, binding power 4
        // Bounds are parsed with min_bp=3 so that AND (bp=2) stops the lower
        // bound but arithmetic (+/-/*) and comparisons are allowed.
        if p.at_keyword(Keyword::Between) && 4 > min_bp {
            let m = p.precede(lhs);
            p.advance(); // consume BETWEEN
            parse_expression_rec(p, 3); // parse low bound (stops at AND)
            p.expect_keyword(Keyword::And);
            parse_expression_rec(p, 3); // parse high bound
            lhs = p.complete(m, SyntaxKind::BetweenExpression);
            continue;
        }

        // NOT BETWEEN, NOT IN, NOT LIKE — prefix NOT modifying a postfix operator
        if p.at_keyword(Keyword::Not) && 4 > min_bp {
            // Peek ahead to see if it's NOT BETWEEN, NOT IN, or NOT LIKE
            // We need to check the next non-trivia token after NOT
            if is_not_followed_by_postfix_op(p) {
                let m = p.precede(lhs);
                p.advance(); // consume NOT

                if p.at_keyword(Keyword::Between) {
                    p.advance(); // consume BETWEEN
                    parse_expression_rec(p, 3);
                    p.expect_keyword(Keyword::And);
                    parse_expression_rec(p, 3);
                    lhs = p.complete(m, SyntaxKind::BetweenExpression);
                } else if p.at_keyword(Keyword::In) {
                    p.advance(); // consume IN
                    parse_in_rhs(p);
                    lhs = p.complete(m, SyntaxKind::InExpression);
                } else if p.at_keyword(Keyword::Like) || p.at_keyword(Keyword::Ilike) {
                    p.advance(); // consume LIKE or ILIKE
                    parse_expression_rec(p, 4);
                    lhs = p.complete(m, SyntaxKind::LikeExpression);
                }
                continue;
            }
        }

        // [GLOBAL] [NOT] IN (...)
        if p.at_keyword(Keyword::Global) && 4 > min_bp {
            let m = p.precede(lhs);
            p.advance(); // consume GLOBAL
            p.eat_keyword(Keyword::Not); // optional NOT
            p.expect_keyword(Keyword::In);
            parse_in_rhs(p);
            lhs = p.complete(m, SyntaxKind::InExpression);
            continue;
        }

        if p.at_keyword(Keyword::In) && 4 > min_bp {
            let m = p.precede(lhs);
            p.advance(); // consume IN
            parse_in_rhs(p);
            lhs = p.complete(m, SyntaxKind::InExpression);
            continue;
        }

        // LIKE / ILIKE — infix, binding power 4
        if (p.at_keyword(Keyword::Like) || p.at_keyword(Keyword::Ilike)) && 4 > min_bp {
            let m = p.precede(lhs);
            p.advance(); // consume LIKE or ILIKE
            parse_expression_rec(p, 4);
            lhs = p.complete(m, SyntaxKind::LikeExpression);
            continue;
        }

        // REGEXP — infix, binding power 4, the same level as LIKE (ClickHouse
        // maps it to `match`). It is its own node rather than a LikeExpression:
        // the right operand is a regular expression, not a LIKE pattern, and
        // consumers that read the pattern must not confuse the two. There is no
        // `NOT REGEXP` — ClickHouse's operator table has no such entry, and the
        // server rejects it — so NOT is deliberately not accepted here.
        if p.at_keyword(Keyword::Regexp) && 4 > min_bp {
            let m = p.precede(lhs);
            p.advance(); // consume REGEXP
            parse_expression_rec(p, 4);
            lhs = p.complete(m, SyntaxKind::MatchExpression);
            continue;
        }

        // Binary operators via Pratt precedence climbing
        let Some(op) = BinOp::from_parser(p) else {
            break;
        };
        if op.binding_power() <= min_bp {
            break;
        }

        let m = p.precede(lhs);
        p.advance();
        parse_expression_rec(p, op.binding_power());
        lhs = p.complete(m, SyntaxKind::BinaryExpression);
    }

    // Ternary operator: expr ? expr : expr
    // Lowest precedence — handled after all binary operators.
    if p.at(SyntaxKind::QuestionMark) && 0 >= min_bp {
        let m = p.precede(lhs);
        p.advance(); // consume ?
        parse_expression(p); // middle ("then") expression
        p.expect(SyntaxKind::Colon);
        parse_expression(p); // right ("else") expression
        p.complete(m, SyntaxKind::TernaryExpression);
    }
}

/// Check if we're at NOT followed by BETWEEN, IN, or LIKE
fn is_not_followed_by_postfix_op(p: &mut Parser) -> bool {
    // We know p is at NOT. We need to peek past NOT to see what follows.
    // The parser skips trivia on nth(), so nth(1) looks at the next non-trivia token after current.
    if p.nth(0) != SyntaxKind::BareWord {
        return false;
    }
    // Look at the token after NOT (skipping whitespace between them)
    // We need to check raw tokens to peek ahead
    let text = p.nth_text(0);
    if !text.eq_ignore_ascii_case("NOT") {
        return false;
    }
    // Now check what's after NOT — we need to look at position 1
    // nth(1) should give us the next non-trivia token
    let next = p.nth(1);
    if next != SyntaxKind::BareWord {
        return false;
    }
    let next_text = p.nth_text(1);
    next_text.eq_ignore_ascii_case("BETWEEN")
        || next_text.eq_ignore_ascii_case("IN")
        || next_text.eq_ignore_ascii_case("LIKE")
        || next_text.eq_ignore_ascii_case("ILIKE")
}

/// Parse the right-hand side of an IN expression: (expr, ...) or (subquery)
fn parse_in_rhs(p: &mut Parser) {
    if p.at(SyntaxKind::OpeningRoundBracket) {
        p.expect(SyntaxKind::OpeningRoundBracket);
        if !p.at(SyntaxKind::ClosingRoundBracket) {
            // Check if it's a subquery
            if at_select_statement(p) {
                let m = p.start();
                parse_select_statement(p);
                p.complete(m, SyntaxKind::SubqueryExpression);
            } else {
                parse_expression(p);
                while p.at(SyntaxKind::Comma) && !p.eof() {
                    p.advance();
                    parse_expression(p);
                }
            }
        }
        p.expect(SyntaxKind::ClosingRoundBracket);
    } else {
        // Could be a table name or other expression
        parse_expression_rec(p, 4);
    }
}

/// Parses a "delimited" (atomic) expression and any postfix operators.
///
/// Atoms: identifiers, literals, `*`, parenthesized expressions, arrays, maps,
/// subqueries, INTERVAL, CASE, NULL, TRUE, FALSE.
/// Postfix: `::` cast operator.
fn expr_delimited(p: &mut Parser) -> Option<CompletedMarker> {
    let result = match p.nth(0) {
        SyntaxKind::Star => {
            let m = p.start();
            p.advance();
            p.complete(m, SyntaxKind::Asterisk)
        }
        SyntaxKind::StringToken => {
            let m = p.start();
            p.advance();
            p.complete(m, SyntaxKind::StringLiteral)
        }
        SyntaxKind::Number => {
            let m = p.start();
            p.advance();
            p.complete(m, SyntaxKind::NumberLiteral)
        }
        // Template placeholder: {{name}}
        SyntaxKind::PlaceholderToken => {
            let m = p.start();
            p.advance();
            p.complete(m, SyntaxKind::PlaceholderExpression)
        }
        SyntaxKind::BareWord | SyntaxKind::QuotedIdentifier => {
            // NULL literal
            if p.at_keyword(Keyword::Null) {
                let m = p.start();
                p.advance();
                p.complete(m, SyntaxKind::NullLiteral)
            }
            // Boolean literals
            else if p.at_keyword(Keyword::True) || p.at_keyword(Keyword::False) {
                let m = p.start();
                p.advance();
                p.complete(m, SyntaxKind::BooleanLiteral)
            }
            // CASE expression
            else if p.at_keyword(Keyword::Case) {
                parse_case_expression(p)
            }
            // CAST(expr AS type) or CAST(expr, 'type_string') — two CAST syntaxes
            else if p.at_keyword(Keyword::Cast) && p.nth(1) == SyntaxKind::OpeningRoundBracket {
                let m = p.start();
                p.advance(); // consume CAST
                p.expect(SyntaxKind::OpeningRoundBracket);
                parse_expression(p);
                if p.at(SyntaxKind::Comma) {
                    // Comma form: CAST(expr, 'TypeString')
                    p.advance(); // consume comma
                    parse_expression(p);
                } else {
                    // Standard form: CAST(expr AS Type)
                    p.expect_keyword(Keyword::As);
                    parse_column_type(p);
                }
                p.expect(SyntaxKind::ClosingRoundBracket);
                p.complete(m, SyntaxKind::CastExpression)
            }
            // TRIM([BOTH|LEADING|TRAILING] [chars] FROM str) — the SQL-standard
            // spelling, which ClickHouse accepts alongside plain trim(str).
            // ltrim/rtrim take no keywords (their side is already fixed), so
            // only `trim` needs the special form.
            else if p.at_keyword(Keyword::Trim) && p.nth(1) == SyntaxKind::OpeningRoundBracket {
                let m = p.start();
                let name = p.start();
                p.advance(); // consume TRIM
                p.complete(name, SyntaxKind::Identifier);
                parse_trim_args(p);
                p.complete(m, SyntaxKind::FunctionCall)
            }
            // INTERVAL expression
            else if p.at_keyword(Keyword::Interval) {
                let m = p.start();
                parse_interval_expression(p);
                p.complete(m, SyntaxKind::IntervalExpression)
            }
            // SQL-standard date/time literals: DATE '2024-01-01',
            // TIMESTAMP '2024-01-01 00:00:00'
            else if (p.nth_text(0).eq_ignore_ascii_case("DATE")
                || p.nth_text(0).eq_ignore_ascii_case("TIMESTAMP"))
                && p.nth(1) == SyntaxKind::StringToken
            {
                let m = p.start();
                p.advance(); // DATE / TIMESTAMP keyword
                p.expect(SyntaxKind::StringToken); // string literal
                p.complete(m, SyntaxKind::DateLiteral)
            }
            // Subquery starting with SELECT/FROM/WITH
            else if at_select_statement(p) {
                let m = p.start();
                parse_select_statement(p);
                p.complete(m, SyntaxKind::SubqueryExpression)
            }
            // Regular identifier / column reference
            // Greedily eats contiguous identifier.identifier chains (db.table.col,
            // json.path.field).  Stops when the segment after a dot is NOT an
            // identifier — numeric tuple indices (a.1) are left for the
            // DotAccessExpression postfix handler, matching ClickHouse semantics.
            //
            // Clause keywords are accepted here: ClickHouse keywords are
            // non-reserved, and a clause can never start where an operand is
            // required (`WHERE sample = 0` references a column named sample).
            // Only an unmistakable clause start ends the expression instead.
            else if !at_recoverable_clause_start(p) {
                let m = p.start();
                p.advance();
                while p.at(SyntaxKind::Dot)
                    && (p.nth(1) == SyntaxKind::BareWord
                        || p.nth(1) == SyntaxKind::QuotedIdentifier)
                    && !p.eof()
                {
                    p.advance(); // consume .
                    p.advance(); // consume identifier
                }
                p.complete(m, SyntaxKind::ColumnReference)
            } else {
                return None;
            }
        }
        // Parenthesized expression or tuple: (expr) or (expr, expr, ...)
        SyntaxKind::OpeningRoundBracket => {
            let m = p.start();
            p.expect(SyntaxKind::OpeningRoundBracket);
            let mut count = 0;
            if !p.at(SyntaxKind::ClosingRoundBracket) {
                parse_expression(p);
                // ClickHouse allows expression aliases inside parens:
                // (expr AS alias).field
                parse_expression_alias(p);
                count += 1;
                while p.at(SyntaxKind::Comma) && !p.eof() {
                    p.advance();
                    parse_expression(p);
                    parse_expression_alias(p);
                    count += 1;
                }
            }

            p.expect(SyntaxKind::ClosingRoundBracket);
            if count > 1 {
                p.complete(m, SyntaxKind::TupleExpression)
            } else {
                p.complete(m, SyntaxKind::Expression)
            }
        }
        // Array literal: [expr, expr, ...] or []
        SyntaxKind::OpeningSquareBracket => {
            let m = p.start();
            p.expect(SyntaxKind::OpeningSquareBracket);

            if !p.at(SyntaxKind::ClosingSquareBracket) {
                parse_expression(p);

                while p.at(SyntaxKind::Comma) && !p.eof() {
                    p.advance();
                    parse_expression(p);
                }
            }

            p.expect(SyntaxKind::ClosingSquareBracket);
            p.complete(m, SyntaxKind::ArrayExpression)
        }
        // Query parameter: {name:Type} or Map literal: {key: value, ...} or {}
        //
        // Query parameters use bare identifier keys: {o:UInt32}, {ts:DateTime64(3)}
        // Map literals use expression keys (typically strings): {'key': value}
        // We distinguish by checking: { BareWord : ... means query parameter.
        SyntaxKind::OpeningCurlyBrace => {
            if super::common::at_query_parameter(p) {
                let m = p.start();
                p.expect(SyntaxKind::OpeningCurlyBrace);
                p.advance(); // parameter name
                p.expect(SyntaxKind::Colon);
                parse_column_type(p); // type (may be complex: DateTime64(3), Array(UInt32), etc.)
                p.expect(SyntaxKind::ClosingCurlyBrace);
                p.complete(m, SyntaxKind::QueryParameterExpression)
            } else {
                let m = p.start();
                p.expect(SyntaxKind::OpeningCurlyBrace);

                if !p.at(SyntaxKind::ClosingCurlyBrace) {
                    parse_expression(p);
                    p.expect(SyntaxKind::Colon);
                    parse_expression(p);

                    while p.at(SyntaxKind::Comma) && !p.eof() {
                        p.advance();
                        parse_expression(p);
                        p.expect(SyntaxKind::Colon);
                        parse_expression(p);
                    }
                }

                p.expect(SyntaxKind::ClosingCurlyBrace);
                p.complete(m, SyntaxKind::MapExpression)
            }
        }
        _ => return None,
    };

    Some(result)
}

/// Parses: CASE [expr] WHEN expr THEN expr [WHEN ... THEN ...] [ELSE expr] END
fn parse_case_expression(p: &mut Parser) -> CompletedMarker {
    let m = p.start();
    p.expect_keyword(Keyword::Case);

    // Optional operand for simple CASE (CASE x WHEN 1 THEN ...)
    if !p.at_keyword(Keyword::When) && !p.at_keyword(Keyword::End) && !p.eof() {
        parse_expression(p);
    }

    // WHEN ... THEN ... clauses
    while p.at_keyword(Keyword::When) && !p.eof() {
        let w = p.start();
        p.advance(); // consume WHEN
        parse_expression(p);
        p.expect_keyword(Keyword::Then);
        parse_expression(p);
        p.complete(w, SyntaxKind::WhenClause);
    }

    // Optional ELSE
    if p.eat_keyword(Keyword::Else) {
        parse_expression(p);
    }

    p.expect_keyword(Keyword::End);
    p.complete(m, SyntaxKind::CaseExpression)
}

fn at_interval_unit(p: &mut Parser) -> bool {
    p.nth(0) == SyntaxKind::BareWord && IntervalUnit::from_str(p.nth_text(0)).is_some()
}

/// Parses: INTERVAL expr UNIT | INTERVAL 'duration_string'
/// e.g. `INTERVAL 5 MINUTE`, `INTERVAL (1 + 2) DAY`, `INTERVAL '2 years'`
fn parse_interval_expression(p: &mut Parser) {
    p.expect_keyword(Keyword::Interval);

    // ClickHouse supports `INTERVAL 'duration_string'` where the string encodes
    // both the value and the unit (e.g. '2 years', '3 months').
    // If the next token is a string literal and is NOT followed by a known
    // interval unit keyword, parse it as a single-string INTERVAL.
    if p.at(SyntaxKind::StringToken) && !at_interval_unit_at(p, 1) {
        p.advance(); // consume the string literal
        return;
    }

    parse_expression(p);
    if at_interval_unit(p) {
        p.advance();
    } else {
        p.recover_with_error("Expected interval unit (e.g. SECOND, MINUTE, HOUR, DAY, WEEK, MONTH, QUARTER, YEAR)");
    }
}

/// Check if the token at offset `n` is a known interval unit keyword.
fn at_interval_unit_at(p: &mut Parser, n: usize) -> bool {
    p.nth(n) == SyntaxKind::BareWord && IntervalUnit::from_str(p.nth_text(n)).is_some()
}

/// Parses a parenthesized argument list: (arg, arg, ...)
/// Handles aggregate DISTINCT: count(DISTINCT x), uniq(DISTINCT x), etc.
fn arg_list(p: &mut Parser) {
    let m = p.start();

    let mut first = true;
    p.expect(SyntaxKind::OpeningRoundBracket);

    // ClickHouse allows DISTINCT as the first token inside aggregate function calls:
    // count(DISTINCT x), uniq(DISTINCT x, y), etc.
    p.eat_keyword(Keyword::Distinct);

    while !p.at(SyntaxKind::ClosingRoundBracket) && !p.eof() {
        // SETTINGS clause inside table function arguments:
        // e.g. mysql('host', db, tbl, 'user', '', SETTINGS connect_timeout = 100)
        if p.at_keyword(Keyword::Settings)
            && (p.nth(1) == SyntaxKind::BareWord || p.nth(1) == SyntaxKind::QuotedIdentifier)
            && p.nth(2) == SyntaxKind::Equals
        {
            parse_optional_settings_clause(p);
            break;
        }
        if !first {
            p.expect(SyntaxKind::Comma);
            // Check for SETTINGS after a comma:
            // e.g. func(arg1, SETTINGS key = value)
            if p.at_keyword(Keyword::Settings)
                && (p.nth(1) == SyntaxKind::BareWord || p.nth(1) == SyntaxKind::QuotedIdentifier)
                && p.nth(2) == SyntaxKind::Equals
            {
                parse_optional_settings_clause(p);
                break;
            }
        }
        arg(p);
        first = false;
    }
    p.expect(SyntaxKind::ClosingRoundBracket);

    p.complete(m, SyntaxKind::ExpressionList);
}

/// Parses a single function argument, detecting lambda expressions (x -> expr).
fn arg(p: &mut Parser) {
    let m = p.start();
    parse_expression(p);

    if p.at(SyntaxKind::Arrow) {
        p.advance();
        parse_expression(p);
        p.complete(m, SyntaxKind::LambdaExpression);
        return;
    }

    // An argument may carry an alias that names the subexpression for the rest
    // of the query: `concat(f(x) AS country, ' - ', g(y))`. ClickHouse parses
    // argument lists as expressions with an OPTIONAL alias, but only the
    // explicit `AS` form — a bare word after an argument is a syntax error
    // there — which is exactly what `parse_expression_alias` accepts.
    parse_expression_alias(p);

    p.complete(m, SyntaxKind::Expression);
}

/// Parses TRIM's argument list, which is keyword-separated rather than
/// comma-separated:
///   trim(str)
///   trim(FROM str)
///   trim(BOTH|LEADING|TRAILING [chars] FROM str)
///
/// A side keyword commits the call to the FROM form (ClickHouse's TrimLayer
/// sets `char_override` and then requires FROM), so a missing FROM is reported
/// rather than silently accepted.
fn parse_trim_args(p: &mut Parser) {
    let m = p.start();
    p.expect(SyntaxKind::OpeningRoundBracket);

    let sided = p.eat_keyword(Keyword::Both)
        || p.eat_keyword(Keyword::Leading)
        || p.eat_keyword(Keyword::Trailing);

    // The characters to strip, present only in the FROM form and optional even
    // there (`trim(BOTH FROM x)` strips whitespace).
    if !p.at_keyword(Keyword::From)
        && !p.at(SyntaxKind::ClosingRoundBracket)
        && !p.eof()
        && !p.end_of_statement()
    {
        arg(p);
    }

    if sided {
        p.expect_keyword(Keyword::From);
        arg(p);
    } else if p.eat_keyword(Keyword::From) {
        arg(p);
    }

    p.expect(SyntaxKind::ClosingRoundBracket);
    p.complete(m, SyntaxKind::ExpressionList);
}

/// Parses a parenthesized argument list for column transformers (APPLY, EXCEPT, REPLACE).
/// Handles the special `expr AS name` syntax used by REPLACE.
fn parse_column_transformer_args(p: &mut Parser) {
    let m = p.start();
    p.expect(SyntaxKind::OpeningRoundBracket);

    let mut first = true;
    while !p.at(SyntaxKind::ClosingRoundBracket) && !p.eof() {
        if !first {
            p.expect(SyntaxKind::Comma);
        }
        first = false;
        parse_expression(p);
        // Handle REPLACE's `expr AS name` syntax
        if p.at_keyword(Keyword::As) {
            let am = p.start();
            p.advance(); // consume AS
            if p.at_identifier() {
                p.advance();
            } else {
                p.recover_with_error("Expected alias after AS");
            }
            p.complete(am, SyntaxKind::ColumnAlias);
        }
    }
    p.expect(SyntaxKind::ClosingRoundBracket);
    p.complete(m, SyntaxKind::ExpressionList);
}

/// Parses a window specification: ( [PARTITION BY ...] [ORDER BY ...] [frame] )
///
/// Called from OVER (...) and WINDOW name AS (...).
pub fn parse_window_spec(p: &mut Parser) {
    let m = p.start();
    p.expect(SyntaxKind::OpeningRoundBracket);

    // Optional PARTITION BY
    if p.at_keyword(Keyword::Partition) {
        p.advance(); // PARTITION
        p.expect_keyword(Keyword::By);
        // expression list until ORDER/ROWS/RANGE/GROUPS/closing paren
        let mut first = true;
        while !p.eof()
            && !p.at(SyntaxKind::ClosingRoundBracket)
            && !p.at_keyword(Keyword::Order)
            && !at_window_frame_keyword(p)
        {
            if !first {
                p.expect(SyntaxKind::Comma);
            }
            first = false;
            parse_expression(p);
        }
    }

    // Optional ORDER BY
    if p.at_keyword(Keyword::Order) {
        p.advance(); // ORDER
        p.expect_keyword(Keyword::By);
        let mut first = true;
        while !p.eof()
            && !p.at(SyntaxKind::ClosingRoundBracket)
            && !at_window_frame_keyword(p)
        {
            if !first {
                p.expect(SyntaxKind::Comma);
            }
            first = false;
            // inline order by item: expr [ASC|DESC] [NULLS FIRST|LAST]
            parse_expression(p);
            if p.at_keyword(Keyword::Asc) || p.at_keyword(Keyword::Desc) {
                p.advance();
            }
            if p.at_keyword(Keyword::Nulls) {
                p.advance();
                if p.at_keyword(Keyword::First) || p.at_keyword(Keyword::Last) {
                    p.advance();
                }
            }
        }
    }

    // Optional frame: ROWS|RANGE|GROUPS BETWEEN bound AND bound
    //                 or ROWS|RANGE|GROUPS bound
    if at_window_frame_keyword(p) {
        let fm = p.start();
        p.advance(); // consume ROWS/RANGE/GROUPS
        if p.at_keyword(Keyword::Between) {
            p.advance(); // consume BETWEEN
            parse_window_frame_bound(p);
            p.expect_keyword(Keyword::And);
            parse_window_frame_bound(p);
        } else {
            // single frame bound (shorthand for BETWEEN bound AND CURRENT ROW)
            parse_window_frame_bound(p);
        }
        p.complete(fm, SyntaxKind::WindowFrame);
    }

    p.expect(SyntaxKind::ClosingRoundBracket);
    p.complete(m, SyntaxKind::WindowSpec);
}

fn at_window_frame_keyword(p: &mut Parser) -> bool {
    p.at_keyword(Keyword::Rows) || p.at_keyword(Keyword::Range) || p.at_keyword(Keyword::Groups)
}

/// Parses a window frame bound:
///   UNBOUNDED PRECEDING | UNBOUNDED FOLLOWING
///   CURRENT ROW
///   expr PRECEDING | expr FOLLOWING
fn parse_window_frame_bound(p: &mut Parser) {
    if p.at_keyword(Keyword::Unbounded) {
        p.advance(); // UNBOUNDED
        if p.at_keyword(Keyword::Preceding) || p.at_keyword(Keyword::Following) {
            p.advance();
        } else {
            p.recover_with_error("Expected PRECEDING or FOLLOWING after UNBOUNDED");
        }
    } else if p.at_keyword(Keyword::Current) {
        p.advance(); // CURRENT
        p.expect_keyword(Keyword::Row);
    } else {
        // expr PRECEDING | expr FOLLOWING
        parse_expression(p);
        if p.at_keyword(Keyword::Preceding) || p.at_keyword(Keyword::Following) {
            p.advance();
        } else {
            p.recover_with_error("Expected PRECEDING or FOLLOWING");
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;
    use expect_test::{expect, Expect};

    fn check(input: &str, expected: Expect) {
        let result = parse(input);
        let mut buf = String::new();
        result.tree.print(&mut buf, 0, &result.source);
        expected.assert_eq(&buf);
    }

    fn check_no_errors(input: &str) {
        let result = parse(input);
        assert!(
            result.errors.is_empty(),
            "Expected no errors for `{input}`, got: {:?}",
            result.errors,
        );
    }

    #[test]
    fn bounds_deeply_nested_parentheses() {
        // Unbounded recursion on deep nesting overflows the stack (and on WASM
        // poisons the whole module instance). Past the depth limit the parser
        // emits an error and stops descending rather than recursing, so the
        // parse stays error-tolerant and never crashes.
        let deep = format!("SELECT {}1{}", "(".repeat(5000), ")".repeat(5000));
        let result = parse(&deep);
        assert!(
            result.errors.iter().any(|e| e.message.contains("nesting depth")),
            "expected a nesting-depth error, got: {:?}",
            result.errors,
        );

        // Ordinary nesting well under the limit still parses cleanly.
        check_no_errors(&format!("SELECT {}1 + 2{}", "(".repeat(50), ")".repeat(50)));
    }

    #[test]
    fn binary_precedence() {
        check("SELECT 1 + 2 * 3", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    BinaryExpression
                      NumberLiteral
                        '1'
                      '+'
                      BinaryExpression
                        NumberLiteral
                          '2'
                        '*'
                        NumberLiteral
                          '3'
        "#]]);
    }

    #[test]
    fn function_call() {
        check("SELECT now()", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    FunctionCall
                      Identifier
                        'now'
                      ExpressionList
                        '('
                        ')'
        "#]]);
    }

    #[test]
    fn bare_except_column_transformer() {
        check_no_errors("SELECT * EXCEPT _row_type, 0 AS bytes FROM t");
        check("SELECT * EXCEPT _row_type FROM t", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ColumnTransformer
                      Asterisk
                        '*'
                      'EXCEPT'
                      ExpressionList
                        ColumnReference
                          '_row_type'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
        "#]]);
    }

    #[test]
    fn except_set_operation_still_parses() {
        // EXCEPT followed by a query keyword is the set operation, not the
        // column transformer.
        check_no_errors("SELECT * FROM a EXCEPT SELECT * FROM b");
    }

    #[test]
    fn date_literal() {
        check_no_errors("SELECT * FROM t WHERE dt > DATE '2024-01-01'");
        check("SELECT DATE '2024-01-01'", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    DateLiteral
                      'DATE'
                      ''2024-01-01''
        "#]]);
    }

    #[test]
    fn timestamp_literal() {
        check_no_errors("SELECT * FROM t WHERE dt < timestamp '2024-01-02 03:04:05'");
        check("SELECT TIMESTAMP '2024-01-02 03:04:05'", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    DateLiteral
                      'TIMESTAMP'
                      ''2024-01-02 03:04:05''
        "#]]);
    }

    #[test]
    fn date_as_identifier_still_parses() {
        // DATE/TIMESTAMP only form literals when immediately followed by a
        // string; as plain identifiers they keep parsing as column references.
        check_no_errors("SELECT date FROM t WHERE date > toDateTime('2024-01-01 00:00:00')");
    }

    #[test]
    fn placeholder_expression() {
        check_no_errors("SELECT * FROM t WHERE dt > {{start_time}} AND dt < {{end_time}}");
        check("SELECT x WHERE a = {{value}}", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ColumnReference
                      'x'
                WhereClause
                  'WHERE'
                  BinaryExpression
                    ColumnReference
                      'a'
                    '='
                    PlaceholderExpression
                      '{{value}}'
        "#]]);
    }

    #[test]
    fn parametric_function() {
        check("SELECT quantile(0.9)(x)", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    FunctionCall
                      Identifier
                        'quantile'
                      ExpressionList
                        '('
                        Expression
                          NumberLiteral
                            '0.9'
                        ')'
                      ExpressionList
                        '('
                        Expression
                          ColumnReference
                            'x'
                        ')'
        "#]]);
    }

    #[test]
    fn cast_expression() {
        check("SELECT x::Int32", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    CastExpression
                      ColumnReference
                        'x'
                      '::'
                      DataType
                        'Int32'
        "#]]);
    }

    #[test]
    fn cast_expression_comma_syntax() {
        check("SELECT CAST('value', 'UUID')", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    CastExpression
                      'CAST'
                      '('
                      StringLiteral
                        ''value''
                      ','
                      StringLiteral
                        ''UUID''
                      ')'
        "#]]);
    }

    #[test]
    fn cast_expression_comma_syntax_with_alias() {
        check("SELECT CAST(x, 'Nullable(String)') AS y", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    CastExpression
                      'CAST'
                      '('
                      ColumnReference
                        'x'
                      ','
                      StringLiteral
                        ''Nullable(String)''
                      ')'
                    ColumnAlias
                      'AS'
                      'y'
        "#]]);
    }

    #[test]
    fn settings_in_table_function() {
        check("SELECT count() FROM mysql('host', db, tbl, 'user', '', SETTINGS connect_timeout = 100)", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    FunctionCall
                      Identifier
                        'count'
                      ExpressionList
                        '('
                        ')'
                FromClause
                  'FROM'
                  TableFunction
                    'mysql'
                    '('
                    StringLiteral
                      ''host''
                    ','
                    ColumnReference
                      'db'
                    ','
                    ColumnReference
                      'tbl'
                    ','
                    StringLiteral
                      ''user''
                    ','
                    StringLiteral
                      ''''
                    ','
                    SettingsClause
                      'SETTINGS'
                      SettingItem
                        'connect_timeout'
                        '='
                        NumberLiteral
                          '100'
                    ')'
        "#]]);
    }

    #[test]
    fn interval_expression() {
        check("SELECT INTERVAL 5 MINUTE", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    IntervalExpression
                      'INTERVAL'
                      NumberLiteral
                        '5'
                      'MINUTE'
        "#]]);
    }

    #[test]
    fn interval_string_literal() {
        check("SELECT INTERVAL '2 years'", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    IntervalExpression
                      'INTERVAL'
                      ''2 years''
        "#]]);
    }

    #[test]
    fn interval_string_literal_no_errors() {
        check_no_errors("SELECT INTERVAL '2 years'");
        check_no_errors("SELECT INTERVAL '3 months'");
        check_no_errors("SELECT now() + INTERVAL '1 day'");
    }

    #[test]
    fn array_literal() {
        check("SELECT [1, 2, 3]", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ArrayExpression
                      '['
                      NumberLiteral
                        '1'
                      ','
                      NumberLiteral
                        '2'
                      ','
                      NumberLiteral
                        '3'
                      ']'
        "#]]);
    }

    #[test]
    fn lambda_in_function() {
        check("SELECT arrayMap(x -> x + 1, arr)", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    FunctionCall
                      Identifier
                        'arrayMap'
                      ExpressionList
                        '('
                        LambdaExpression
                          ColumnReference
                            'x'
                          '->'
                          BinaryExpression
                            ColumnReference
                              'x'
                            '+'
                            NumberLiteral
                              '1'
                        ','
                        Expression
                          ColumnReference
                            'arr'
                        ')'
        "#]]);
    }

    #[test]
    fn logical_operators() {
        check("SELECT 1 FROM t WHERE a > 1 AND b < 2 OR c = 3", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    NumberLiteral
                      '1'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
                WhereClause
                  'WHERE'
                  BinaryExpression
                    BinaryExpression
                      BinaryExpression
                        ColumnReference
                          'a'
                        '>'
                        NumberLiteral
                          '1'
                      'AND'
                      BinaryExpression
                        ColumnReference
                          'b'
                        '<'
                        NumberLiteral
                          '2'
                    'OR'
                    BinaryExpression
                      ColumnReference
                        'c'
                      '='
                      NumberLiteral
                        '3'
        "#]]);
    }

    #[test]
    fn nested_dot_access() {
        check("SELECT json.nested.path", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ColumnReference
                      'json'
                      '.'
                      'nested'
                      '.'
                      'path'
        "#]]);
    }

    // === New expression type tests ===

    #[test]
    fn unary_not() {
        check("SELECT NOT true", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    UnaryExpression
                      'NOT'
                      BooleanLiteral
                        'true'
        "#]]);
    }

    #[test]
    fn unary_not_not() {
        check("SELECT NOT NOT false", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    UnaryExpression
                      'NOT'
                      UnaryExpression
                        'NOT'
                        BooleanLiteral
                          'false'
        "#]]);
    }

    #[test]
    fn unary_minus() {
        check("SELECT -1", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    UnaryExpression
                      '-'
                      NumberLiteral
                        '1'
        "#]]);
    }

    #[test]
    fn unary_minus_paren() {
        check("SELECT -(1 + 2)", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    UnaryExpression
                      '-'
                      Expression
                        '('
                        BinaryExpression
                          NumberLiteral
                            '1'
                          '+'
                          NumberLiteral
                            '2'
                        ')'
        "#]]);
    }

    #[test]
    fn between_expression() {
        check("SELECT x BETWEEN 1 AND 10", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    BetweenExpression
                      ColumnReference
                        'x'
                      'BETWEEN'
                      NumberLiteral
                        '1'
                      'AND'
                      NumberLiteral
                        '10'
        "#]]);
    }

    #[test]
    fn not_between_expression() {
        check("SELECT x NOT BETWEEN 1 AND 10", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    BetweenExpression
                      ColumnReference
                        'x'
                      'NOT'
                      'BETWEEN'
                      NumberLiteral
                        '1'
                      'AND'
                      NumberLiteral
                        '10'
        "#]]);
    }

    #[test]
    fn in_expression() {
        check("SELECT x IN (1, 2, 3)", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    InExpression
                      ColumnReference
                        'x'
                      'IN'
                      '('
                      NumberLiteral
                        '1'
                      ','
                      NumberLiteral
                        '2'
                      ','
                      NumberLiteral
                        '3'
                      ')'
        "#]]);
    }

    #[test]
    fn not_in_expression() {
        check("SELECT x NOT IN (1, 2, 3)", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    InExpression
                      ColumnReference
                        'x'
                      'NOT'
                      'IN'
                      '('
                      NumberLiteral
                        '1'
                      ','
                      NumberLiteral
                        '2'
                      ','
                      NumberLiteral
                        '3'
                      ')'
        "#]]);
    }

    #[test]
    fn global_in_expression() {
        check("SELECT x GLOBAL IN (SELECT 1)", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    InExpression
                      ColumnReference
                        'x'
                      'GLOBAL'
                      'IN'
                      '('
                      SubqueryExpression
                        SelectStatement
                          SelectClause
                            'SELECT'
                            ColumnList
                              NumberLiteral
                                '1'
                      ')'
        "#]]);
    }

    #[test]
    fn like_expression() {
        check("SELECT x LIKE '%test%'", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    LikeExpression
                      ColumnReference
                        'x'
                      'LIKE'
                      StringLiteral
                        ''%test%''
        "#]]);
    }

    #[test]
    fn not_like_expression() {
        check("SELECT x NOT LIKE '%test%'", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    LikeExpression
                      ColumnReference
                        'x'
                      'NOT'
                      'LIKE'
                      StringLiteral
                        ''%test%''
        "#]]);
    }

    #[test]
    fn trim_with_side_keyword() {
        check("SELECT trim(BOTH ' ' FROM x)", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    FunctionCall
                      Identifier
                        'trim'
                      ExpressionList
                        '('
                        'BOTH'
                        Expression
                          StringLiteral
                            '' ''
                        'FROM'
                        Expression
                          ColumnReference
                            'x'
                        ')'
        "#]]);
    }

    #[test]
    fn trim_variants() {
        check_no_errors("SELECT trim(x)");
        check_no_errors("SELECT trim(FROM x)");
        check_no_errors("SELECT trim(BOTH FROM x)");
        check_no_errors("SELECT trim(LEADING 'x' FROM y)");
        check_no_errors("SELECT trim(TRAILING 'x' FROM y)");
        // ltrim/rtrim have no side keyword to parse; they stay ordinary calls.
        check_no_errors("SELECT ltrim(x), rtrim(x)");
    }

    #[test]
    fn trim_side_keyword_requires_from() {
        // ClickHouse commits to the FROM form once a side keyword is seen.
        let result = parse("SELECT trim(BOTH ' ' x)");
        assert!(
            result.errors.iter().any(|e| e.message.contains("FROM")),
            "expected a missing-FROM error, got: {:?}",
            result.errors,
        );
    }

    #[test]
    fn alias_on_a_function_argument() {
        check("SELECT concat(f(x) AS country, ' - ')", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    FunctionCall
                      Identifier
                        'concat'
                      ExpressionList
                        '('
                        Expression
                          FunctionCall
                            Identifier
                              'f'
                            ExpressionList
                              '('
                              Expression
                                ColumnReference
                                  'x'
                              ')'
                          ColumnAlias
                            'AS'
                            'country'
                        ','
                        Expression
                          StringLiteral
                            '' - ''
                        ')'
        "#]]);
    }

    #[test]
    fn argument_alias_requires_as() {
        // ClickHouse accepts only the explicit `AS` form inside an argument
        // list; a bare word there is a syntax error on the server too, so the
        // parser must not silently absorb it as an alias.
        let result = parse("SELECT concat(f(x) country, ' - ')");
        assert!(
            !result.errors.is_empty(),
            "expected an error for a bare argument alias",
        );

        // Error tolerance: a dangling AS reports once and keeps the call intact.
        let result = parse("SELECT concat(f(x) AS, 'y')");
        assert!(
            result.errors.len() == 1,
            "expected exactly one error, got: {:?}",
            result.errors,
        );
    }

    #[test]
    fn leading_dot_number() {
        check("SELECT x * .1", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    BinaryExpression
                      ColumnReference
                        'x'
                      '*'
                      NumberLiteral
                        '.1'
        "#]]);
        check_no_errors("SELECT ((logins * .1) - orders) AS value FROM t");
    }

    #[test]
    fn tuple_access_is_not_a_leading_dot_number() {
        check("SELECT x.1", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    DotAccessExpression
                      ColumnReference
                        'x'
                      '.'
                      '1'
        "#]]);
        check_no_errors("SELECT x.1.1, f(x).1 FROM t");
    }

    #[test]
    fn regexp_expression() {
        check("SELECT x REGEXP '^/v1/.*'", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    MatchExpression
                      ColumnReference
                        'x'
                      'REGEXP'
                      StringLiteral
                        ''^/v1/.*''
        "#]]);
    }

    #[test]
    fn regexp_binds_like_a_comparison() {
        // Binding power 4, the same as LIKE: AND splits the two operands rather
        // than being swallowed by the right-hand side.
        check_no_errors("SELECT * FROM t WHERE a REGEXP 'x' AND b = 1");
        check("SELECT a REGEXP 'x' AND b", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    BinaryExpression
                      MatchExpression
                        ColumnReference
                          'a'
                        'REGEXP'
                        StringLiteral
                          ''x''
                      'AND'
                      ColumnReference
                        'b'
        "#]]);
    }

    #[test]
    fn regexp_without_pattern_recovers() {
        // Error tolerance: a REGEXP with nothing to its right reports one error
        // and still yields a tree covering the rest of the statement.
        let result = parse("SELECT * FROM t WHERE a REGEXP");
        assert!(
            result.errors.iter().any(|e| e.message.contains("Expected expression")),
            "expected a missing-operand error, got: {:?}",
            result.errors,
        );
    }

    #[test]
    fn regexp_as_a_column_name() {
        // REGEXP is not reserved: at operand position it is still an identifier.
        check_no_errors("SELECT regexp FROM t");
        check_no_errors("SELECT 1 AS regexp");
    }

    #[test]
    fn is_null_expression() {
        check("SELECT x IS NULL", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    IsNullExpression
                      ColumnReference
                        'x'
                      'IS'
                      'NULL'
        "#]]);
    }

    #[test]
    fn is_not_null_expression() {
        check("SELECT x IS NOT NULL", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    IsNullExpression
                      ColumnReference
                        'x'
                      'IS'
                      'NOT'
                      'NULL'
        "#]]);
    }

    #[test]
    fn case_when_else() {
        check("SELECT CASE WHEN x > 1 THEN 'a' ELSE 'b' END", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    CaseExpression
                      'CASE'
                      WhenClause
                        'WHEN'
                        BinaryExpression
                          ColumnReference
                            'x'
                          '>'
                          NumberLiteral
                            '1'
                        'THEN'
                        StringLiteral
                          ''a''
                      'ELSE'
                      StringLiteral
                        ''b''
                      'END'
        "#]]);
    }

    #[test]
    fn case_simple() {
        check("SELECT CASE x WHEN 1 THEN 'one' WHEN 2 THEN 'two' END", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    CaseExpression
                      'CASE'
                      ColumnReference
                        'x'
                      WhenClause
                        'WHEN'
                        NumberLiteral
                          '1'
                        'THEN'
                        StringLiteral
                          ''one''
                      WhenClause
                        'WHEN'
                        NumberLiteral
                          '2'
                        'THEN'
                        StringLiteral
                          ''two''
                      'END'
        "#]]);
    }

    #[test]
    fn null_literal() {
        check("SELECT NULL", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    NullLiteral
                      'NULL'
        "#]]);
    }

    #[test]
    fn boolean_literals() {
        check("SELECT TRUE, FALSE", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    BooleanLiteral
                      'TRUE'
                    ','
                    BooleanLiteral
                      'FALSE'
        "#]]);
    }

    #[test]
    fn map_literal() {
        check("SELECT {'key': 'value', 'k2': 'v2'}", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    MapExpression
                      '{'
                      StringLiteral
                        ''key''
                      ':'
                      StringLiteral
                        ''value''
                      ','
                      StringLiteral
                        ''k2''
                      ':'
                      StringLiteral
                        ''v2''
                      '}'
        "#]]);
    }

    #[test]
    fn empty_map_literal() {
        check("SELECT {}", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    MapExpression
                      '{'
                      '}'
        "#]]);
    }

    #[test]
    fn query_parameter() {
        check("SELECT {o:UInt32}", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    QueryParameterExpression
                      '{'
                      'o'
                      ':'
                      DataType
                        'UInt32'
                      '}'
        "#]]);
    }

    #[test]
    fn query_parameter_complex_type() {
        check("SELECT {ts:DateTime64(3)}", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    QueryParameterExpression
                      '{'
                      'ts'
                      ':'
                      DataType
                        'DateTime64'
                        DataTypeParameters
                          '('
                          NumberLiteral
                            '3'
                          ')'
                      '}'
        "#]]);
    }

    #[test]
    fn query_parameter_in_where() {
        check("SELECT 1 WHERE x >= {o:UInt32}", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    NumberLiteral
                      '1'
                WhereClause
                  'WHERE'
                  BinaryExpression
                    ColumnReference
                      'x'
                    '>='
                    QueryParameterExpression
                      '{'
                      'o'
                      ':'
                      DataType
                        'UInt32'
                      '}'
        "#]]);
    }

    // === Array access (subscript) tests ===

    #[test]
    fn array_access_string_key() {
        // Map-style access: SpanAttributes['test.key']
        check("SELECT SpanAttributes['test.key']", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ArrayAccessExpression
                      ColumnReference
                        'SpanAttributes'
                      '['
                      StringLiteral
                        ''test.key''
                      ']'
        "#]]);
    }

    #[test]
    fn array_access_numeric_index() {
        check("SELECT arr[1]", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ArrayAccessExpression
                      ColumnReference
                        'arr'
                      '['
                      NumberLiteral
                        '1'
                      ']'
        "#]]);
    }

    #[test]
    fn array_access_chained() {
        // Nested access: matrix[0][1]
        check("SELECT matrix[0][1]", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ArrayAccessExpression
                      ArrayAccessExpression
                        ColumnReference
                          'matrix'
                        '['
                        NumberLiteral
                          '0'
                        ']'
                      '['
                      NumberLiteral
                        '1'
                      ']'
        "#]]);
    }

    #[test]
    fn array_access_on_function_result() {
        // Access on function call: splitByChar(',', x)[1]
        check("SELECT splitByChar(',', x)[1]", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ArrayAccessExpression
                      FunctionCall
                        Identifier
                          'splitByChar'
                        ExpressionList
                          '('
                          Expression
                            StringLiteral
                              '',''
                          ','
                          Expression
                            ColumnReference
                              'x'
                          ')'
                      '['
                      NumberLiteral
                        '1'
                      ']'
        "#]]);
    }

    #[test]
    fn array_access_with_expression_key() {
        // Dynamic key: arr[i + 1]
        check("SELECT arr[i + 1]", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ArrayAccessExpression
                      ColumnReference
                        'arr'
                      '['
                      BinaryExpression
                        ColumnReference
                          'i'
                        '+'
                        NumberLiteral
                          '1'
                      ']'
        "#]]);
    }

    #[test]
    fn array_access_in_where_clause() {
        check("SELECT 1 FROM t WHERE attrs['status'] = 'ok'", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    NumberLiteral
                      '1'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
                WhereClause
                  'WHERE'
                  BinaryExpression
                    ArrayAccessExpression
                      ColumnReference
                        'attrs'
                      '['
                      StringLiteral
                        ''status''
                      ']'
                    '='
                    StringLiteral
                      ''ok''
        "#]]);
    }

    #[test]
    fn array_access_with_dot_and_subscript() {
        // Dotted column + subscript: otel.SpanAttributes['key']
        check("SELECT otel.SpanAttributes['key']", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ArrayAccessExpression
                      ColumnReference
                        'otel'
                        '.'
                        'SpanAttributes'
                      '['
                      StringLiteral
                        ''key''
                      ']'
        "#]]);
    }

    #[test]
    fn ignore_nulls() {
        check("SELECT any(x) IGNORE NULLS FROM t", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    NullsModifier
                      FunctionCall
                        Identifier
                          'any'
                        ExpressionList
                          '('
                          Expression
                            ColumnReference
                              'x'
                          ')'
                      'IGNORE'
                      'NULLS'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
        "#]]);
    }

    #[test]
    fn ignore_nulls_before_over() {
        // The modifier sits between the call and OVER; leaving NULLS unconsumed
        // used to strand the whole window specification.
        check_no_errors(
            "SELECT last_value(x) IGNORE NULLS OVER (PARTITION BY a ORDER BY b) FROM t",
        );
        check_no_errors("SELECT first_value(x) RESPECT NULLS OVER w FROM t WINDOW w AS ()");
    }

    #[test]
    fn ignore_without_nulls_is_an_alias() {
        // `IGNORE` alone is not a modifier — it is an ordinary alias, and the
        // lookahead must not claim it.
        check_no_errors("SELECT count(x) ignore FROM t");
    }

    #[test]
    fn respect_nulls() {
        check("SELECT first_value(x) RESPECT NULLS FROM t", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    NullsModifier
                      FunctionCall
                        Identifier
                          'first_value'
                        ExpressionList
                          '('
                          Expression
                            ColumnReference
                              'x'
                          ')'
                      'RESPECT'
                      'NULLS'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
        "#]]);
    }

    #[test]
    fn column_transformer_apply() {
        check("SELECT * APPLY(toString) FROM t", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ColumnTransformer
                      Asterisk
                        '*'
                      'APPLY'
                      ExpressionList
                        '('
                        ColumnReference
                          'toString'
                        ')'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
        "#]]);
    }

    #[test]
    fn column_transformer_except() {
        check("SELECT * EXCEPT(id) FROM t", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ColumnTransformer
                      Asterisk
                        '*'
                      'EXCEPT'
                      ExpressionList
                        '('
                        ColumnReference
                          'id'
                        ')'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
        "#]]);
    }

    #[test]
    fn column_transformer_replace() {
        check("SELECT * REPLACE(id + 1 AS id) FROM t", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ColumnTransformer
                      Asterisk
                        '*'
                      'REPLACE'
                      ExpressionList
                        '('
                        BinaryExpression
                          ColumnReference
                            'id'
                          '+'
                          NumberLiteral
                            '1'
                        ColumnAlias
                          'AS'
                          'id'
                        ')'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
        "#]]);
    }

    #[test]
    fn column_transformer_chained() {
        check("SELECT * EXCEPT(id) APPLY(toString) FROM t", expect![[r#"
            File
              SelectStatement
                SelectClause
                  'SELECT'
                  ColumnList
                    ColumnTransformer
                      ColumnTransformer
                        Asterisk
                          '*'
                        'EXCEPT'
                        ExpressionList
                          '('
                          ColumnReference
                            'id'
                          ')'
                      'APPLY'
                      ExpressionList
                        '('
                        ColumnReference
                          'toString'
                        ')'
                FromClause
                  'FROM'
                  TableIdentifier
                    't'
        "#]]);
    }
}
