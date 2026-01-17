#ifndef IVL_SVA_EXPR_H
#define IVL_SVA_EXPR_H

#include "LineInfo.h"

class PExpr;

class PSvaExpr : public LineInfo {
public:
      enum Kind {
            ATOM,
            IF,
            NOT,
            AND,
            OR,
            IFF,
            IMPLIES,
            IMPLIES_NONOVERLAP,
            CONCAT,
            DELAY,
            REPEAT,
            THROUGHOUT,
            UNTIL,
            UNTIL_WITH,
            S_UNTIL,
            S_UNTIL_WITH,
            FIRST_MATCH
      };

      enum RepeatKind {
            REP_CONSEC,   // Consecutive repetition [*n]
            REP_GOTO,     // Goto repetition [->n]
            REP_NONCON    // Non-consecutive repetition [=n]
      };

      PSvaExpr(Kind kind);
      ~PSvaExpr() override;

      static PSvaExpr* make_atom(PExpr* expr);
      static PSvaExpr* make_if(PExpr* cond, PSvaExpr* then_expr, PSvaExpr* else_expr);
      static PSvaExpr* make_not(PSvaExpr* expr);
      static PSvaExpr* make_and(PSvaExpr* left, PSvaExpr* right);
      static PSvaExpr* make_or(PSvaExpr* left, PSvaExpr* right);
      static PSvaExpr* make_iff(PSvaExpr* left, PSvaExpr* right);
      static PSvaExpr* make_implies(PSvaExpr* ant, PSvaExpr* cons, bool nonoverlap);
      static PSvaExpr* make_concat(PSvaExpr* left, int min_delay, int max_delay, PSvaExpr* right);
      static PSvaExpr* make_concat_expr(PSvaExpr* left, PExpr* min_delay_expr,
                                        PExpr* max_delay_expr, bool max_unbounded,
                                        PSvaExpr* right);
      static PSvaExpr* make_delay(int min_delay, int max_delay, PSvaExpr* child);
      static PSvaExpr* make_delay_expr(PExpr* min_delay_expr, PExpr* max_delay_expr,
                                       bool max_unbounded, PSvaExpr* child);
      static PSvaExpr* make_repeat(PSvaExpr* child, int min_rep, int max_rep, RepeatKind kind);
      static PSvaExpr* make_throughout(PSvaExpr* cond, PSvaExpr* seq);
      static PSvaExpr* make_until(PSvaExpr* left, PSvaExpr* right, bool strong, bool with);
      static PSvaExpr* make_first_match(PSvaExpr* child);

      PSvaExpr* clone() const;

      Kind kind() const { return kind_; }
      PExpr* atom_expr() const { return atom_expr_; }
      PExpr* cond_expr() const { return atom_expr_; }
      PSvaExpr* left() const { return left_; }
      PSvaExpr* right() const { return right_; }
      int min_delay() const { return min_delay_; }
      int max_delay() const { return max_delay_; }
      PExpr* min_delay_expr() const { return min_delay_expr_; }
      PExpr* max_delay_expr() const { return max_delay_expr_; }
      int min_rep() const { return min_rep_; }
      int max_rep() const { return max_rep_; }
      RepeatKind rep_kind() const { return rep_kind_; }
      bool strong() const { return strong_; }
      bool with() const { return with_; }

private:
      Kind kind_;
      PExpr* atom_expr_ = nullptr;
      PSvaExpr* left_ = nullptr;
      PSvaExpr* right_ = nullptr;

      int min_delay_ = 0;
      int max_delay_ = 0;
      PExpr* min_delay_expr_ = nullptr;
      PExpr* max_delay_expr_ = nullptr;
      int min_rep_ = 0;
      int max_rep_ = 0;
      RepeatKind rep_kind_ = REP_CONSEC;
      bool strong_ = false;
      bool with_ = false;
};

#endif /* IVL_SVA_EXPR_H */
