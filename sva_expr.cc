#include "sva_expr.h"

#include "PExpr.h"

PSvaExpr::PSvaExpr(Kind kind)
: kind_(kind)
{
}

PSvaExpr::~PSvaExpr()
{
      delete left_;
      delete right_;
}

PSvaExpr* PSvaExpr::make_atom(PExpr* expr)
{
      PSvaExpr* node = new PSvaExpr(ATOM);
      node->atom_expr_ = expr;
      return node;
}

PSvaExpr* PSvaExpr::make_if(PExpr* cond, PSvaExpr* then_expr, PSvaExpr* else_expr)
{
      PSvaExpr* node = new PSvaExpr(IF);
      node->atom_expr_ = cond;
      node->left_ = then_expr;
      node->right_ = else_expr;
      return node;
}

PSvaExpr* PSvaExpr::make_not(PSvaExpr* expr)
{
      PSvaExpr* node = new PSvaExpr(NOT);
      node->left_ = expr;
      return node;
}

PSvaExpr* PSvaExpr::make_and(PSvaExpr* left, PSvaExpr* right)
{
      PSvaExpr* node = new PSvaExpr(AND);
      node->left_ = left;
      node->right_ = right;
      return node;
}

PSvaExpr* PSvaExpr::make_or(PSvaExpr* left, PSvaExpr* right)
{
      PSvaExpr* node = new PSvaExpr(OR);
      node->left_ = left;
      node->right_ = right;
      return node;
}

PSvaExpr* PSvaExpr::make_iff(PSvaExpr* left, PSvaExpr* right)
{
      PSvaExpr* node = new PSvaExpr(IFF);
      node->left_ = left;
      node->right_ = right;
      return node;
}

PSvaExpr* PSvaExpr::make_implies(PSvaExpr* ant, PSvaExpr* cons, bool nonoverlap)
{
      PSvaExpr* node = new PSvaExpr(nonoverlap ? IMPLIES_NONOVERLAP : IMPLIES);
      node->left_ = ant;
      node->right_ = cons;
      return node;
}

PSvaExpr* PSvaExpr::make_concat(PSvaExpr* left, int min_delay, int max_delay, PSvaExpr* right)
{
      PSvaExpr* node = new PSvaExpr(CONCAT);
      node->left_ = left;
      node->right_ = right;
      node->min_delay_ = min_delay;
      node->max_delay_ = max_delay;
      return node;
}

PSvaExpr* PSvaExpr::make_concat_expr(PSvaExpr* left, PExpr* min_delay_expr,
                                     PExpr* max_delay_expr, bool max_unbounded,
                                     PSvaExpr* right)
{
      PSvaExpr* node = new PSvaExpr(CONCAT);
      node->left_ = left;
      node->right_ = right;
      node->min_delay_expr_ = min_delay_expr;
      node->max_delay_expr_ = max_delay_expr;
      node->max_delay_ = max_unbounded ? -1 : 0;
      return node;
}

PSvaExpr* PSvaExpr::make_delay(int min_delay, int max_delay, PSvaExpr* child)
{
      PSvaExpr* node = new PSvaExpr(DELAY);
      node->left_ = child;
      node->min_delay_ = min_delay;
      node->max_delay_ = max_delay;
      return node;
}

PSvaExpr* PSvaExpr::make_delay_expr(PExpr* min_delay_expr, PExpr* max_delay_expr,
                                    bool max_unbounded, PSvaExpr* child)
{
      PSvaExpr* node = new PSvaExpr(DELAY);
      node->left_ = child;
      node->min_delay_expr_ = min_delay_expr;
      node->max_delay_expr_ = max_delay_expr;
      node->max_delay_ = max_unbounded ? -1 : 0;
      return node;
}

PSvaExpr* PSvaExpr::make_repeat(PSvaExpr* child, int min_rep, int max_rep, RepeatKind kind)
{
      PSvaExpr* node = new PSvaExpr(REPEAT);
      node->left_ = child;
      node->min_rep_ = min_rep;
      node->max_rep_ = max_rep;
      node->rep_kind_ = kind;
      return node;
}

PSvaExpr* PSvaExpr::make_throughout(PSvaExpr* cond, PSvaExpr* seq)
{
      PSvaExpr* node = new PSvaExpr(THROUGHOUT);
      node->left_ = cond;
      node->right_ = seq;
      return node;
}

PSvaExpr* PSvaExpr::make_until(PSvaExpr* left, PSvaExpr* right, bool strong, bool with)
{
      PSvaExpr* node = new PSvaExpr(with ? (strong ? S_UNTIL_WITH : UNTIL_WITH)
                                         : (strong ? S_UNTIL : UNTIL));
      node->left_ = left;
      node->right_ = right;
      node->strong_ = strong;
      node->with_ = with;
      return node;
}

PSvaExpr* PSvaExpr::make_first_match(PSvaExpr* child)
{
      PSvaExpr* node = new PSvaExpr(FIRST_MATCH);
      node->left_ = child;
      return node;
}

PSvaExpr* PSvaExpr::clone() const
{
      PSvaExpr* node = new PSvaExpr(kind_);
      node->atom_expr_ = atom_expr_;
      node->min_delay_ = min_delay_;
      node->max_delay_ = max_delay_;
      node->min_delay_expr_ = min_delay_expr_;
      node->max_delay_expr_ = max_delay_expr_;
      node->min_rep_ = min_rep_;
      node->max_rep_ = max_rep_;
      node->rep_kind_ = rep_kind_;
      node->strong_ = strong_;
      node->with_ = with_;
      if (left_)
            node->left_ = left_->clone();
      if (right_)
            node->right_ = right_->clone();
      return node;
}
