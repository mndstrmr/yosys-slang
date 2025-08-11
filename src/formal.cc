#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/util/Util.h"
#include "slang_frontend.h"
#include <algorithm>
#include <vector>

#include "formal.h"

namespace slang_frontend {

RTLIL::SigSpec past(EvalContext& eval, RTLIL::SigSpec sig, int time, RTLIL::Const init) {
	for (int i = 0; i < time; i++) {
		auto next = eval.netlist.canvas->addWire(eval.netlist.new_id(), sig.size());
		next->attributes[ID::init] = init;
		eval.netlist.canvas->addFf(eval.netlist.new_id(), sig, next);
		sig = next;
	}
	return sig;
}

struct AssertionMatch {
  EvalContext& eval;
  std::optional<RTLIL::SigSpec> sig; // None = always true
  int start;

  AssertionMatch(EvalContext& eval_, std::optional<RTLIL::SigSpec> sig_): eval(eval_), sig(sig_), start(0) {}

private:
  AssertionMatch(EvalContext& eval_, std::optional<RTLIL::SigSpec> sig_, int start_): eval(eval_), sig(sig_), start(start_) {}

public:
  void operator=(AssertionMatch other) {
    sig = other.sig;
    start = other.start;
  }

  AssertionMatch shift(int time) const {
    if (!sig.has_value()) return { eval, {}, start + time };
    return { eval, past(eval, sig.value(), time, false), start + time };
  }

  AssertionMatch operator||(AssertionMatch& other) const {
    if (!sig.has_value() || !other.sig.has_value()) return { eval, {}, std::max(other.start, start) };
    return { eval, eval.netlist.LogicOr(sig.value(), other.sig.value()), std::max(other.start, start) };
  }

  AssertionMatch operator&&(AssertionMatch& other) const {
    if (!sig.has_value()) return { eval, other.sig, std::max(other.start, start)};
    if (!other.sig.has_value()) return { eval, sig, std::max(other.start, start)};
    return { eval, eval.netlist.LogicAnd(sig.value(), other.sig.value()), std::max(other.start, start) };
  }

  AssertionMatch operator!() const {
    if (!sig.has_value()) log_abort(); // This should never happen
    return { eval, eval.netlist.LogicNot(sig.value()), start };
  }
};

static std::vector<AssertionMatch> compress_paths(std::vector<AssertionMatch> paths) {
  struct amcmp {
    bool operator()(AssertionMatch& a, AssertionMatch& b) const {
      return a.start > b.start;
    }
  };
  std::sort(paths.begin(), paths.end(), (amcmp) {});
  
  std::vector<AssertionMatch> grouped;
  std::optional<AssertionMatch> group;
  int time = -1;
  for (auto path : paths) {
    if (path.start != time) {
      if (group.has_value()) grouped.push_back(group.value());
      time = path.start;
      group = path;
    } else {
      group = group.value() || path;
    }
  }
  if (group.has_value()) grouped.push_back(group.value());
  
  return grouped;
}

static std::vector<AssertionMatch> not_vec(std::vector<AssertionMatch> in) {
  if (in.empty()) log_abort();
	AssertionMatch collapsed = in[0];
	for (int i = 1; i < in.size(); i++) {
    if (collapsed.start >= in[i].start)
      collapsed = in[i].shift(collapsed.start - in[i].start) || collapsed;
    else
      collapsed = collapsed.shift(in[i].start - collapsed.start) || in[i];
	}
	return { !collapsed };
}

static std::vector<AssertionMatch> seq_vec(std::vector<AssertionMatch> a, slang::ast::SequenceRange delay, std::vector<AssertionMatch> b) {
  if (!delay.max.has_value())
    log_abort();
  int max = delay.max.value();

  std::vector<AssertionMatch> new_own_paths;
  for (auto path : a) {
    for (int offset = delay.min; offset <= max; offset++) {
	    for (auto inner : b)
		    new_own_paths.push_back(path.shift(offset + inner.start) && inner);
    }
  }
  return compress_paths(new_own_paths);
}

static std::vector<AssertionMatch> synthesizeAssertionExpr(EvalContext& eval, const ast::AssertionExpr& expr) {
  switch (expr.kind) {
    case slang::ast::AssertionExprKind::Invalid:
    	log_abort();
    case slang::ast::AssertionExprKind::Simple:
    	{
    		const auto& simple = expr.as<ast::SimpleAssertionExpr>();
    		return {{ eval, simple.isNullExpr ? false : eval(simple.expr) }};
    	}
    case slang::ast::AssertionExprKind::SequenceConcat:
    	{
  			const auto& sequence = expr.as<ast::SequenceConcatExpr>();
  			std::vector<AssertionMatch> own_paths;
  			own_paths.push_back({eval, {}});
  			for (int i = 0; i < sequence.elements.size(); i++) {
  			  auto inner_paths = synthesizeAssertionExpr(eval, *sequence.elements[i].sequence);
  			  own_paths = seq_vec(own_paths, sequence.elements[i].delay, inner_paths);
  			}
  			return own_paths;
    	}
    case slang::ast::AssertionExprKind::SequenceWithMatch: log_abort();
    case slang::ast::AssertionExprKind::Unary:
    	{
  			const auto& uop = expr.as<ast::UnaryAssertionExpr>();
  			switch (uop.op) {
          case slang::ast::UnaryAssertionOperator::Not:
            return not_vec(synthesizeAssertionExpr(eval, uop.expr));
          case slang::ast::UnaryAssertionOperator::NextTime: log_abort();
          case slang::ast::UnaryAssertionOperator::SNextTime: log_abort();
          case slang::ast::UnaryAssertionOperator::Always: log_abort();
          case slang::ast::UnaryAssertionOperator::SAlways: log_abort();
          case slang::ast::UnaryAssertionOperator::Eventually: log_abort();
          case slang::ast::UnaryAssertionOperator::SEventually: log_abort();
          }
        }
    case slang::ast::AssertionExprKind::Binary:
  		{
  			const auto& biop = expr.as<ast::BinaryAssertionExpr>();
  			auto left = synthesizeAssertionExpr(eval, biop.left);
  			auto right = synthesizeAssertionExpr(eval, biop.right);

  			switch (biop.op) {
  			case ast::BinaryAssertionOperator::And:
  				{
  				  std::vector<AssertionMatch> results;
  				  for (auto a : left) {
  				    for (auto b : right) {
  				      if (a.start >= b.start)
    				      results.push_back(b.shift(a.start - b.start) && a);
    				    else
    				      results.push_back(a.shift(b.start - a.start) && b);
  				    }
  				  }
  				  return compress_paths(results);
  				}
  			case ast::BinaryAssertionOperator::Or:
  				{
  				  left.insert(left.end(), right.begin(), right.end());
  				  return left;
  				}
  			case ast::BinaryAssertionOperator::Intersect: log_abort();
  			case ast::BinaryAssertionOperator::Throughout: log_abort();
  			case ast::BinaryAssertionOperator::Within: log_abort();
  			case ast::BinaryAssertionOperator::Iff: log_abort();
  			case ast::BinaryAssertionOperator::Until: log_abort();
  			case ast::BinaryAssertionOperator::SUntil: log_abort();
  			case ast::BinaryAssertionOperator::UntilWith: log_abort();
  			case ast::BinaryAssertionOperator::SUntilWith: log_abort();
  			case ast::BinaryAssertionOperator::Implies: log_abort();
  			case ast::BinaryAssertionOperator::OverlappedImplication:
  				{
  				  auto a_then_not_b = seq_vec(left, { .min = 0, .max = 0 }, not_vec(right));
  				  return not_vec(a_then_not_b);
  				}
  			case ast::BinaryAssertionOperator::NonOverlappedImplication:
  				{
  				  auto a_then_not_b = seq_vec(left, { .min = 1, .max = 1 }, not_vec(right));
  				  return not_vec(a_then_not_b);
  				}
  			case ast::BinaryAssertionOperator::OverlappedFollowedBy: log_abort();
  			case ast::BinaryAssertionOperator::NonOverlappedFollowedBy: log_abort();
  			}
  		}
    case slang::ast::AssertionExprKind::FirstMatch: log_abort();
    case slang::ast::AssertionExprKind::Clocking:
      {
        const auto& clocking = expr.as<ast::ClockingAssertionExpr>();
        // Ignore clocking information, since we just use a global clock anyway
        return synthesizeAssertionExpr(eval, clocking.expr);
      }
    case slang::ast::AssertionExprKind::StrongWeak: log_abort();
    case slang::ast::AssertionExprKind::Abort: log_abort();
    case slang::ast::AssertionExprKind::Conditional: log_abort();
    case slang::ast::AssertionExprKind::Case: log_abort();
    case slang::ast::AssertionExprKind::DisableIff:
  		{
  			const auto& disableiff = expr.as<ast::DisableIffAssertionExpr>();
  		  auto disable = (AssertionMatch) {eval, eval(disableiff.condition)};
  		  auto inner = synthesizeAssertionExpr(eval, disableiff.expr);
  		  std::vector<AssertionMatch> disables;
  		  disables.push_back(disable);
  		  for (int i = 0; i < inner.size(); i++) {
  		    std::optional<AssertionMatch> this_disables = {};
  		    for (int t = 0; t <= inner[i].start; t++) {
  		      while (disables.size() <= t)
  		        disables.push_back(disables[disables.size() - 1].shift(1));

  		      if (this_disables.has_value())
    		      this_disables = this_disables.value() || disables[t];
    		    else
    		      this_disables = disables[t];
  		    }
  		    if (this_disables.has_value())
  		      inner[i] = this_disables.value() || inner[i];
  		  }
  		  return inner;
  		}
  }
  log_abort(); // Unreachable
};

AssertionMatch synthesizeAll(EvalContext& eval, std::vector<AssertionMatch>& paths) {
    auto sig = paths[0];
    for (size_t i = 1; i < paths.size(); i++) sig = sig || paths[i];
    return sig;
}

RTLIL::SigSpec evalAssertion(EvalContext& eval, const ast::AssertionExpr& assertion) {
	auto paths = synthesizeAssertionExpr(eval, assertion);
	auto sig = synthesizeAll(eval, paths);
	auto init_escape = past(eval, false, sig.start, true);
	// Checks are disabled until all(?) paths are in the frame
	if (!sig.sig.has_value()) log_abort();
	return eval.netlist.LogicOr(sig.sig.value(), init_escape);
}

}
