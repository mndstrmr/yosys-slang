#include "kernel/log.h"
#include "kernel/rtlil.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/util/Util.h"
#include "slang_frontend.h"
#include <algorithm>
#include <vector>

#include "formal.h"
#include "diag.h"

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
	RTLIL::SigSpec sig;
	int start;

	AssertionMatch(EvalContext& eval_, RTLIL::SigSpec sig_): eval(eval_), sig(sig_), start(0) {}

private:
	AssertionMatch(EvalContext& eval_, RTLIL::SigSpec sig_, int start_): eval(eval_), sig(sig_), start(start_) {}

public:
	void operator=(AssertionMatch other) {
		sig = other.sig;
		start = other.start;
	}

	AssertionMatch shift(int time) const {
		if (sig.is_fully_const()) return { eval, sig, start + time };
		return { eval, past(eval, sig, time, RTLIL::State::Sx), start + time };
	}

	AssertionMatch operator||(AssertionMatch& other) const {
		if (sig.is_fully_const() && sig.as_bool()) return { eval, true, std::max(other.start, start) };
		if (sig.is_fully_const() && !sig.as_bool()) return { eval, other.sig, std::max(other.start, start) };
		if (other.sig.is_fully_const() && other.sig.as_bool()) return { eval, true, std::max(other.start, start) };
		if (other.sig.is_fully_const() && !other.sig.as_bool()) return { eval, sig, std::max(other.start, start) };
		return { eval, eval.netlist.LogicOr(sig, other.sig), std::max(other.start, start) };
	}

	AssertionMatch operator&&(AssertionMatch& other) const {
		if (sig.is_fully_const() && sig.as_bool()) return { eval, other.sig, std::max(other.start, start) };
		if (sig.is_fully_const() && !sig.as_bool()) return { eval, false, std::max(other.start, start) };
		if (other.sig.is_fully_const() && other.sig.as_bool()) return { eval, sig, std::max(other.start, start) };
		if (other.sig.is_fully_const() && !other.sig.as_bool()) return { eval, false, std::max(other.start, start) };
		return { eval, eval.netlist.LogicAnd(sig, other.sig), std::max(other.start, start) };
	}

	AssertionMatch operator!() const {
		if (sig.is_fully_const()) return { eval, !sig.as_bool(), start };
		return { eval, eval.netlist.LogicNot(sig), start };
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
	if (in.empty()) return {};
	AssertionMatch collapsed = in[0];
	for (int i = 1; i < in.size(); i++) {
		if (collapsed.start >= in[i].start)
			collapsed = in[i].shift(collapsed.start - in[i].start) || collapsed;
		else
			collapsed = collapsed.shift(in[i].start - collapsed.start) || in[i];
	}
	return { !collapsed };
}

static std::vector<AssertionMatch> seq_vec(std::vector<AssertionMatch> a, int min, int max, std::vector<AssertionMatch> b) {
	std::vector<AssertionMatch> new_own_paths;
	for (auto path : a) {
		for (int offset = min; offset <= max; offset++) {
			for (auto inner : b)
				new_own_paths.push_back(path.shift(offset + inner.start) && inner);
		}
	}
	return compress_paths(new_own_paths);
}

// Empty indicates error
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
				own_paths.push_back({eval, true});
				for (int i = 0; i < sequence.elements.size(); i++) {
					auto inner_paths = synthesizeAssertionExpr(eval, *sequence.elements[i].sequence);

					auto delay = sequence.elements[i].delay;
					if (!delay.max.has_value()) {
						eval.netlist.add_diag(diag::AssertionUnsupported, expr.syntax->sourceRange().start());
						return {};
					}

					own_paths = seq_vec(own_paths, delay.min, delay.max.value(), inner_paths);
				}
				return own_paths;
			}
		case slang::ast::AssertionExprKind::Unary:
			{
				const auto& uop = expr.as<ast::UnaryAssertionExpr>();
				switch (uop.op) {
				case slang::ast::UnaryAssertionOperator::Not:
					return not_vec(synthesizeAssertionExpr(eval, uop.expr));

				case slang::ast::UnaryAssertionOperator::NextTime:
				case slang::ast::UnaryAssertionOperator::SNextTime:
				case slang::ast::UnaryAssertionOperator::Always:
				case slang::ast::UnaryAssertionOperator::SAlways:
				case slang::ast::UnaryAssertionOperator::Eventually:
				case slang::ast::UnaryAssertionOperator::SEventually:
					eval.netlist.add_diag(diag::AssertionUnsupported, expr.syntax->sourceRange().start());
					return {};
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
					/*
					When te1 and te2 are sequences, then the composite sequence te1 and te2 matches if te1 and te2 match.
					The end time is the end time of either te1 or te2, whichever matches last.
					*/
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
					/*
					If the operands te1 and te2 are expressions, then te1 or te2 matches at any clock tick on which at least
					one of te1 and te2 evaluates to true.
					*/
					if (left.empty() || right.empty()) return {}; // Propogate errors
					left.insert(left.end(), right.begin(), right.end());
					return left;
				}
				case ast::BinaryAssertionOperator::OverlappedImplication:
					return not_vec(seq_vec(left, 0, 0, not_vec(right)));
				case ast::BinaryAssertionOperator::NonOverlappedImplication:
					return not_vec(seq_vec(left, 1, 1, not_vec(right)));

				case ast::BinaryAssertionOperator::Intersect:
				case ast::BinaryAssertionOperator::Throughout:
				case ast::BinaryAssertionOperator::Within:
				case ast::BinaryAssertionOperator::Iff:
				case ast::BinaryAssertionOperator::Until:
				case ast::BinaryAssertionOperator::SUntil:
				case ast::BinaryAssertionOperator::UntilWith:
				case ast::BinaryAssertionOperator::SUntilWith:
				case ast::BinaryAssertionOperator::Implies:
				case ast::BinaryAssertionOperator::OverlappedFollowedBy:
				case ast::BinaryAssertionOperator::NonOverlappedFollowedBy:
					eval.netlist.add_diag(diag::AssertionUnsupported, expr.syntax->sourceRange().start());
					return {};
				}
			}
		case slang::ast::AssertionExprKind::Clocking:
			{
				const auto& clocking = expr.as<ast::ClockingAssertionExpr>();
				// Ignore clocking information, since we just use a global clock anyway
				return synthesizeAssertionExpr(eval, clocking.expr);
			}
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

		case slang::ast::AssertionExprKind::SequenceWithMatch:
		case slang::ast::AssertionExprKind::FirstMatch:
		case slang::ast::AssertionExprKind::StrongWeak:
		case slang::ast::AssertionExprKind::Abort:
		case slang::ast::AssertionExprKind::Conditional:
		case slang::ast::AssertionExprKind::Case:
			eval.netlist.add_diag(diag::AssertionUnsupported, expr.syntax->sourceRange().start());
			return {};
	}
	log_abort(); // Unreachable
};

RTLIL::SigSpec evalAssertion(EvalContext& eval, const ast::AssertionExpr& assertion) {
	auto paths = synthesizeAssertionExpr(eval, assertion);
	if (paths.empty()) return false; // Ran into an error

	auto sig = paths[0];
	for (size_t i = 1; i < paths.size(); i++) sig = sig || paths[i];

	auto init_escape = past(eval, false, sig.start, true);
	// Checks are disabled until all(?) paths are in the frame
	return eval.netlist.LogicOr(sig.sig, init_escape);
}

}
