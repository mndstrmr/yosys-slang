#include <memory>
#include <vector>
#include "kernel/rtlil.h"

/*
SVA is a difficult language to implement, in fact it's difficult even to state the semantics of. I formalise it as per the below (extract from our Lean 4 definitions).
Essentially, we expand a property into all of it's paths. This obviously blows up (exponentially) in general, but it's good for most realistic properties.

structure Trace (α : Type u) where
  get : Nat -> α

structure TimingDelay where
  min : Nat
  count : Nat
def TimingDelay.range (td : TimingDelay) : List Nat := -- obvious definition
def TimingDelay.const (n : Nat) : TimingDelay := { min := n, count := 0 }

structure RepeatCount where
  min : Nat
  count : Nat
def RepeatCount.range (rc : RepeatCount) : List Nat := -- obvious definition

inductive SVA (α : Type u)
| state : (α -> Prop) -> SVA α
| seq : SVA α -> TimingDelay -> SVA α -> SVA α
| not : SVA α -> SVA α
| or : SVA α -> SVA α -> SVA α
| and : SVA α -> SVA α -> SVA α
| repeats : SVA α -> RepeatCount -> SVA α

def SVA.true : SVA α := .state (fun _ => True)
def SVA.false : SVA α := .state (fun _ => False)
def SVA.implies (a c : SVA α) : SVA α := .or (.seq a (.const 0) c) (.not a)
def SVA.non_overlapped_implies (a c : SVA α) : SVA α := .or (.seq a (.const 1) c) (.not a)

inductive SeqPath (α : Type u)
| state : (α -> Prop) -> Nat -> SeqPath α
| or : SeqPath α -> SeqPath α -> SeqPath α
| and : SeqPath α -> SeqPath α -> SeqPath α
| not : SeqPath α -> SeqPath α
def SeqPath.true : SeqPath α := .state (fun _ => True) 0
def SeqPath.false : SeqPath α := .state (fun _ => False) 0

def SeqPath.shift (p : SeqPath α) (s : Nat) : SeqPath α := match p with
| state t n => .state t (n + s)
| or a b => .or (a.shift s) (b.shift s)
-- etc

def SeqPath.end : SeqPath α -> Nat
| state _ n => n
| or a b => a.end.max b.end
-- etc

def SVA.paths : SVA α -> List (SeqPath α)
| state t => [.state t 0]
| seq pre td post =>
  pre.paths.flatMap (fun a =>
    td.range.flatMap (fun td =>
      post.paths.map (fun b =>
        a.and (b.shift (a.end + td)))))
| or a b => a.paths.append b.paths
| and a b =>
  a.paths.flatMap (fun a =>
    b.paths.map (fun b =>
      a.and b))
| repeats a rc => rc.range.flatMap (SeqPath.cross a.paths)
| not a => [(a.paths.foldl (fun a b => a.or b) SeqPath.false).not]

def SeqPath.sats (p : SeqPath α) (pi : Trace α) : Prop := match p with
| state t n => t (pi.get n)
| or a b => a.sats pi ∨ b.sats pi
| and a b => a.sats pi ∧ b.sats pi
| not a => ¬a.sats pi
*/

namespace slang {
	namespace ast {
		class Expression;
		class AssertionExpr;
	};
};

namespace slang_frontend {

class EvalContext;

namespace RTLIL = ::Yosys::RTLIL;
namespace ast = ::slang::ast;

RTLIL::SigSpec past(EvalContext& eval, RTLIL::SigSpec sig, int time, RTLIL::Const init);

// class SeqPath {
// public:
//   // All nodes are shared. This helps keeps memory down once we hit exponential growth.
//   // using SeqPathPtr = std::shared_ptr<SeqPath>;
//   struct SeqPathPtr {
//     std::shared_ptr<SeqPath> ptr;
//     SeqPath* operator->() { return ptr.get(); }
//     const SeqPath* operator->() const { return ptr.get(); }

//     template<typename... _Args>
//     static SeqPathPtr make(_Args&&... __args) {
//       return { std::make_shared<SeqPath>(__args...) };
//     }

//     SeqPathPtr() = delete;
//     SeqPathPtr(std::shared_ptr<SeqPath> p): ptr(p) {}
//   };

  // Note some differences to the above formal definitions:
  // 1. We introduce a Shift node, where the shift it has is applied to all child nodes recursively
  // 2. We encode the False node as a NULL expr, and a True node seperately. FIXME: Feels a bit ugly.
  // enum SeqPathType {
  //   Shift, State, Or, And, Not, True
  // } type;

  // // Applies recursively to all inner nodes
  // union {
  //   struct {
  //     int shift;
  //     SeqPathPtr inner;
  //   };
  //   const ast::Expression* expr;
  //   struct {
  //     SeqPathPtr left;
  //     SeqPathPtr right;
  //   };
  // };

  // ~SeqPath() {}

  // explicit SeqPath(SeqPathType typ, SeqPathPtr inner_, int shift_ = 0): type(typ), inner(inner_), shift(shift_) {}
  // explicit SeqPath(SeqPathType typ, SeqPathPtr left_, SeqPathPtr right_): type(typ), left(left_), right(right_) {}
  // explicit SeqPath(SeqPathType typ, const ast::Expression* expr_): type(typ), expr(expr_) {}
  
  // static SeqPathPtr shift_by(SeqPathPtr inner, int shift) {
  //   if (shift == 0) return inner;
  //   if (inner->type == Shift)
  //     return SeqPathPtr::make(Shift, inner->left, shift + inner->shift);
  //   return SeqPathPtr::make(Shift, inner, shift);
  // }
  // static SeqPathPtr or_(SeqPathPtr left, SeqPathPtr right) {
  //   if (left->type == True) return left;
  //   if (right->type == True) return right;
  //   if (left->type == State && left->expr == NULL) return right;
  //   if (right->type == State && right->expr == NULL) return left;
  //   return SeqPathPtr::make(Or, left, right);
  // }
  // static SeqPathPtr and_(SeqPathPtr left, SeqPathPtr right) {
  //   if (left->type == True) return right;
  //   if (right->type == True) return left;
  //   if (left->type == State && left->expr == NULL) return left;
  //   if (right->type == State && right->expr == NULL) return right;
  //   return SeqPathPtr::make(And, left, right);
  // }
  // static SeqPathPtr not_(SeqPathPtr left) {
  //   if (left->type == True) return false_();
  //   if (left->type == State && left->expr == NULL) return true_();
  //   return SeqPathPtr::make(Not, left);
  // }
  // static SeqPathPtr state(const ast::Expression* expr) {
  //   return SeqPathPtr::make(State, expr);
  // }
  // static SeqPathPtr false_() {
  //   static SeqPathPtr false_ = SeqPathPtr::make(State, (const ast::Expression*) NULL);
  //   return false_;
  // }
  // static SeqPathPtr true_() {
  //   static SeqPathPtr true_ = SeqPathPtr::make(True, (SeqPathPtr) NULL);
  //   return true_;
  // }

  // int end() const {
  //   if (type == True || type == State) return 0;
  //   if (type == Shift) return inner->end() + shift;
  //   if (type == Not) return left->end();
  //   if (type == Or || type == And) return std::max(left->end(), right->end());
  //   log_abort();
  // }

//   static std::vector<SeqPathPtr> pathsFromAssertionExpr(const ast::AssertionExpr& expr);

//   RTLIL::SigSpec synthesize(EvalContext& eval, int offset, const RTLIL::SigSpec* clk) const;
//   RTLIL::SigSpec synthesize_backward(EvalContext& eval, const RTLIL::SigSpec* clk) const {
//     return synthesize(eval, -end(), clk);
//   }
//   static RTLIL::SigSpec synthesize_all(EvalContext& eval, std::vector<SeqPathPtr>& paths, const RTLIL::SigSpec* clk);

//   void dump(int depth = 0) const;
// };
  // static RTLIL::SigSpec synthesize_all(EvalContext& eval, std::vector<SeqPathPtr>& paths, const RTLIL::SigSpec* clk);

RTLIL::SigSpec evalAssertion(EvalContext& eval, const ast::AssertionExpr& assertion);

}
