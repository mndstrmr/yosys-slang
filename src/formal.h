#include <memory>
#include <vector>
#include "kernel/rtlil.h"

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
RTLIL::SigSpec evalAssertion(EvalContext& eval, const ast::AssertionExpr& assertion);

}
