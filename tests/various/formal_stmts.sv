module m_assert(input logic x);
	always_comb assert(x);
endmodule

module m_assume(input logic x);
	always_comb assume(x);
endmodule

module m_cover(input logic x);
	always_comb cover(x);
endmodule

module m_assert_conc(input logic x);
	named: assert property(x);
endmodule

module m_assume_conc(input logic x);
	assume property(x);
endmodule

module m_cover_conc(input logic x);
	cover property(x);
endmodule
