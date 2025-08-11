module m_assert(input logic x);
	always_comb assert(x);
endmodule

module m_assume(input logic x);
	always_comb assume(x);
endmodule

module m_cover(input logic x);
	always_comb cover(x);
endmodule

module m_assert_conc(input logic clk_i, input logic x);
	named: assert property(@(posedge clk_i) x);
endmodule

module m_assume_conc(input logic clk_i, input logic x);
	named: assume property(@(posedge clk_i) x);
endmodule

module m_cover_conc(input logic clk_i, input logic x);
	named: cover property(@(posedge clk_i) x);
endmodule

module m_assert_seq_1(input logic clk_i, input logic x, input logic y);
	named: assert property(@(posedge clk_i) x ##1 y);
endmodule

module m_assert_seq_2(input logic clk_i, input logic x, input logic y);
	named: assert property(@(posedge clk_i) x ##[1:2] y);
endmodule

module m_assert_seq_3(input logic clk_i, input logic x, input logic y, input logic z);
	named: assert property(@(posedge clk_i) x ##[1:2] y |=> (z ##[1:2] x) or (##1 y));
endmodule

module m_assert_seq_4(input logic clk_i, input logic x, input logic y, input logic z);
	named: assert property(@(posedge clk_i) ((z ##[1:2] x) and (##1 y)) ##1 x);
endmodule

module m_assert_seq_5(input logic clk_i, input logic x);
	named: assert property(@(posedge clk_i) ##3 x);
endmodule

module m_assert_seq_6(input logic clk_i, input logic x, input logic y, input logic z);
	named: assert property(@(posedge clk_i) x |=> y or (##1 z));
endmodule

module m_assert_seq_7(input logic clk_i, input logic x, input logic y, input logic z);
	named: assert property(@(posedge clk_i) disable iff (~z)  x |-> ##3 ~y);
endmodule

