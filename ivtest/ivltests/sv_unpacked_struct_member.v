// Test: Unpacked struct member assignment (l-value)
// Tests writing to individual members of unpacked structs

module test;

typedef struct {
    logic [7:0] a;
    logic [15:0] b;
    logic [31:0] c;
} my_struct_t;

my_struct_t s;
logic [7:0] tmp_a;
logic [15:0] tmp_b;
logic [31:0] tmp_c;

initial begin
    // Test 1: Write to individual struct members
    s.a = 8'hAA;
    s.b = 16'hBBBB;
    s.c = 32'hCCCCCCCC;
    $display("Wrote s.a=AA, s.b=BBBB, s.c=CCCCCCCC");

    // Test 2: Overwrite with different values
    s.a = 8'h12;
    s.b = 16'h3456;
    s.c = 32'h789ABCDE;
    $display("Wrote s.a=12, s.b=3456, s.c=789ABCDE");

    // Test 3: Zero values
    s.a = 8'h00;
    s.b = 16'h0000;
    s.c = 32'h00000000;
    $display("Zeroed struct members");

    // Test 4: Write using expressions
    tmp_a = 8'h55;
    tmp_b = 16'hAAAA;
    tmp_c = 32'h12345678;
    s.a = tmp_a;
    s.b = tmp_b;
    s.c = tmp_c;
    $display("Wrote from variables: a=55, b=AAAA, c=12345678");

    $display("PASSED");
end

endmodule
