// Test parameterized mailbox (SV 15.4)
module test;
    // Basic unparameterized mailbox
    mailbox m1;

    // Parameterized mailbox with int
    mailbox #(int) m2;

    // Parameterized mailbox with custom type
    typedef struct packed {
        logic [7:0] a;
        logic [7:0] b;
    } data_t;
    mailbox #(data_t) m3;

    initial begin
        int val;
        data_t d_out, d_in;

        // Test basic mailbox
        m1 = new();
        m1.put(100);
        m1.get(val);
        if (val !== 100) begin
            $display("FAILED: basic mailbox, got %d", val);
            $finish;
        end

        // Test int parameterized mailbox
        m2 = new();
        m2.put(200);
        m2.get(val);
        if (val !== 200) begin
            $display("FAILED: int mailbox, got %d", val);
            $finish;
        end

        // Test struct parameterized mailbox
        m3 = new();
        d_in.a = 8'hAB;
        d_in.b = 8'hCD;
        m3.put(d_in);
        m3.get(d_out);
        if (d_out !== d_in) begin
            $display("FAILED: struct mailbox, got %h", d_out);
            $finish;
        end

        // Test num() method
        m1.put(1);
        m1.put(2);
        if (m1.num() !== 2) begin
            $display("FAILED: num() returned %d, expected 2", m1.num());
            $finish;
        end

        $display("PASSED");
    end
endmodule
