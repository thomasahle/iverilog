// Test using a type name as a variable name
// This is valid SystemVerilog when the variable shadows the type

class MyConfig;
  int value;
endclass

class MyTransaction;
  int data;
endclass

// Class with covergroup that uses type names as parameter names
class MyCoverage;
  covergroup cg with function sample(MyConfig MyConfig, MyTransaction MyTransaction);
    option.per_instance = 1;
    DATA_CP: coverpoint MyTransaction.data;
  endgroup : cg
  
  function new();
  endfunction
endclass

// Function with type name as parameter name
function automatic void process_config(MyConfig MyConfig);
  $display("Config value: %0d", MyConfig.value);
endfunction

// Task with type name as parameter name  
task automatic handle_transaction(MyTransaction MyTransaction);
  $display("Transaction data: %0d", MyTransaction.data);
endtask

module test;
  MyConfig cfg;
  MyTransaction tx;
  
  initial begin
    cfg = new();
    cfg.value = 42;
    tx = new();
    tx.data = 100;
    
    process_config(cfg);
    handle_transaction(tx);
    
    $display("PASSED - Type name as variable name works");
    $finish;
  end
endmodule
