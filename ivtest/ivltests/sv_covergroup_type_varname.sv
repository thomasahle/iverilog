class MyConfig;
endclass

class MyTx;
  int data;
endclass

class MyCoverage;
  covergroup cg with function sample(MyConfig MyConfig, MyTx MyTx);
    option.per_instance = 1;
  endgroup : cg
  
  function new(string name);
  endfunction
endclass

module test;
  initial begin
    $display("PASSED");
    $finish;
  end
endmodule
