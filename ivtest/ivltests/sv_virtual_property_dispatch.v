// Test virtual method dispatch through property access
// When a derived class object is stored in a base class property,
// calling a virtual method through that property should dispatch
// to the derived class implementation

class animal;
    function new();
    endfunction

    virtual function string speak();
        return "...";
    endfunction
endclass

class dog extends animal;
    virtual function string speak();
        return "woof";
    endfunction
endclass

class cat extends animal;
    virtual function string speak();
        return "meow";
    endfunction
endclass

// Container that holds an animal reference
class kennel;
    animal pet;

    function void set_pet(animal a);
        pet = a;
    endfunction

    function string get_pet_sound();
        return pet.speak();  // Should dispatch to derived class
    endfunction
endclass

module test;
    kennel k;
    dog d;
    cat c;
    string sound;
    int errors;

    initial begin
        errors = 0;

        // Test 1: Dog stored in kennel
        k = new();
        d = new();
        k.set_pet(d);
        sound = k.get_pet_sound();
        if (sound != "woof") begin
            $display("FAILED Test 1: Expected 'woof', got '%s'", sound);
            errors++;
        end

        // Test 2: Direct access to property
        sound = k.pet.speak();
        if (sound != "woof") begin
            $display("FAILED Test 2: Expected 'woof' from k.pet.speak(), got '%s'", sound);
            errors++;
        end

        // Test 3: Cat stored in kennel
        c = new();
        k.set_pet(c);
        sound = k.get_pet_sound();
        if (sound != "meow") begin
            $display("FAILED Test 3: Expected 'meow', got '%s'", sound);
            errors++;
        end

        // Test 4: Direct property access for cat
        sound = k.pet.speak();
        if (sound != "meow") begin
            $display("FAILED Test 4: Expected 'meow' from k.pet.speak(), got '%s'", sound);
            errors++;
        end

        if (errors == 0) begin
            $display("PASSED");
        end else begin
            $display("FAILED: %0d errors", errors);
        end

        $finish;
    end
endmodule
