function Bit#(1) and1(Bit#(1) a, Bit#(1) b);
    return a&b;
endfunction

function Bit#(1) or1(Bit#(1) a, Bit#(1) b);
    return a|b;
endfunction

function Bit#(1) not1(Bit#(1) a);
    return ~a;
endfunction

// Exercise 1
function Bit#(1) multiplexer1(Bit#(1) sel, Bit#(1) a, Bit#(1) b);
    // (a & (~sel)) | (b & sel)
    // 4 gates required
    return or1(and1(a, not1(sel)), and1(b, sel));
endfunction

// Exercise 3
function Bit#(n) multiplexer_n(Bit#(1) sel, Bit#(n) a, Bit#(n) b);
    Bit#(n) aggregate;
    for (Integer i = 0; i < valueOf(n); i=i+1) begin
        aggregate[i] = multiplexer1(sel, a[i], b[i]);
    end
    return aggregate;
endfunction

// Exercise 2
function Bit#(5) multiplexer5(Bit#(1) sel, Bit#(5) a, Bit#(5) b);
    return multiplexer_n(sel, a, b);
endfunction