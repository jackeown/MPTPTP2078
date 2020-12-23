%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:23 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :   95 (  95 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u28,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) )).

cnf(u27,negated_conjecture,
    ( v4_yellow_0(sK1,sK0) )).

cnf(u21,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u36,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_orders_2(X0) )).

cnf(u43,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u45,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) )).

cnf(u59,negated_conjecture,
    ( r1_orders_2(sK0,sK6(sK0,X2,X3),sK3)
    | ~ r2_hidden(sK6(sK0,X2,X3),sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r2_lattice3(sK0,X2,X3) )).

cnf(u58,negated_conjecture,
    ( r1_orders_2(sK0,sK5(sK0,X0,X1),sK3)
    | ~ r2_hidden(sK5(sK0,X0,X1),sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X1) )).

cnf(u55,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK3)
    | ~ r2_hidden(sK3,sK2)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u39,axiom,
    ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u35,axiom,
    ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u32,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_orders_2(X0) )).

cnf(u46,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3) )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u31,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u47,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u26,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u38,axiom,
    ( r2_hidden(sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u34,axiom,
    ( r2_hidden(sK5(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u51,axiom,
    ( r2_hidden(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | r2_lattice3(X1,X2,X0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(X1)) )).

cnf(u50,axiom,
    ( r2_hidden(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | r1_lattice3(X1,X2,X0)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(X1)) )).

cnf(u49,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u48,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u63,negated_conjecture,
    ( ~ r2_hidden(sK6(sK0,X0,sK3),sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,X0,sK3) )).

cnf(u40,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u37,axiom,
    ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u33,axiom,
    ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u42,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u54,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,sK2)
    | r1_orders_2(sK0,X0,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u24,negated_conjecture,
    ( sK3 = sK4 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (9738)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.47  % (9745)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (9745)# SZS output start Saturation.
% 0.21/0.49  cnf(u28,negated_conjecture,
% 0.21/0.49      m1_yellow_0(sK1,sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u27,negated_conjecture,
% 0.21/0.49      v4_yellow_0(sK1,sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u21,negated_conjecture,
% 0.21/0.49      r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u36,axiom,
% 0.21/0.49      ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~l1_orders_2(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u43,negated_conjecture,
% 0.21/0.49      ~r2_lattice3(sK1,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u45,negated_conjecture,
% 0.21/0.49      ~r2_lattice3(sK1,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u59,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK6(sK0,X2,X3),sK3) | ~r2_hidden(sK6(sK0,X2,X3),sK2) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_lattice3(sK0,X2,X3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u58,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK5(sK0,X0,X1),sK3) | ~r2_hidden(sK5(sK0,X0,X1),sK2) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u55,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,sK3,sK3) | ~r2_hidden(sK3,sK2) | r1_lattice3(sK0,sK2,sK3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u39,axiom,
% 0.21/0.49      ~r1_orders_2(X0,sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u35,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u32,axiom,
% 0.21/0.49      ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~l1_orders_2(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u46,negated_conjecture,
% 0.21/0.49      ~r1_lattice3(sK1,sK2,sK3) | r2_lattice3(sK0,sK2,sK3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u30,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u31,axiom,
% 0.21/0.49      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u47,negated_conjecture,
% 0.21/0.49      l1_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u29,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u26,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u38,axiom,
% 0.21/0.49      r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u34,axiom,
% 0.21/0.49      r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u51,axiom,
% 0.21/0.49      r2_hidden(sK6(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,X2,X0) | v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u50,axiom,
% 0.21/0.49      r2_hidden(sK5(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_lattice3(X1,X2,X0) | v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u49,negated_conjecture,
% 0.21/0.49      r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u48,negated_conjecture,
% 0.21/0.49      r2_hidden(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u63,negated_conjecture,
% 0.21/0.49      ~r2_hidden(sK6(sK0,X0,sK3),sK2) | r1_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,X0,sK3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u40,axiom,
% 0.21/0.49      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u37,axiom,
% 0.21/0.49      m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u33,axiom,
% 0.21/0.49      m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u42,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u25,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u54,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r1_orders_2(sK0,X0,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.21/0.49  
% 0.21/0.49  cnf(u41,axiom,
% 0.21/0.49      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u24,negated_conjecture,
% 0.21/0.49      sK3 = sK4).
% 0.21/0.49  
% 0.21/0.49  % (9745)# SZS output end Saturation.
% 0.21/0.49  % (9745)------------------------------
% 0.21/0.49  % (9745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9745)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (9745)Memory used [KB]: 6140
% 0.21/0.49  % (9745)Time elapsed: 0.066 s
% 0.21/0.49  % (9745)------------------------------
% 0.21/0.49  % (9745)------------------------------
% 0.21/0.49  % (9741)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (9731)Success in time 0.133 s
%------------------------------------------------------------------------------
