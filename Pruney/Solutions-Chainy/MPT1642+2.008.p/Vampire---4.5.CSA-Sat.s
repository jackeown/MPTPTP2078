%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:03 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   72 (  72 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u35,axiom,
    ( ~ v4_orders_2(X0)
    | ~ r1_orders_2(X0,X3,X2)
    | ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X3) )).

cnf(u61,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK3(sK0,X1,sK2))
    | r1_lattice3(sK0,X1,sK2)
    | m1_subset_1(sK3(sK0,X1,sK1),u1_struct_0(sK0)) )).

cnf(u29,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK2) )).

cnf(u48,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_lattice3(sK0,X2,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattice3(sK0,X2,X0) )).

cnf(u34,axiom,
    ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u46,negated_conjecture,
    ( r1_lattice3(sK0,X1,sK2)
    | m1_subset_1(sK3(sK0,X1,sK2),u1_struct_0(sK0)) )).

cnf(u45,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u52,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0)) )).

cnf(u43,negated_conjecture,
    ( ~ r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(sK3(sK0,X2,sK1),u1_struct_0(X0))
    | r1_orders_2(X0,X1,sK3(sK0,X2,sK1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(sK0,X2,sK1) )).

cnf(u44,negated_conjecture,
    ( ~ r1_lattice3(X3,X5,X4)
    | ~ m1_subset_1(sK3(sK0,X5,sK2),u1_struct_0(X3))
    | r1_orders_2(X3,X4,sK3(sK0,X5,sK2))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X3)
    | r1_lattice3(sK0,X5,sK2) )).

cnf(u64,negated_conjecture,
    ( ~ r1_lattice3(sK0,X1,sK3(sK0,X0,sK2))
    | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,sK2)
    | r1_lattice3(sK0,X1,sK1) )).

cnf(u51,negated_conjecture,
    ( ~ r1_lattice3(sK0,X0,sK2)
    | r1_lattice3(sK0,X0,sK1) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | r2_hidden(sK3(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2) )).

cnf(u41,negated_conjecture,
    ( r2_hidden(sK3(sK0,X1,sK2),X1)
    | r1_lattice3(sK0,X1,sK2) )).

cnf(u40,negated_conjecture,
    ( r2_hidden(sK3(sK0,X0,sK1),X0)
    | r1_lattice3(sK0,X0,sK1) )).

cnf(u31,axiom,
    ( ~ r2_hidden(X4,X1)
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u39,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,X0,X1),X0)
    | r1_lattice3(sK0,X0,X1) )).

cnf(u42,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:31:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (16420)WARNING: option uwaf not known.
% 0.22/0.46  % (16430)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.47  % (16430)# SZS output start Saturation.
% 0.22/0.47  cnf(u25,negated_conjecture,
% 0.22/0.47      v4_orders_2(sK0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u35,axiom,
% 0.22/0.47      ~v4_orders_2(X0) | ~r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X3)).
% 0.22/0.47  
% 0.22/0.47  cnf(u61,negated_conjecture,
% 0.22/0.47      r1_orders_2(sK0,sK1,sK3(sK0,X1,sK2)) | r1_lattice3(sK0,X1,sK2) | m1_subset_1(sK3(sK0,X1,sK1),u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u29,negated_conjecture,
% 0.22/0.47      r1_orders_2(sK0,sK1,sK2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u48,negated_conjecture,
% 0.22/0.47      ~r1_orders_2(sK0,X0,X1) | ~r1_lattice3(sK0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X2,X0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u34,axiom,
% 0.22/0.47      ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u46,negated_conjecture,
% 0.22/0.47      r1_lattice3(sK0,X1,sK2) | m1_subset_1(sK3(sK0,X1,sK2),u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u45,negated_conjecture,
% 0.22/0.47      r1_lattice3(sK0,X0,sK1) | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u52,negated_conjecture,
% 0.22/0.47      r1_lattice3(sK0,X0,sK1) | m1_subset_1(sK3(sK0,X0,sK2),u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u43,negated_conjecture,
% 0.22/0.47      ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(sK3(sK0,X2,sK1),u1_struct_0(X0)) | r1_orders_2(X0,X1,sK3(sK0,X2,sK1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(sK0,X2,sK1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u44,negated_conjecture,
% 0.22/0.47      ~r1_lattice3(X3,X5,X4) | ~m1_subset_1(sK3(sK0,X5,sK2),u1_struct_0(X3)) | r1_orders_2(X3,X4,sK3(sK0,X5,sK2)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | r1_lattice3(sK0,X5,sK2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u64,negated_conjecture,
% 0.22/0.47      ~r1_lattice3(sK0,X1,sK3(sK0,X0,sK2)) | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK2) | r1_lattice3(sK0,X1,sK1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u51,negated_conjecture,
% 0.22/0.47      ~r1_lattice3(sK0,X0,sK2) | r1_lattice3(sK0,X0,sK1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u26,negated_conjecture,
% 0.22/0.47      l1_orders_2(sK0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u33,axiom,
% 0.22/0.47      ~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u32,axiom,
% 0.22/0.47      ~l1_orders_2(X0) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u41,negated_conjecture,
% 0.22/0.47      r2_hidden(sK3(sK0,X1,sK2),X1) | r1_lattice3(sK0,X1,sK2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u40,negated_conjecture,
% 0.22/0.47      r2_hidden(sK3(sK0,X0,sK1),X0) | r1_lattice3(sK0,X0,sK1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u31,axiom,
% 0.22/0.47      ~r2_hidden(X4,X1) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u28,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u27,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u39,negated_conjecture,
% 0.22/0.47      ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,X0,X1),X0) | r1_lattice3(sK0,X0,X1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u42,negated_conjecture,
% 0.22/0.47      ~m1_subset_1(X1,u1_struct_0(sK0)) | m1_subset_1(sK3(sK0,X0,X1),u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)).
% 0.22/0.47  
% 0.22/0.47  % (16430)# SZS output end Saturation.
% 0.22/0.47  % (16430)------------------------------
% 0.22/0.47  % (16430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (16430)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (16430)Memory used [KB]: 5373
% 0.22/0.47  % (16430)Time elapsed: 0.045 s
% 0.22/0.47  % (16430)------------------------------
% 0.22/0.47  % (16430)------------------------------
% 0.22/0.47  % (16409)Success in time 0.097 s
%------------------------------------------------------------------------------
