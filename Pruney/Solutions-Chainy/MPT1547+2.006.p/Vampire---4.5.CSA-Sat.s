%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:02 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u20,negated_conjecture,
    ( v2_lattice3(sK0) )).

cnf(u22,axiom,
    ( ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) )).

cnf(u57,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK2)
    | sK1 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u35,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u32,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2) )).

cnf(u24,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | r3_orders_2(X0,X1,X2) )).

cnf(u47,negated_conjecture,
    ( r3_orders_2(sK0,sK1,sK1) )).

cnf(u43,negated_conjecture,
    ( r3_orders_2(sK0,sK2,sK2) )).

cnf(u14,negated_conjecture,
    ( r3_orders_2(sK0,sK1,sK2)
    | sK1 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u25,axiom,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2)
    | v2_struct_0(X0) )).

cnf(u17,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u16,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | r1_orders_2(X0,X1,X1) )).

cnf(u21,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u18,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u27,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u15,negated_conjecture,
    ( sK1 != k12_lattice3(sK0,sK1,sK2)
    | ~ r3_orders_2(sK0,sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (32672)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.45  % (32685)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.46  % (32686)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.46  % (32679)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % (32680)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.46  % (32680)# SZS output start Saturation.
% 0.20/0.46  cnf(u19,negated_conjecture,
% 0.20/0.46      v5_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u20,negated_conjecture,
% 0.20/0.46      v2_lattice3(sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u22,axiom,
% 0.20/0.46      ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u57,negated_conjecture,
% 0.20/0.46      r1_orders_2(sK0,sK1,sK2) | sK1 = k12_lattice3(sK0,sK1,sK2)).
% 0.20/0.46  
% 0.20/0.46  cnf(u35,negated_conjecture,
% 0.20/0.46      r1_orders_2(sK0,sK1,sK1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u32,negated_conjecture,
% 0.20/0.46      r1_orders_2(sK0,sK2,sK2)).
% 0.20/0.46  
% 0.20/0.46  cnf(u24,axiom,
% 0.20/0.46      ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)).
% 0.20/0.46  
% 0.20/0.46  cnf(u47,negated_conjecture,
% 0.20/0.46      r3_orders_2(sK0,sK1,sK1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u43,negated_conjecture,
% 0.20/0.46      r3_orders_2(sK0,sK2,sK2)).
% 0.20/0.46  
% 0.20/0.46  cnf(u14,negated_conjecture,
% 0.20/0.46      r3_orders_2(sK0,sK1,sK2) | sK1 = k12_lattice3(sK0,sK1,sK2)).
% 0.20/0.46  
% 0.20/0.46  cnf(u25,axiom,
% 0.20/0.46      ~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u17,negated_conjecture,
% 0.20/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u16,negated_conjecture,
% 0.20/0.46      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.46  
% 0.20/0.46  cnf(u23,axiom,
% 0.20/0.46      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1)).
% 0.20/0.46  
% 0.20/0.46  cnf(u21,negated_conjecture,
% 0.20/0.46      l1_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u18,negated_conjecture,
% 0.20/0.46      v3_orders_2(sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u27,negated_conjecture,
% 0.20/0.46      ~v2_struct_0(sK0)).
% 0.20/0.46  
% 0.20/0.46  cnf(u15,negated_conjecture,
% 0.20/0.46      sK1 != k12_lattice3(sK0,sK1,sK2) | ~r3_orders_2(sK0,sK1,sK2)).
% 0.20/0.46  
% 0.20/0.46  % (32680)# SZS output end Saturation.
% 0.20/0.46  % (32680)------------------------------
% 0.20/0.46  % (32680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (32680)Termination reason: Satisfiable
% 0.20/0.46  
% 0.20/0.46  % (32680)Memory used [KB]: 6140
% 0.20/0.46  % (32680)Time elapsed: 0.057 s
% 0.20/0.46  % (32680)------------------------------
% 0.20/0.46  % (32680)------------------------------
% 0.20/0.46  % (32666)Success in time 0.108 s
%------------------------------------------------------------------------------
