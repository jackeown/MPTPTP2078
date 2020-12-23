%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:59 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   69 (  69 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u32,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK3)
    | sK3 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u17,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK2)
    | sK3 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u16,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK1)
    | sK3 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u11,negated_conjecture,
    ( ~ r1_orders_2(sK0,X4,sK2)
    | ~ r1_orders_2(sK0,X4,sK1)
    | ~ m1_subset_1(X4,u1_struct_0(sK0))
    | r1_orders_2(sK0,X4,sK3)
    | sK3 = k12_lattice3(sK0,sK1,sK2) )).

cnf(u15,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK4,sK3)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | sK3 != k12_lattice3(sK0,sK1,sK2) )).

cnf(u12,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | sK3 != k12_lattice3(sK0,sK1,sK2) )).

cnf(u13,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK4,sK1)
    | sK3 != k12_lattice3(sK0,sK1,sK2) )).

cnf(u14,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK4,sK2)
    | sK3 != k12_lattice3(sK0,sK1,sK2) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u38,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k11_lattice3(sK0,sK3,X0) = k11_lattice3(sK0,X0,sK3) )).

cnf(u41,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k11_lattice3(sK0,sK2,X1) = k11_lattice3(sK0,X1,sK2) )).

cnf(u44,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k11_lattice3(sK0,sK1,X2) = k11_lattice3(sK0,X2,sK1) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k11_lattice3(sK0,sK3,X0) = k12_lattice3(sK0,sK3,X0) )).

cnf(u53,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k11_lattice3(sK0,sK2,X1) = k12_lattice3(sK0,sK2,X1) )).

cnf(u56,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | k11_lattice3(sK0,sK1,X2) = k12_lattice3(sK0,sK1,X2) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u22,negated_conjecture,
    ( v2_lattice3(sK0) )).

cnf(u21,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u83,negated_conjecture,
    ( k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1) )).

cnf(u78,negated_conjecture,
    ( k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK1,sK2) )).

cnf(u82,negated_conjecture,
    ( k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1) )).

cnf(u80,negated_conjecture,
    ( k12_lattice3(sK0,sK3,sK1) = k12_lattice3(sK0,sK1,sK3) )).

cnf(u74,negated_conjecture,
    ( k12_lattice3(sK0,sK3,sK2) = k12_lattice3(sK0,sK2,sK3) )).

cnf(u81,negated_conjecture,
    ( k11_lattice3(sK0,sK3,sK1) = k12_lattice3(sK0,sK1,sK3) )).

cnf(u79,negated_conjecture,
    ( k11_lattice3(sK0,sK1,sK1) = k12_lattice3(sK0,sK1,sK1) )).

cnf(u75,negated_conjecture,
    ( k11_lattice3(sK0,sK3,sK2) = k12_lattice3(sK0,sK2,sK3) )).

cnf(u72,negated_conjecture,
    ( k11_lattice3(sK0,sK2,sK2) = k12_lattice3(sK0,sK2,sK2) )).

cnf(u77,negated_conjecture,
    ( k11_lattice3(sK0,sK1,sK3) = k12_lattice3(sK0,sK1,sK3) )).

cnf(u71,negated_conjecture,
    ( k11_lattice3(sK0,sK2,sK3) = k12_lattice3(sK0,sK2,sK3) )).

cnf(u66,negated_conjecture,
    ( k11_lattice3(sK0,sK3,sK3) = k12_lattice3(sK0,sK3,sK3) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (30831)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.42  % (30831)Refutation not found, incomplete strategy% (30831)------------------------------
% 0.21/0.42  % (30831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (30831)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (30831)Memory used [KB]: 6268
% 0.21/0.42  % (30831)Time elapsed: 0.007 s
% 0.21/0.42  % (30831)------------------------------
% 0.21/0.42  % (30831)------------------------------
% 0.21/0.44  % (30825)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.44  % (30825)Refutation not found, incomplete strategy% (30825)------------------------------
% 0.21/0.44  % (30825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (30825)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (30825)Memory used [KB]: 1663
% 0.21/0.44  % (30825)Time elapsed: 0.045 s
% 0.21/0.44  % (30825)------------------------------
% 0.21/0.44  % (30825)------------------------------
% 0.21/0.45  % (30838)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.45  % (30838)# SZS output start Saturation.
% 0.21/0.45  cnf(u32,negated_conjecture,
% 0.21/0.45      r1_orders_2(sK0,sK3,sK3) | sK3 = k12_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u17,negated_conjecture,
% 0.21/0.45      r1_orders_2(sK0,sK3,sK2) | sK3 = k12_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u16,negated_conjecture,
% 0.21/0.45      r1_orders_2(sK0,sK3,sK1) | sK3 = k12_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u11,negated_conjecture,
% 0.21/0.45      ~r1_orders_2(sK0,X4,sK2) | ~r1_orders_2(sK0,X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_orders_2(sK0,X4,sK3) | sK3 = k12_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u15,negated_conjecture,
% 0.21/0.45      ~r1_orders_2(sK0,sK4,sK3) | ~r1_orders_2(sK0,sK3,sK2) | ~r1_orders_2(sK0,sK3,sK1) | sK3 != k12_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u12,negated_conjecture,
% 0.21/0.45      ~r1_orders_2(sK0,sK3,sK2) | ~r1_orders_2(sK0,sK3,sK1) | m1_subset_1(sK4,u1_struct_0(sK0)) | sK3 != k12_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u13,negated_conjecture,
% 0.21/0.45      ~r1_orders_2(sK0,sK3,sK2) | ~r1_orders_2(sK0,sK3,sK1) | r1_orders_2(sK0,sK4,sK1) | sK3 != k12_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u14,negated_conjecture,
% 0.21/0.45      ~r1_orders_2(sK0,sK3,sK2) | ~r1_orders_2(sK0,sK3,sK1) | r1_orders_2(sK0,sK4,sK2) | sK3 != k12_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u20,negated_conjecture,
% 0.21/0.45      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.45  
% 0.21/0.45  cnf(u19,negated_conjecture,
% 0.21/0.45      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.45  
% 0.21/0.45  cnf(u18,negated_conjecture,
% 0.21/0.45      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.45  
% 0.21/0.45  cnf(u38,negated_conjecture,
% 0.21/0.45      ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,sK3,X0) = k11_lattice3(sK0,X0,sK3)).
% 0.21/0.45  
% 0.21/0.45  cnf(u41,negated_conjecture,
% 0.21/0.45      ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,sK2,X1) = k11_lattice3(sK0,X1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u44,negated_conjecture,
% 0.21/0.45      ~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,X2) = k11_lattice3(sK0,X2,sK1)).
% 0.21/0.45  
% 0.21/0.45  cnf(u50,negated_conjecture,
% 0.21/0.45      ~m1_subset_1(X0,u1_struct_0(sK0)) | k11_lattice3(sK0,sK3,X0) = k12_lattice3(sK0,sK3,X0)).
% 0.21/0.45  
% 0.21/0.45  cnf(u53,negated_conjecture,
% 0.21/0.45      ~m1_subset_1(X1,u1_struct_0(sK0)) | k11_lattice3(sK0,sK2,X1) = k12_lattice3(sK0,sK2,X1)).
% 0.21/0.45  
% 0.21/0.45  cnf(u56,negated_conjecture,
% 0.21/0.45      ~m1_subset_1(X2,u1_struct_0(sK0)) | k11_lattice3(sK0,sK1,X2) = k12_lattice3(sK0,sK1,X2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u24,axiom,
% 0.21/0.45      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)).
% 0.21/0.45  
% 0.21/0.45  cnf(u25,axiom,
% 0.21/0.45      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u23,negated_conjecture,
% 0.21/0.45      l1_orders_2(sK0)).
% 0.21/0.45  
% 0.21/0.45  cnf(u22,negated_conjecture,
% 0.21/0.45      v2_lattice3(sK0)).
% 0.21/0.45  
% 0.21/0.45  cnf(u21,negated_conjecture,
% 0.21/0.45      v5_orders_2(sK0)).
% 0.21/0.45  
% 0.21/0.45  cnf(u83,negated_conjecture,
% 0.21/0.45      k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK2,sK1)).
% 0.21/0.45  
% 0.21/0.45  cnf(u78,negated_conjecture,
% 0.21/0.45      k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK1,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u82,negated_conjecture,
% 0.21/0.45      k12_lattice3(sK0,sK1,sK2) = k12_lattice3(sK0,sK2,sK1)).
% 0.21/0.45  
% 0.21/0.45  cnf(u80,negated_conjecture,
% 0.21/0.45      k12_lattice3(sK0,sK3,sK1) = k12_lattice3(sK0,sK1,sK3)).
% 0.21/0.45  
% 0.21/0.45  cnf(u74,negated_conjecture,
% 0.21/0.45      k12_lattice3(sK0,sK3,sK2) = k12_lattice3(sK0,sK2,sK3)).
% 0.21/0.45  
% 0.21/0.45  cnf(u81,negated_conjecture,
% 0.21/0.45      k11_lattice3(sK0,sK3,sK1) = k12_lattice3(sK0,sK1,sK3)).
% 0.21/0.45  
% 0.21/0.45  cnf(u79,negated_conjecture,
% 0.21/0.45      k11_lattice3(sK0,sK1,sK1) = k12_lattice3(sK0,sK1,sK1)).
% 0.21/0.45  
% 0.21/0.45  cnf(u75,negated_conjecture,
% 0.21/0.45      k11_lattice3(sK0,sK3,sK2) = k12_lattice3(sK0,sK2,sK3)).
% 0.21/0.45  
% 0.21/0.45  cnf(u72,negated_conjecture,
% 0.21/0.45      k11_lattice3(sK0,sK2,sK2) = k12_lattice3(sK0,sK2,sK2)).
% 0.21/0.45  
% 0.21/0.45  cnf(u77,negated_conjecture,
% 0.21/0.45      k11_lattice3(sK0,sK1,sK3) = k12_lattice3(sK0,sK1,sK3)).
% 0.21/0.45  
% 0.21/0.45  cnf(u71,negated_conjecture,
% 0.21/0.45      k11_lattice3(sK0,sK2,sK3) = k12_lattice3(sK0,sK2,sK3)).
% 0.21/0.45  
% 0.21/0.45  cnf(u66,negated_conjecture,
% 0.21/0.45      k11_lattice3(sK0,sK3,sK3) = k12_lattice3(sK0,sK3,sK3)).
% 0.21/0.45  
% 0.21/0.45  % (30838)# SZS output end Saturation.
% 0.21/0.45  % (30838)------------------------------
% 0.21/0.45  % (30838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (30838)Termination reason: Satisfiable
% 0.21/0.45  
% 0.21/0.45  % (30838)Memory used [KB]: 1663
% 0.21/0.45  % (30838)Time elapsed: 0.056 s
% 0.21/0.45  % (30838)------------------------------
% 0.21/0.45  % (30838)------------------------------
% 0.21/0.46  % (30820)Success in time 0.097 s
%------------------------------------------------------------------------------
