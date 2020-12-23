%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:18 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u13,negated_conjecture,
    ( r1_yellow_0(sK0,sK1) )).

cnf(u14,negated_conjecture,
    ( ~ r1_yellow_0(sK0,sK2) )).

cnf(u12,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK2,X3)
    | r2_lattice3(sK0,sK1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0)) )).

cnf(u11,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK1,X3)
    | r2_lattice3(sK0,sK2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0)) )).

cnf(u10,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u9,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:33:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (26641)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.45  % (26641)Refutation not found, incomplete strategy% (26641)------------------------------
% 0.21/0.45  % (26641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (26652)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (26652)# SZS output start Saturation.
% 0.21/0.46  cnf(u13,negated_conjecture,
% 0.21/0.46      r1_yellow_0(sK0,sK1)).
% 0.21/0.46  
% 0.21/0.46  cnf(u14,negated_conjecture,
% 0.21/0.46      ~r1_yellow_0(sK0,sK2)).
% 0.21/0.46  
% 0.21/0.46  cnf(u12,negated_conjecture,
% 0.21/0.46      ~r2_lattice3(sK0,sK2,X3) | r2_lattice3(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  cnf(u11,negated_conjecture,
% 0.21/0.46      ~r2_lattice3(sK0,sK1,X3) | r2_lattice3(sK0,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  cnf(u10,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u9,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  % (26652)# SZS output end Saturation.
% 0.21/0.46  % (26652)------------------------------
% 0.21/0.46  % (26652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (26652)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (26652)Memory used [KB]: 5245
% 0.21/0.46  % (26652)Time elapsed: 0.004 s
% 0.21/0.46  % (26652)------------------------------
% 0.21/0.46  % (26652)------------------------------
% 0.21/0.46  % (26641)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (26641)Memory used [KB]: 9722
% 0.21/0.46  % (26641)Time elapsed: 0.065 s
% 0.21/0.46  % (26641)------------------------------
% 0.21/0.46  % (26641)------------------------------
% 0.21/0.47  % (26637)Success in time 0.106 s
%------------------------------------------------------------------------------
