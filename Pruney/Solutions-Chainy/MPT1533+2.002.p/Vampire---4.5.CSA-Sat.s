%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:58 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :    7 (   7 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u14,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3) )).

cnf(u13,negated_conjecture,
    ( r2_lattice3(sK0,sK1,sK2) )).

cnf(u15,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK1,sK3) )).

cnf(u12,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u11,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u10,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u9,negated_conjecture,
    ( v4_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (26108)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.49  % (26119)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (26111)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.50  % (26116)WARNING: option uwaf not known.
% 0.21/0.50  % (26116)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.50  % (26116)Refutation not found, incomplete strategy% (26116)------------------------------
% 0.21/0.50  % (26116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26116)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26116)Memory used [KB]: 767
% 0.21/0.50  % (26116)Time elapsed: 0.073 s
% 0.21/0.50  % (26116)------------------------------
% 0.21/0.50  % (26116)------------------------------
% 0.21/0.51  % (26106)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (26106)Refutation not found, incomplete strategy% (26106)------------------------------
% 0.21/0.51  % (26106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26106)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26106)Memory used [KB]: 5245
% 0.21/0.51  % (26106)Time elapsed: 0.075 s
% 0.21/0.51  % (26106)------------------------------
% 0.21/0.51  % (26106)------------------------------
% 0.21/0.51  % (26111)Refutation not found, incomplete strategy% (26111)------------------------------
% 0.21/0.51  % (26111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26111)Memory used [KB]: 767
% 0.21/0.51  % (26111)Time elapsed: 0.084 s
% 0.21/0.51  % (26111)------------------------------
% 0.21/0.51  % (26111)------------------------------
% 0.21/0.51  % (26120)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.51  % (26110)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (26120)# SZS output start Saturation.
% 0.21/0.52  cnf(u14,negated_conjecture,
% 0.21/0.52      r1_orders_2(sK0,sK2,sK3)).
% 0.21/0.52  
% 0.21/0.52  cnf(u13,negated_conjecture,
% 0.21/0.52      r2_lattice3(sK0,sK1,sK2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u15,negated_conjecture,
% 0.21/0.52      ~r2_lattice3(sK0,sK1,sK3)).
% 0.21/0.52  
% 0.21/0.52  cnf(u12,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u11,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u10,negated_conjecture,
% 0.21/0.52      l1_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u9,negated_conjecture,
% 0.21/0.52      v4_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  % (26120)# SZS output end Saturation.
% 0.21/0.52  % (26120)------------------------------
% 0.21/0.52  % (26120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26120)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (26120)Memory used [KB]: 5245
% 0.21/0.52  % (26120)Time elapsed: 0.083 s
% 0.21/0.52  % (26120)------------------------------
% 0.21/0.52  % (26120)------------------------------
% 0.21/0.52  % (26105)Success in time 0.152 s
%------------------------------------------------------------------------------
