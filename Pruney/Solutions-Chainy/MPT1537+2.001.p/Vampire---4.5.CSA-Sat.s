%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:58 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u15,negated_conjecture,
    ( r2_lattice3(sK0,sK1,sK2)
    | r1_yellow_0(sK0,sK1) )).

cnf(u10,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,X3)
    | r1_yellow_0(sK0,sK1) )).

cnf(u11,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | m1_subset_1(sK3(X2),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1) )).

cnf(u12,negated_conjecture,
    ( ~ r2_lattice3(sK0,sK1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | r2_lattice3(sK0,sK1,sK3(X2))
    | ~ r1_yellow_0(sK0,sK1) )).

cnf(u16,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u26,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2)
    | r1_yellow_0(sK0,sK1) )).

cnf(u21,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_orders_2(X0,X2,X1) )).

cnf(u20,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2
    | r2_orders_2(X0,X1,X2) )).

cnf(u13,negated_conjecture,
    ( ~ r1_orders_2(sK0,X2,sK3(X2))
    | ~ r2_lattice3(sK0,sK1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1) )).

cnf(u18,axiom,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u23,axiom,
    ( ~ r2_orders_2(X0,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK1) )).

cnf(u17,negated_conjecture,
    ( l1_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (6375)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (6375)Refutation not found, incomplete strategy% (6375)------------------------------
% 0.21/0.49  % (6375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6376)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (6375)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6375)Memory used [KB]: 1663
% 0.21/0.49  % (6375)Time elapsed: 0.054 s
% 0.21/0.49  % (6375)------------------------------
% 0.21/0.49  % (6375)------------------------------
% 0.21/0.49  % (6376)Refutation not found, incomplete strategy% (6376)------------------------------
% 0.21/0.49  % (6376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6376)Memory used [KB]: 6140
% 0.21/0.49  % (6376)Time elapsed: 0.071 s
% 0.21/0.49  % (6376)------------------------------
% 0.21/0.49  % (6376)------------------------------
% 0.21/0.50  % (6384)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (6384)Refutation not found, incomplete strategy% (6384)------------------------------
% 0.21/0.50  % (6384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (6384)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (6384)Memory used [KB]: 1535
% 0.21/0.50  % (6384)Time elapsed: 0.061 s
% 0.21/0.50  % (6384)------------------------------
% 0.21/0.50  % (6384)------------------------------
% 0.21/0.50  % (6373)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (6373)Refutation not found, incomplete strategy% (6373)------------------------------
% 0.21/0.51  % (6373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6373)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6373)Memory used [KB]: 10618
% 0.21/0.51  % (6373)Time elapsed: 0.063 s
% 0.21/0.51  % (6373)------------------------------
% 0.21/0.51  % (6373)------------------------------
% 0.21/0.51  % (6371)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (6371)Refutation not found, incomplete strategy% (6371)------------------------------
% 0.21/0.51  % (6371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6371)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6371)Memory used [KB]: 6140
% 0.21/0.51  % (6371)Time elapsed: 0.085 s
% 0.21/0.51  % (6371)------------------------------
% 0.21/0.51  % (6371)------------------------------
% 0.21/0.52  % (6390)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (6381)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (6381)Refutation not found, incomplete strategy% (6381)------------------------------
% 0.21/0.52  % (6381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6381)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6381)Memory used [KB]: 6140
% 0.21/0.52  % (6381)Time elapsed: 0.081 s
% 0.21/0.52  % (6381)------------------------------
% 0.21/0.52  % (6381)------------------------------
% 0.21/0.52  % (6390)Refutation not found, incomplete strategy% (6390)------------------------------
% 0.21/0.52  % (6390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6390)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6390)Memory used [KB]: 6140
% 0.21/0.52  % (6390)Time elapsed: 0.075 s
% 0.21/0.52  % (6390)------------------------------
% 0.21/0.52  % (6390)------------------------------
% 0.21/0.52  % (6389)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (6389)Refutation not found, incomplete strategy% (6389)------------------------------
% 0.21/0.52  % (6389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6389)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6389)Memory used [KB]: 1663
% 0.21/0.52  % (6389)Time elapsed: 0.082 s
% 0.21/0.52  % (6389)------------------------------
% 0.21/0.52  % (6389)------------------------------
% 0.21/0.52  % (6385)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.53  % (6385)Refutation not found, incomplete strategy% (6385)------------------------------
% 0.21/0.53  % (6385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6385)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6385)Memory used [KB]: 10618
% 0.21/0.53  % (6385)Time elapsed: 0.093 s
% 0.21/0.53  % (6385)------------------------------
% 0.21/0.53  % (6385)------------------------------
% 0.21/0.53  % (6377)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  % (6391)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (6379)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (6391)Refutation not found, incomplete strategy% (6391)------------------------------
% 0.21/0.53  % (6391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6391)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6391)Memory used [KB]: 10490
% 0.21/0.53  % (6391)Time elapsed: 0.098 s
% 0.21/0.53  % (6391)------------------------------
% 0.21/0.53  % (6391)------------------------------
% 0.21/0.53  % (6388)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (6388)# SZS output start Saturation.
% 0.21/0.54  cnf(u15,negated_conjecture,
% 0.21/0.54      r2_lattice3(sK0,sK1,sK2) | r1_yellow_0(sK0,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u10,negated_conjecture,
% 0.21/0.54      ~r2_lattice3(sK0,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,X3) | r1_yellow_0(sK0,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u11,negated_conjecture,
% 0.21/0.54      ~r2_lattice3(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u12,negated_conjecture,
% 0.21/0.54      ~r2_lattice3(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_lattice3(sK0,sK1,sK3(X2)) | ~r1_yellow_0(sK0,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u16,negated_conjecture,
% 0.21/0.54      v5_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u26,negated_conjecture,
% 0.21/0.54      r1_orders_2(sK0,sK2,sK2) | r1_yellow_0(sK0,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u21,axiom,
% 0.21/0.54      ~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_orders_2(X0,X2,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u20,axiom,
% 0.21/0.54      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2 | r2_orders_2(X0,X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u13,negated_conjecture,
% 0.21/0.54      ~r1_orders_2(sK0,X2,sK3(X2)) | ~r2_lattice3(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u18,axiom,
% 0.21/0.54      ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u23,axiom,
% 0.21/0.54      ~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u14,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK2,u1_struct_0(sK0)) | r1_yellow_0(sK0,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u17,negated_conjecture,
% 0.21/0.54      l1_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  % (6388)# SZS output end Saturation.
% 0.21/0.54  % (6388)------------------------------
% 0.21/0.54  % (6388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6388)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (6388)Memory used [KB]: 1663
% 0.21/0.54  % (6388)Time elapsed: 0.099 s
% 0.21/0.54  % (6388)------------------------------
% 0.21/0.54  % (6388)------------------------------
% 0.21/0.54  % (6370)Success in time 0.176 s
%------------------------------------------------------------------------------
