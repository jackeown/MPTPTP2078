%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:59 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   35 (  35 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u18,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u17,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u35,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u32,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2) )).

cnf(u25,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_orders_2(X0,X2,X1) )).

cnf(u23,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2
    | r2_orders_2(X0,X1,X2) )).

cnf(u21,axiom,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u27,axiom,
    ( ~ r2_orders_2(X0,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u16,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u13,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | r1_orders_2(X0,X1,X1) )).

cnf(u20,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u14,negated_conjecture,
    ( k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2) )).

cnf(u15,negated_conjecture,
    ( sK1 != sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (15983)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (15975)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (15983)Refutation not found, incomplete strategy% (15983)------------------------------
% 0.20/0.48  % (15983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15983)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (15983)Memory used [KB]: 6140
% 0.20/0.48  % (15983)Time elapsed: 0.008 s
% 0.20/0.48  % (15983)------------------------------
% 0.20/0.48  % (15983)------------------------------
% 0.20/0.48  % (15984)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (15974)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (15977)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (15974)Refutation not found, incomplete strategy% (15974)------------------------------
% 0.20/0.49  % (15974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15974)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (15974)Memory used [KB]: 10618
% 0.20/0.49  % (15974)Time elapsed: 0.070 s
% 0.20/0.49  % (15974)------------------------------
% 0.20/0.49  % (15974)------------------------------
% 0.20/0.49  % (15984)Refutation not found, incomplete strategy% (15984)------------------------------
% 0.20/0.49  % (15984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15987)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (15977)Refutation not found, incomplete strategy% (15977)------------------------------
% 0.20/0.50  % (15977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15984)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15984)Memory used [KB]: 10746
% 0.20/0.50  % (15984)Time elapsed: 0.072 s
% 0.20/0.50  % (15984)------------------------------
% 0.20/0.50  % (15984)------------------------------
% 0.20/0.50  % (15980)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (15977)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15977)Memory used [KB]: 10618
% 0.20/0.50  % (15977)Time elapsed: 0.078 s
% 0.20/0.50  % (15977)------------------------------
% 0.20/0.50  % (15977)------------------------------
% 0.20/0.50  % (15971)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (15980)Refutation not found, incomplete strategy% (15980)------------------------------
% 0.20/0.50  % (15980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15969)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (15980)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15980)Memory used [KB]: 6140
% 0.20/0.50  % (15980)Time elapsed: 0.076 s
% 0.20/0.50  % (15980)------------------------------
% 0.20/0.50  % (15980)------------------------------
% 0.20/0.50  % (15971)Refutation not found, incomplete strategy% (15971)------------------------------
% 0.20/0.50  % (15971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15971)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15971)Memory used [KB]: 10618
% 0.20/0.50  % (15971)Time elapsed: 0.078 s
% 0.20/0.50  % (15971)------------------------------
% 0.20/0.50  % (15971)------------------------------
% 0.20/0.51  % (15973)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (15986)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (15986)Refutation not found, incomplete strategy% (15986)------------------------------
% 0.20/0.51  % (15986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15986)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (15986)Memory used [KB]: 1663
% 0.20/0.51  % (15986)Time elapsed: 0.088 s
% 0.20/0.51  % (15986)------------------------------
% 0.20/0.51  % (15986)------------------------------
% 0.20/0.51  % (15968)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (15987)Refutation not found, incomplete strategy% (15987)------------------------------
% 0.20/0.51  % (15987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15987)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (15987)Memory used [KB]: 6140
% 0.20/0.51  % (15987)Time elapsed: 0.081 s
% 0.20/0.51  % (15987)------------------------------
% 0.20/0.51  % (15987)------------------------------
% 0.20/0.51  % (15982)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.52  % (15972)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  % (15969)Refutation not found, incomplete strategy% (15969)------------------------------
% 0.20/0.52  % (15969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15969)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (15969)Memory used [KB]: 10490
% 0.20/0.52  % (15969)Time elapsed: 0.098 s
% 0.20/0.52  % (15969)------------------------------
% 0.20/0.52  % (15969)------------------------------
% 0.20/0.52  % (15972)Refutation not found, incomplete strategy% (15972)------------------------------
% 0.20/0.52  % (15972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15972)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (15972)Memory used [KB]: 1663
% 0.20/0.52  % (15972)Time elapsed: 0.097 s
% 0.20/0.52  % (15972)------------------------------
% 0.20/0.52  % (15972)------------------------------
% 0.20/0.52  % (15968)Refutation not found, incomplete strategy% (15968)------------------------------
% 0.20/0.52  % (15968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15968)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (15968)Memory used [KB]: 6140
% 0.20/0.52  % (15968)Time elapsed: 0.087 s
% 0.20/0.52  % (15968)------------------------------
% 0.20/0.52  % (15968)------------------------------
% 0.20/0.52  % (15988)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (15979)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.53  % (15970)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.53  % (15979)Refutation not found, incomplete strategy% (15979)------------------------------
% 0.20/0.53  % (15979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15979)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15979)Memory used [KB]: 10618
% 0.20/0.53  % (15979)Time elapsed: 0.103 s
% 0.20/0.53  % (15979)------------------------------
% 0.20/0.53  % (15979)------------------------------
% 0.20/0.53  % (15976)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.53  % (15970)Refutation not found, incomplete strategy% (15970)------------------------------
% 0.20/0.53  % (15970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15970)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15970)Memory used [KB]: 10618
% 0.20/0.53  % (15970)Time elapsed: 0.106 s
% 0.20/0.53  % (15970)------------------------------
% 0.20/0.53  % (15970)------------------------------
% 0.20/0.53  % (15985)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (15985)# SZS output start Saturation.
% 0.20/0.53  cnf(u19,negated_conjecture,
% 0.20/0.53      v5_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u18,negated_conjecture,
% 0.20/0.53      v3_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u17,negated_conjecture,
% 0.20/0.53      ~v2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u35,negated_conjecture,
% 0.20/0.53      r1_orders_2(sK0,sK1,sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u32,negated_conjecture,
% 0.20/0.53      r1_orders_2(sK0,sK2,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u25,axiom,
% 0.20/0.53      ~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_orders_2(X0,X2,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u23,axiom,
% 0.20/0.53      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2 | r2_orders_2(X0,X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u21,axiom,
% 0.20/0.53      ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u27,axiom,
% 0.20/0.53      ~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u16,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u13,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u24,axiom,
% 0.20/0.53      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u20,negated_conjecture,
% 0.20/0.53      l1_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u14,negated_conjecture,
% 0.20/0.53      k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u15,negated_conjecture,
% 0.20/0.53      sK1 != sK2).
% 0.20/0.53  
% 0.20/0.53  % (15985)# SZS output end Saturation.
% 0.20/0.53  % (15985)------------------------------
% 0.20/0.53  % (15985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15985)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (15985)Memory used [KB]: 1663
% 0.20/0.53  % (15985)Time elapsed: 0.107 s
% 0.20/0.53  % (15985)------------------------------
% 0.20/0.53  % (15985)------------------------------
% 0.20/0.53  % (15967)Success in time 0.174 s
%------------------------------------------------------------------------------
