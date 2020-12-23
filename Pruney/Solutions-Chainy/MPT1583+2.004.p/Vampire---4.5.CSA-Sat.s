%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:23 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   45 (  45 expanded)
%              Number of leaves         :   45 (  45 expanded)
%              Depth                    :    0
%              Number of atoms          :  147 ( 147 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) )).

cnf(u26,negated_conjecture,
    ( v4_yellow_0(sK1,sK0) )).

cnf(u20,negated_conjecture,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u35,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X3,X2)
    | ~ l1_orders_2(X0) )).

cnf(u45,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u47,negated_conjecture,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ r1_lattice3(sK1,sK2,sK3) )).

cnf(u85,negated_conjecture,
    ( r1_orders_2(sK0,sK6(X7,u1_struct_0(sK0),X8),sK3)
    | ~ r2_hidden(sK6(X7,u1_struct_0(sK0),X8),sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ l1_orders_2(X7)
    | r2_lattice3(X7,u1_struct_0(sK0),X8)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(X8,u1_struct_0(X7)) )).

cnf(u87,negated_conjecture,
    ( r1_orders_2(sK0,sK6(sK0,X2,X3),sK3)
    | ~ r2_hidden(sK6(sK0,X2,X3),sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X3,u1_struct_0(sK0))
    | r2_lattice3(sK0,X2,X3) )).

cnf(u84,negated_conjecture,
    ( r1_orders_2(sK0,sK5(X5,u1_struct_0(sK0),X6),sK3)
    | ~ r2_hidden(sK5(X5,u1_struct_0(sK0),X6),sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ l1_orders_2(X5)
    | r1_lattice3(X5,u1_struct_0(sK0),X6)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(X6,u1_struct_0(X5)) )).

cnf(u86,negated_conjecture,
    ( r1_orders_2(sK0,sK5(sK0,X0,X1),sK3)
    | ~ r2_hidden(sK5(sK0,X0,X1),sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_lattice3(sK0,X0,X1) )).

cnf(u80,negated_conjecture,
    ( r1_orders_2(sK0,sK3,sK3)
    | ~ r2_hidden(sK3,sK2)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u83,negated_conjecture,
    ( r1_orders_2(sK0,X4,sK3)
    | ~ r2_hidden(X4,sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ v1_xboole_0(X4)
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u38,axiom,
    ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u34,axiom,
    ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u31,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | r1_orders_2(X0,X2,X3)
    | ~ l1_orders_2(X0) )).

cnf(u48,negated_conjecture,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3) )).

cnf(u29,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u30,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u49,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u25,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u37,axiom,
    ( r2_hidden(sK6(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u33,axiom,
    ( r2_hidden(sK5(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u65,axiom,
    ( r2_hidden(sK6(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | r2_lattice3(X1,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1)) )).

cnf(u63,axiom,
    ( r2_hidden(sK5(X1,X2,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | r1_lattice3(X1,X2,X0)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1)) )).

cnf(u55,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u54,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u96,negated_conjecture,
    ( ~ r2_hidden(sK6(sK0,X0,sK3),sK2)
    | r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,X0,sK3) )).

cnf(u42,axiom,
    ( ~ r2_hidden(X1,X0)
    | v1_xboole_0(X0)
    | m1_subset_1(X1,X0) )).

cnf(u62,axiom,
    ( m1_subset_1(sK6(X1,X2,X0),X2)
    | ~ l1_orders_2(X1)
    | r2_lattice3(X1,X2,X0)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1)) )).

cnf(u61,axiom,
    ( m1_subset_1(sK5(X1,X2,X0),X2)
    | ~ l1_orders_2(X1)
    | r1_lattice3(X1,X2,X0)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X0,u1_struct_0(X1)) )).

cnf(u40,axiom,
    ( m1_subset_1(X1,X0)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) )).

cnf(u36,axiom,
    ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r2_lattice3(X0,X1,X2) )).

cnf(u32,axiom,
    ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_lattice3(X0,X1,X2) )).

cnf(u44,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u79,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_hidden(X0,sK2)
    | r1_orders_2(sK0,X0,sK3)
    | r1_lattice3(sK0,sK2,sK3) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X1,X0)
    | r2_hidden(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u66,axiom,
    ( v1_xboole_0(sK6(X4,X5,X3))
    | ~ l1_orders_2(X4)
    | r2_lattice3(X4,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_xboole_0(u1_struct_0(X4)) )).

cnf(u64,axiom,
    ( v1_xboole_0(sK5(X4,X5,X3))
    | ~ l1_orders_2(X4)
    | r1_lattice3(X4,X5,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ v1_xboole_0(u1_struct_0(X4)) )).

cnf(u51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(sK3) )).

cnf(u50,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK3) )).

cnf(u39,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u23,negated_conjecture,
    ( sK3 = sK4 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:42 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.47  % (11318)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.47  % (11323)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.47  % (11323)Refutation not found, incomplete strategy% (11323)------------------------------
% 0.22/0.47  % (11323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (11323)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (11323)Memory used [KB]: 1663
% 0.22/0.48  % (11323)Time elapsed: 0.057 s
% 0.22/0.48  % (11323)------------------------------
% 0.22/0.48  % (11323)------------------------------
% 0.22/0.49  % (11324)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.49  % (11309)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.49  % (11316)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (11319)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (11315)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (11311)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (11324)Refutation not found, incomplete strategy% (11324)------------------------------
% 0.22/0.51  % (11324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11324)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (11324)Memory used [KB]: 1663
% 0.22/0.51  % (11324)Time elapsed: 0.092 s
% 0.22/0.51  % (11324)------------------------------
% 0.22/0.51  % (11324)------------------------------
% 0.22/0.51  % (11307)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (11310)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (11310)Refutation not found, incomplete strategy% (11310)------------------------------
% 0.22/0.51  % (11310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (11310)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (11310)Memory used [KB]: 10618
% 0.22/0.51  % (11310)Time elapsed: 0.093 s
% 0.22/0.51  % (11310)------------------------------
% 0.22/0.51  % (11310)------------------------------
% 0.22/0.51  % (11325)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (11314)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (11313)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (11314)Refutation not found, incomplete strategy% (11314)------------------------------
% 0.22/0.52  % (11314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11314)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11314)Memory used [KB]: 6140
% 0.22/0.52  % (11314)Time elapsed: 0.106 s
% 0.22/0.52  % (11314)------------------------------
% 0.22/0.52  % (11314)------------------------------
% 0.22/0.52  % (11317)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (11317)Refutation not found, incomplete strategy% (11317)------------------------------
% 0.22/0.52  % (11317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11317)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11317)Memory used [KB]: 10618
% 0.22/0.52  % (11317)Time elapsed: 0.107 s
% 0.22/0.52  % (11317)------------------------------
% 0.22/0.52  % (11317)------------------------------
% 0.22/0.52  % (11328)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (11312)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.52  % (11308)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (11322)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (11326)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (11327)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.53  % (11329)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.53  % (11321)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % (11320)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (11320)# SZS output start Saturation.
% 0.22/0.54  cnf(u27,negated_conjecture,
% 0.22/0.54      m1_yellow_0(sK1,sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u26,negated_conjecture,
% 0.22/0.54      v4_yellow_0(sK1,sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u20,negated_conjecture,
% 0.22/0.54      r2_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u35,axiom,
% 0.22/0.54      ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~l1_orders_2(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u45,negated_conjecture,
% 0.22/0.54      ~r2_lattice3(sK1,sK2,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u47,negated_conjecture,
% 0.22/0.54      ~r2_lattice3(sK1,sK2,sK3) | ~r1_lattice3(sK1,sK2,sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u85,negated_conjecture,
% 0.22/0.54      r1_orders_2(sK0,sK6(X7,u1_struct_0(sK0),X8),sK3) | ~r2_hidden(sK6(X7,u1_struct_0(sK0),X8),sK2) | r1_lattice3(sK0,sK2,sK3) | ~l1_orders_2(X7) | r2_lattice3(X7,u1_struct_0(sK0),X8) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X8,u1_struct_0(X7))).
% 0.22/0.54  
% 0.22/0.54  cnf(u87,negated_conjecture,
% 0.22/0.54      r1_orders_2(sK0,sK6(sK0,X2,X3),sK3) | ~r2_hidden(sK6(sK0,X2,X3),sK2) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r2_lattice3(sK0,X2,X3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u84,negated_conjecture,
% 0.22/0.54      r1_orders_2(sK0,sK5(X5,u1_struct_0(sK0),X6),sK3) | ~r2_hidden(sK5(X5,u1_struct_0(sK0),X6),sK2) | r1_lattice3(sK0,sK2,sK3) | ~l1_orders_2(X5) | r1_lattice3(X5,u1_struct_0(sK0),X6) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X6,u1_struct_0(X5))).
% 0.22/0.54  
% 0.22/0.54  cnf(u86,negated_conjecture,
% 0.22/0.54      r1_orders_2(sK0,sK5(sK0,X0,X1),sK3) | ~r2_hidden(sK5(sK0,X0,X1),sK2) | r1_lattice3(sK0,sK2,sK3) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u80,negated_conjecture,
% 0.22/0.54      r1_orders_2(sK0,sK3,sK3) | ~r2_hidden(sK3,sK2) | r1_lattice3(sK0,sK2,sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u83,negated_conjecture,
% 0.22/0.54      r1_orders_2(sK0,X4,sK3) | ~r2_hidden(X4,sK2) | r1_lattice3(sK0,sK2,sK3) | ~v1_xboole_0(X4) | ~v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u38,axiom,
% 0.22/0.54      ~r1_orders_2(X0,sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u34,axiom,
% 0.22/0.54      ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u31,axiom,
% 0.22/0.54      ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~l1_orders_2(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u48,negated_conjecture,
% 0.22/0.54      ~r1_lattice3(sK1,sK2,sK3) | r2_lattice3(sK0,sK2,sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u29,negated_conjecture,
% 0.22/0.54      l1_orders_2(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u30,axiom,
% 0.22/0.54      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u49,negated_conjecture,
% 0.22/0.54      l1_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u28,negated_conjecture,
% 0.22/0.54      ~v2_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u25,negated_conjecture,
% 0.22/0.54      ~v2_struct_0(sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u37,axiom,
% 0.22/0.54      r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u33,axiom,
% 0.22/0.54      r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u65,axiom,
% 0.22/0.54      r2_hidden(sK6(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u63,axiom,
% 0.22/0.54      r2_hidden(sK5(X1,X2,X0),u1_struct_0(X1)) | ~l1_orders_2(X1) | r1_lattice3(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u55,negated_conjecture,
% 0.22/0.54      r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u54,negated_conjecture,
% 0.22/0.54      r2_hidden(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u96,negated_conjecture,
% 0.22/0.54      ~r2_hidden(sK6(sK0,X0,sK3),sK2) | r1_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,X0,sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u42,axiom,
% 0.22/0.54      ~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u62,axiom,
% 0.22/0.54      m1_subset_1(sK6(X1,X2,X0),X2) | ~l1_orders_2(X1) | r2_lattice3(X1,X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X0,u1_struct_0(X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u61,axiom,
% 0.22/0.54      m1_subset_1(sK5(X1,X2,X0),X2) | ~l1_orders_2(X1) | r1_lattice3(X1,X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X0,u1_struct_0(X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u40,axiom,
% 0.22/0.54      m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u36,axiom,
% 0.22/0.54      m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u32,axiom,
% 0.22/0.54      m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u44,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u24,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u79,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r1_orders_2(sK0,X0,sK3) | r1_lattice3(sK0,sK2,sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u41,axiom,
% 0.22/0.54      ~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u43,axiom,
% 0.22/0.54      ~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u66,axiom,
% 0.22/0.54      v1_xboole_0(sK6(X4,X5,X3)) | ~l1_orders_2(X4) | r2_lattice3(X4,X5,X3) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~v1_xboole_0(u1_struct_0(X4))).
% 0.22/0.54  
% 0.22/0.54  cnf(u64,axiom,
% 0.22/0.54      v1_xboole_0(sK5(X4,X5,X3)) | ~l1_orders_2(X4) | r1_lattice3(X4,X5,X3) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~v1_xboole_0(u1_struct_0(X4))).
% 0.22/0.54  
% 0.22/0.54  cnf(u51,negated_conjecture,
% 0.22/0.54      ~v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u50,negated_conjecture,
% 0.22/0.54      ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u39,axiom,
% 0.22/0.54      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u23,negated_conjecture,
% 0.22/0.54      sK3 = sK4).
% 0.22/0.54  
% 0.22/0.54  % (11320)# SZS output end Saturation.
% 0.22/0.54  % (11320)------------------------------
% 0.22/0.54  % (11320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11320)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (11320)Memory used [KB]: 6140
% 0.22/0.54  % (11320)Time elapsed: 0.132 s
% 0.22/0.54  % (11320)------------------------------
% 0.22/0.54  % (11320)------------------------------
% 0.22/0.54  % (11306)Success in time 0.181 s
%------------------------------------------------------------------------------
