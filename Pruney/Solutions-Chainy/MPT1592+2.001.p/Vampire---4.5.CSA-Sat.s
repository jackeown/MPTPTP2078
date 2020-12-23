%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:25 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   46 (  46 expanded)
%              Number of leaves         :   46 (  46 expanded)
%              Depth                    :    0
%              Number of atoms          :   78 (  78 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u31,negated_conjecture,
    ( m1_yellow_0(sK1,sK0) )).

cnf(u30,negated_conjecture,
    ( v6_yellow_0(sK1,sK0) )).

cnf(u29,negated_conjecture,
    ( v4_yellow_0(sK1,sK0) )).

cnf(u34,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u33,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u32,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u35,negated_conjecture,
    ( v1_lattice3(sK0) )).

cnf(u38,axiom,
    ( ~ v1_lattice3(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_struct_0(X0) )).

cnf(u36,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u37,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u49,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u68,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | k7_domain_1(u1_struct_0(sK1),sK3,sK3) = k2_tarski(sK3,sK3) )).

cnf(u70,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | k7_domain_1(u1_struct_0(sK1),sK2,sK3) = k2_tarski(sK2,sK3) )).

cnf(u75,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | k7_domain_1(u1_struct_0(sK1),sK2,sK2) = k2_tarski(sK2,sK2) )).

cnf(u77,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK1),sK3,sK2) )).

cnf(u51,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK1) )).

cnf(u48,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) )).

cnf(u47,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) )).

cnf(u63,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | k7_domain_1(u1_struct_0(sK0),X2,sK2) = k2_tarski(X2,sK2) )).

cnf(u64,negated_conjecture,
    ( ~ m1_subset_1(X3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | k7_domain_1(u1_struct_0(sK0),X3,sK3) = k2_tarski(X3,sK3) )).

cnf(u61,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3) )).

cnf(u62,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X2,X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) )).

cnf(u55,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u54,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u56,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u53,negated_conjecture,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) )).

cnf(u40,axiom,
    ( r2_hidden(sK6(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u41,axiom,
    ( ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(X0) )).

cnf(u65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k7_domain_1(u1_struct_0(sK1),sK3,sK3) = k2_tarski(sK3,sK3) )).

cnf(u66,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k7_domain_1(u1_struct_0(sK1),sK2,sK3) = k2_tarski(sK2,sK3) )).

cnf(u72,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k7_domain_1(u1_struct_0(sK1),sK2,sK2) = k2_tarski(sK2,sK2) )).

cnf(u73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK1),sK3,sK2) )).

cnf(u39,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u94,negated_conjecture,
    ( k2_tarski(sK3,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK3) )).

cnf(u91,negated_conjecture,
    ( k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK2,sK3) )).

cnf(u86,negated_conjecture,
    ( k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK2) )).

cnf(u83,negated_conjecture,
    ( k2_tarski(sK2,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK2) )).

cnf(u42,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u23,negated_conjecture,
    ( sK3 = sK5 )).

cnf(u22,negated_conjecture,
    ( sK2 = sK4 )).

cnf(u46,negated_conjecture,
    ( k13_lattice3(sK1,sK2,sK3) != k13_lattice3(sK0,sK2,sK3) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (29862)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.47  % (29869)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.48  % (29869)Refutation not found, incomplete strategy% (29869)------------------------------
% 0.20/0.48  % (29869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29862)Refutation not found, incomplete strategy% (29862)------------------------------
% 0.20/0.48  % (29862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29869)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (29869)Memory used [KB]: 1663
% 0.20/0.48  % (29869)Time elapsed: 0.066 s
% 0.20/0.48  % (29869)------------------------------
% 0.20/0.48  % (29869)------------------------------
% 0.20/0.48  % (29862)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (29862)Memory used [KB]: 10490
% 0.20/0.48  % (29862)Time elapsed: 0.060 s
% 0.20/0.48  % (29862)------------------------------
% 0.20/0.48  % (29862)------------------------------
% 0.20/0.50  % (29860)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.50  % (29858)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (29860)Refutation not found, incomplete strategy% (29860)------------------------------
% 0.20/0.50  % (29860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29860)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29860)Memory used [KB]: 10618
% 0.20/0.50  % (29860)Time elapsed: 0.088 s
% 0.20/0.50  % (29860)------------------------------
% 0.20/0.50  % (29860)------------------------------
% 0.20/0.51  % (29855)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (29870)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.51  % (29872)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (29855)Refutation not found, incomplete strategy% (29855)------------------------------
% 0.20/0.51  % (29855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29855)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29855)Memory used [KB]: 10618
% 0.20/0.51  % (29855)Time elapsed: 0.088 s
% 0.20/0.51  % (29855)------------------------------
% 0.20/0.51  % (29855)------------------------------
% 0.20/0.51  % (29872)Refutation not found, incomplete strategy% (29872)------------------------------
% 0.20/0.51  % (29872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29872)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29872)Memory used [KB]: 6140
% 0.20/0.51  % (29872)Time elapsed: 0.093 s
% 0.20/0.51  % (29872)------------------------------
% 0.20/0.51  % (29872)------------------------------
% 0.20/0.51  % (29856)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (29863)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (29857)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.51  % (29871)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (29858)Refutation not found, incomplete strategy% (29858)------------------------------
% 0.20/0.51  % (29858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29858)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29858)Memory used [KB]: 10618
% 0.20/0.51  % (29858)Time elapsed: 0.079 s
% 0.20/0.51  % (29858)------------------------------
% 0.20/0.51  % (29858)------------------------------
% 0.20/0.51  % (29871)Refutation not found, incomplete strategy% (29871)------------------------------
% 0.20/0.51  % (29871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29871)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29871)Memory used [KB]: 6140
% 0.20/0.51  % (29871)Time elapsed: 0.100 s
% 0.20/0.51  % (29871)------------------------------
% 0.20/0.51  % (29871)------------------------------
% 0.20/0.52  % (29863)Refutation not found, incomplete strategy% (29863)------------------------------
% 0.20/0.52  % (29863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29863)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29863)Memory used [KB]: 1663
% 0.20/0.52  % (29863)Time elapsed: 0.102 s
% 0.20/0.52  % (29863)------------------------------
% 0.20/0.52  % (29863)------------------------------
% 0.20/0.52  % (29873)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.52  % (29875)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.52  % (29873)Refutation not found, incomplete strategy% (29873)------------------------------
% 0.20/0.52  % (29873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29873)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29873)Memory used [KB]: 1663
% 0.20/0.52  % (29873)Time elapsed: 0.065 s
% 0.20/0.52  % (29873)------------------------------
% 0.20/0.52  % (29873)------------------------------
% 0.20/0.52  % (29853)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.52  % (29859)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (29865)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.52  % (29859)Refutation not found, incomplete strategy% (29859)------------------------------
% 0.20/0.52  % (29859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29859)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29859)Memory used [KB]: 6012
% 0.20/0.52  % (29859)Time elapsed: 0.110 s
% 0.20/0.52  % (29859)------------------------------
% 0.20/0.52  % (29859)------------------------------
% 0.20/0.53  % (29864)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (29865)# SZS output start Saturation.
% 0.20/0.53  cnf(u31,negated_conjecture,
% 0.20/0.53      m1_yellow_0(sK1,sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u30,negated_conjecture,
% 0.20/0.53      v6_yellow_0(sK1,sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u29,negated_conjecture,
% 0.20/0.53      v4_yellow_0(sK1,sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u34,negated_conjecture,
% 0.20/0.53      v5_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u33,negated_conjecture,
% 0.20/0.53      v4_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u32,negated_conjecture,
% 0.20/0.53      v3_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u35,negated_conjecture,
% 0.20/0.53      v1_lattice3(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u38,axiom,
% 0.20/0.53      ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~v2_struct_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u36,negated_conjecture,
% 0.20/0.53      l1_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u37,axiom,
% 0.20/0.53      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u49,negated_conjecture,
% 0.20/0.53      l1_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u68,negated_conjecture,
% 0.20/0.53      ~l1_struct_0(sK1) | k7_domain_1(u1_struct_0(sK1),sK3,sK3) = k2_tarski(sK3,sK3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u70,negated_conjecture,
% 0.20/0.53      ~l1_struct_0(sK1) | k7_domain_1(u1_struct_0(sK1),sK2,sK3) = k2_tarski(sK2,sK3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u75,negated_conjecture,
% 0.20/0.53      ~l1_struct_0(sK1) | k7_domain_1(u1_struct_0(sK1),sK2,sK2) = k2_tarski(sK2,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u77,negated_conjecture,
% 0.20/0.53      ~l1_struct_0(sK1) | k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK1),sK3,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u51,negated_conjecture,
% 0.20/0.53      ~v2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u28,negated_conjecture,
% 0.20/0.53      ~v2_struct_0(sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u48,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK3,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u47,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u27,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK2,u1_struct_0(sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u26,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK3,u1_struct_0(sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u63,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | k7_domain_1(u1_struct_0(sK0),X2,sK2) = k2_tarski(X2,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u64,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | k7_domain_1(u1_struct_0(sK0),X3,sK3) = k2_tarski(X3,sK3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u61,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X0,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k7_domain_1(u1_struct_0(sK1),X0,sK3) = k2_tarski(X0,sK3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u62,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X1,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | k7_domain_1(u1_struct_0(sK1),X1,sK2) = k2_tarski(X1,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u43,axiom,
% 0.20/0.53      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u44,axiom,
% 0.20/0.53      ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u55,negated_conjecture,
% 0.20/0.53      r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u54,negated_conjecture,
% 0.20/0.53      r2_hidden(sK2,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u56,negated_conjecture,
% 0.20/0.53      r2_hidden(sK3,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u53,negated_conjecture,
% 0.20/0.53      r2_hidden(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u40,axiom,
% 0.20/0.53      r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u41,axiom,
% 0.20/0.53      ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u65,negated_conjecture,
% 0.20/0.53      v1_xboole_0(u1_struct_0(sK1)) | k7_domain_1(u1_struct_0(sK1),sK3,sK3) = k2_tarski(sK3,sK3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u66,negated_conjecture,
% 0.20/0.53      v1_xboole_0(u1_struct_0(sK1)) | k7_domain_1(u1_struct_0(sK1),sK2,sK3) = k2_tarski(sK2,sK3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u72,negated_conjecture,
% 0.20/0.53      v1_xboole_0(u1_struct_0(sK1)) | k7_domain_1(u1_struct_0(sK1),sK2,sK2) = k2_tarski(sK2,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u73,negated_conjecture,
% 0.20/0.53      v1_xboole_0(u1_struct_0(sK1)) | k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK1),sK3,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u39,axiom,
% 0.20/0.53      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u94,negated_conjecture,
% 0.20/0.53      k2_tarski(sK3,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u91,negated_conjecture,
% 0.20/0.53      k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK2,sK3)).
% 0.20/0.53  
% 0.20/0.53  cnf(u86,negated_conjecture,
% 0.20/0.53      k2_tarski(sK2,sK3) = k7_domain_1(u1_struct_0(sK0),sK3,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u83,negated_conjecture,
% 0.20/0.53      k2_tarski(sK2,sK2) = k7_domain_1(u1_struct_0(sK0),sK2,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u42,axiom,
% 0.20/0.53      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u23,negated_conjecture,
% 0.20/0.53      sK3 = sK5).
% 0.20/0.53  
% 0.20/0.53  cnf(u22,negated_conjecture,
% 0.20/0.53      sK2 = sK4).
% 0.20/0.53  
% 0.20/0.53  cnf(u46,negated_conjecture,
% 0.20/0.53      k13_lattice3(sK1,sK2,sK3) != k13_lattice3(sK0,sK2,sK3)).
% 0.20/0.53  
% 0.20/0.53  % (29865)# SZS output end Saturation.
% 0.20/0.53  % (29865)------------------------------
% 0.20/0.53  % (29865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29865)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (29865)Memory used [KB]: 6140
% 0.20/0.53  % (29865)Time elapsed: 0.077 s
% 0.20/0.53  % (29865)------------------------------
% 0.20/0.53  % (29865)------------------------------
% 0.20/0.53  % (29851)Success in time 0.17 s
%------------------------------------------------------------------------------
