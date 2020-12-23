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
% DateTime   : Thu Dec  3 13:16:06 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   38 (  38 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u38,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k1_tarski(sK1))
    | ~ r1_yellow_0(sK0,k1_tarski(sK1)) )).

cnf(u23,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u48,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u29,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | r3_orders_2(X0,X1,X2) )).

cnf(u42,negated_conjecture,
    ( r3_orders_2(sK0,sK1,sK1) )).

cnf(u30,axiom,
    ( ~ r3_orders_2(X0,X1,X2)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2)
    | v2_struct_0(X0) )).

cnf(u22,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | r3_orders_2(X1,X0,X0) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1) )).

cnf(u24,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u25,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u26,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u32,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u21,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u36,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:46:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (18694)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (18688)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (18691)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (18690)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (18690)Refutation not found, incomplete strategy% (18690)------------------------------
% 0.22/0.50  % (18690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18690)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18690)Memory used [KB]: 10618
% 0.22/0.50  % (18690)Time elapsed: 0.085 s
% 0.22/0.50  % (18690)------------------------------
% 0.22/0.50  % (18690)------------------------------
% 0.22/0.50  % (18706)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.50  % (18709)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  % (18706)Refutation not found, incomplete strategy% (18706)------------------------------
% 0.22/0.50  % (18706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (18706)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (18706)Memory used [KB]: 6012
% 0.22/0.50  % (18706)Time elapsed: 0.090 s
% 0.22/0.50  % (18706)------------------------------
% 0.22/0.50  % (18706)------------------------------
% 0.22/0.51  % (18694)Refutation not found, incomplete strategy% (18694)------------------------------
% 0.22/0.51  % (18694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18694)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18694)Memory used [KB]: 6012
% 0.22/0.51  % (18694)Time elapsed: 0.002 s
% 0.22/0.51  % (18694)------------------------------
% 0.22/0.51  % (18694)------------------------------
% 0.22/0.51  % (18692)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (18700)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (18687)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (18700)# SZS output start Saturation.
% 0.22/0.51  cnf(u38,negated_conjecture,
% 0.22/0.51      ~r2_yellow_0(sK0,k1_tarski(sK1)) | ~r1_yellow_0(sK0,k1_tarski(sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u23,negated_conjecture,
% 0.22/0.51      v5_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u48,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK1,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,axiom,
% 0.22/0.51      ~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,negated_conjecture,
% 0.22/0.51      r3_orders_2(sK0,sK1,sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,axiom,
% 0.22/0.51      ~r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | v2_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,negated_conjecture,
% 0.22/0.51      v3_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u31,axiom,
% 0.22/0.51      ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~v3_orders_2(X1) | ~l1_orders_2(X1) | r3_orders_2(X1,X0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u27,axiom,
% 0.22/0.51      ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u24,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u26,axiom,
% 0.22/0.51      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u32,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u21,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u36,negated_conjecture,
% 0.22/0.51      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.22/0.51  
% 0.22/0.51  % (18700)# SZS output end Saturation.
% 0.22/0.51  % (18700)------------------------------
% 0.22/0.51  % (18700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18700)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (18700)Memory used [KB]: 6140
% 0.22/0.51  % (18700)Time elapsed: 0.063 s
% 0.22/0.51  % (18700)------------------------------
% 0.22/0.51  % (18700)------------------------------
% 0.22/0.51  % (18686)Success in time 0.147 s
%------------------------------------------------------------------------------
