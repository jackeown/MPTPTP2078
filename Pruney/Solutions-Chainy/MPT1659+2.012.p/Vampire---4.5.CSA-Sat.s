%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:13 EST 2020

% Result     : CounterSatisfiable 1.20s
% Output     : Saturation 1.20s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   68 (  68 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u25,axiom,
    ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u23,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

cnf(u24,axiom,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u20,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u26,axiom,
    ( ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u27,axiom,
    ( ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u28,axiom,
    ( v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u29,axiom,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u33,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u37,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u21,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u30,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u32,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u18,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u31,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0) )).

cnf(u36,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0) )).

cnf(u17,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u39,negated_conjecture,
    ( sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u35,negated_conjecture,
    ( sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:00:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (3167)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.48  % (3167)Refutation not found, incomplete strategy% (3167)------------------------------
% 0.20/0.48  % (3167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3167)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (3167)Memory used [KB]: 1663
% 0.20/0.48  % (3167)Time elapsed: 0.006 s
% 0.20/0.48  % (3167)------------------------------
% 0.20/0.48  % (3167)------------------------------
% 0.20/0.51  % (3172)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (3152)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.52  % (3154)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.20/0.52  % (3157)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.20/0.52  % (3157)Refutation not found, incomplete strategy% (3157)------------------------------
% 1.20/0.52  % (3157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (3157)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (3157)Memory used [KB]: 6012
% 1.20/0.52  % (3157)Time elapsed: 0.001 s
% 1.20/0.52  % (3157)------------------------------
% 1.20/0.52  % (3157)------------------------------
% 1.20/0.52  % (3166)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.20/0.52  % (3166)Refutation not found, incomplete strategy% (3166)------------------------------
% 1.20/0.52  % (3166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (3166)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (3166)Memory used [KB]: 1535
% 1.20/0.52  % (3166)Time elapsed: 0.002 s
% 1.20/0.52  % (3166)------------------------------
% 1.20/0.52  % (3166)------------------------------
% 1.20/0.53  % (3153)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.20/0.53  % (3160)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.20/0.53  % (3164)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.20/0.53  % (3153)Refutation not found, incomplete strategy% (3153)------------------------------
% 1.20/0.53  % (3153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3153)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (3153)Memory used [KB]: 10490
% 1.20/0.53  % (3153)Time elapsed: 0.097 s
% 1.20/0.53  % (3153)------------------------------
% 1.20/0.53  % (3153)------------------------------
% 1.20/0.53  % (3160)Refutation not found, incomplete strategy% (3160)------------------------------
% 1.20/0.53  % (3160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3160)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (3160)Memory used [KB]: 10490
% 1.20/0.53  % (3160)Time elapsed: 0.003 s
% 1.20/0.53  % (3160)------------------------------
% 1.20/0.53  % (3160)------------------------------
% 1.20/0.53  % (3156)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.20/0.53  % (3169)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.20/0.53  % (3169)Refutation not found, incomplete strategy% (3169)------------------------------
% 1.20/0.53  % (3169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3169)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (3169)Memory used [KB]: 6140
% 1.20/0.53  % (3169)Time elapsed: 0.112 s
% 1.20/0.53  % (3169)------------------------------
% 1.20/0.53  % (3169)------------------------------
% 1.20/0.53  % (3155)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.20/0.53  % (3156)Refutation not found, incomplete strategy% (3156)------------------------------
% 1.20/0.53  % (3156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3156)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (3156)Memory used [KB]: 10618
% 1.20/0.53  % (3156)Time elapsed: 0.107 s
% 1.20/0.53  % (3156)------------------------------
% 1.20/0.53  % (3156)------------------------------
% 1.20/0.53  % (3150)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.20/0.53  % (3168)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.20/0.53  % (3170)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.20/0.53  % (3161)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.20/0.53  % (3151)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.20/0.53  % (3161)Refutation not found, incomplete strategy% (3161)------------------------------
% 1.20/0.53  % (3161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3161)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  % (3170)Refutation not found, incomplete strategy% (3170)------------------------------
% 1.20/0.53  % (3170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3170)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (3170)Memory used [KB]: 6012
% 1.20/0.53  % (3170)Time elapsed: 0.111 s
% 1.20/0.53  % (3170)------------------------------
% 1.20/0.53  % (3170)------------------------------
% 1.20/0.53  
% 1.20/0.53  % (3161)Memory used [KB]: 1663
% 1.20/0.53  % (3161)Time elapsed: 0.111 s
% 1.20/0.53  % (3161)------------------------------
% 1.20/0.53  % (3161)------------------------------
% 1.20/0.53  % (3159)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.20/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.20/0.54  % (3159)# SZS output start Saturation.
% 1.20/0.54  cnf(u19,negated_conjecture,
% 1.20/0.54      v4_orders_2(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u25,axiom,
% 1.20/0.54      r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u23,negated_conjecture,
% 1.20/0.54      ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))).
% 1.20/0.54  
% 1.20/0.54  cnf(u24,axiom,
% 1.20/0.54      r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u20,negated_conjecture,
% 1.20/0.54      v5_orders_2(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u26,axiom,
% 1.20/0.54      ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u27,axiom,
% 1.20/0.54      ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u28,axiom,
% 1.20/0.54      v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u29,axiom,
% 1.20/0.54      m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u22,negated_conjecture,
% 1.20/0.54      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.20/0.54  
% 1.20/0.54  cnf(u33,negated_conjecture,
% 1.20/0.54      ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u37,negated_conjecture,
% 1.20/0.54      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u21,negated_conjecture,
% 1.20/0.54      l1_orders_2(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u30,negated_conjecture,
% 1.20/0.54      ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u32,negated_conjecture,
% 1.20/0.54      ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u18,negated_conjecture,
% 1.20/0.54      v3_orders_2(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u31,negated_conjecture,
% 1.20/0.54      ~v3_orders_2(sK0) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u36,negated_conjecture,
% 1.20/0.54      ~v3_orders_2(sK0) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u17,negated_conjecture,
% 1.20/0.54      ~v2_struct_0(sK0)).
% 1.20/0.54  
% 1.20/0.54  cnf(u39,negated_conjecture,
% 1.20/0.54      sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 1.20/0.54  
% 1.20/0.54  cnf(u35,negated_conjecture,
% 1.20/0.54      sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 1.20/0.54  
% 1.20/0.54  % (3159)# SZS output end Saturation.
% 1.20/0.54  % (3159)------------------------------
% 1.20/0.54  % (3159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.54  % (3159)Termination reason: Satisfiable
% 1.20/0.54  
% 1.20/0.54  % (3159)Memory used [KB]: 1663
% 1.20/0.54  % (3159)Time elapsed: 0.087 s
% 1.20/0.54  % (3159)------------------------------
% 1.20/0.54  % (3159)------------------------------
% 1.20/0.54  % (3148)Success in time 0.17 s
%------------------------------------------------------------------------------
