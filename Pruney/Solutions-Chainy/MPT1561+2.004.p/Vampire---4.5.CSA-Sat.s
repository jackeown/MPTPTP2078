%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:08 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   72 (  72 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u31,axiom,
    ( ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | X1 = X2 )).

cnf(u24,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u30,axiom,
    ( ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1) )).

cnf(u23,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u49,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u65,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,sK1)
    | sK1 = X0 )).

cnf(u51,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,sK1)
    | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u29,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ r1_orders_2(X0,X1,X2) )).

cnf(u37,axiom,
    ( ~ l1_orders_2(X0)
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))),u1_orders_2(X0)) = k1_tarski(u1_orders_2(X0))
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )).

cnf(u27,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u60,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))))
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0))
    | v1_xboole_0(X0) )).

cnf(u48,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
    | ~ r1_orders_2(sK0,X0,X1) )).

cnf(u64,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | X0 = X1 )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1) )).

cnf(u53,negated_conjecture,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) )).

cnf(u32,axiom,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u61,negated_conjecture,
    ( ~ r2_hidden(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0)) )).

cnf(u28,axiom,
    ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X2) )).

cnf(u59,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0)) )).

cnf(u33,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X1,X0) )).

cnf(u34,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | v1_xboole_0(X2) )).

cnf(u55,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u58,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k1_tarski(sK1))
    | sK1 != k1_yellow_0(sK0,k1_tarski(sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (14046)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (14055)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (14054)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (14063)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (14056)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (14070)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (14063)Refutation not found, incomplete strategy% (14063)------------------------------
% 0.20/0.53  % (14063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14070)Refutation not found, incomplete strategy% (14070)------------------------------
% 0.20/0.53  % (14070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14067)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (14070)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14070)Memory used [KB]: 1663
% 0.20/0.54  % (14070)Time elapsed: 0.124 s
% 0.20/0.54  % (14070)------------------------------
% 0.20/0.54  % (14070)------------------------------
% 0.20/0.54  % (14043)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (14063)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14063)Memory used [KB]: 10746
% 0.20/0.54  % (14063)Time elapsed: 0.068 s
% 0.20/0.54  % (14063)------------------------------
% 0.20/0.54  % (14063)------------------------------
% 0.20/0.54  % (14041)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (14043)Refutation not found, incomplete strategy% (14043)------------------------------
% 0.20/0.54  % (14043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14043)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14043)Memory used [KB]: 10618
% 0.20/0.54  % (14043)Time elapsed: 0.123 s
% 0.20/0.54  % (14043)------------------------------
% 0.20/0.54  % (14043)------------------------------
% 0.20/0.54  % (14047)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (14067)Refutation not found, incomplete strategy% (14067)------------------------------
% 0.20/0.54  % (14067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14067)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14067)Memory used [KB]: 10746
% 0.20/0.54  % (14067)Time elapsed: 0.130 s
% 0.20/0.54  % (14067)------------------------------
% 0.20/0.54  % (14067)------------------------------
% 0.20/0.54  % (14069)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (14041)Refutation not found, incomplete strategy% (14041)------------------------------
% 0.20/0.54  % (14041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14041)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14041)Memory used [KB]: 1663
% 0.20/0.54  % (14041)Time elapsed: 0.125 s
% 0.20/0.54  % (14041)------------------------------
% 0.20/0.54  % (14041)------------------------------
% 0.20/0.54  % (14044)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (14056)Refutation not found, incomplete strategy% (14056)------------------------------
% 0.20/0.54  % (14056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14042)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (14056)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14056)Memory used [KB]: 6268
% 0.20/0.54  % (14056)Time elapsed: 0.069 s
% 0.20/0.54  % (14056)------------------------------
% 0.20/0.54  % (14056)------------------------------
% 0.20/0.54  % (14044)Refutation not found, incomplete strategy% (14044)------------------------------
% 0.20/0.54  % (14044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14044)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14044)Memory used [KB]: 10746
% 0.20/0.54  % (14044)Time elapsed: 0.127 s
% 0.20/0.54  % (14044)------------------------------
% 0.20/0.54  % (14044)------------------------------
% 0.20/0.54  % (14048)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (14061)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.54  % (14047)# SZS output start Saturation.
% 0.20/0.54  cnf(u25,negated_conjecture,
% 0.20/0.54      v5_orders_2(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u31,axiom,
% 0.20/0.54      ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 0.20/0.54  
% 0.20/0.54  cnf(u24,negated_conjecture,
% 0.20/0.54      v3_orders_2(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u30,axiom,
% 0.20/0.54      ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u23,negated_conjecture,
% 0.20/0.54      ~v2_struct_0(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u49,negated_conjecture,
% 0.20/0.54      r1_orders_2(sK0,sK1,sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u65,negated_conjecture,
% 0.20/0.54      ~r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK1) | sK1 = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u51,negated_conjecture,
% 0.20/0.54      ~r1_orders_2(sK0,X0,sK1) | r2_hidden(k4_tarski(X0,sK1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u26,negated_conjecture,
% 0.20/0.54      l1_orders_2(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u29,axiom,
% 0.20/0.54      ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u37,axiom,
% 0.20/0.54      ~l1_orders_2(X0) | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))),u1_orders_2(X0)) = k1_tarski(u1_orders_2(X0)) | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))).
% 0.20/0.54  
% 0.20/0.54  cnf(u27,axiom,
% 0.20/0.54      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u22,negated_conjecture,
% 0.20/0.54      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u60,negated_conjecture,
% 0.20/0.54      ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))))) | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0)) | v1_xboole_0(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u48,negated_conjecture,
% 0.20/0.54      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u50,negated_conjecture,
% 0.20/0.54      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~r1_orders_2(sK0,X0,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u64,negated_conjecture,
% 0.20/0.54      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | X0 = X1).
% 0.20/0.54  
% 0.20/0.54  cnf(u35,axiom,
% 0.20/0.54      ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u53,negated_conjecture,
% 0.20/0.54      r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u32,axiom,
% 0.20/0.54      r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u61,negated_conjecture,
% 0.20/0.54      ~r2_hidden(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u28,axiom,
% 0.20/0.54      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u59,negated_conjecture,
% 0.20/0.54      v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k6_domain_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))),u1_orders_2(sK0)) = k1_tarski(u1_orders_2(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u33,axiom,
% 0.20/0.54      ~v1_xboole_0(X0) | ~r2_hidden(X1,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u34,axiom,
% 0.20/0.54      ~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u55,negated_conjecture,
% 0.20/0.54      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u58,negated_conjecture,
% 0.20/0.54      sK1 != k2_yellow_0(sK0,k1_tarski(sK1)) | sK1 != k1_yellow_0(sK0,k1_tarski(sK1))).
% 0.20/0.54  
% 0.20/0.54  % (14047)# SZS output end Saturation.
% 0.20/0.54  % (14047)------------------------------
% 0.20/0.54  % (14047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14047)Termination reason: Satisfiable
% 0.20/0.54  
% 0.20/0.54  % (14047)Memory used [KB]: 6268
% 0.20/0.54  % (14047)Time elapsed: 0.071 s
% 0.20/0.54  % (14047)------------------------------
% 0.20/0.54  % (14047)------------------------------
% 1.37/0.54  % (14036)Success in time 0.18 s
%------------------------------------------------------------------------------
