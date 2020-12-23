%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:54 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   39 (  39 expanded)
%              Number of leaves         :   39 (  39 expanded)
%              Depth                    :    0
%              Number of atoms          :  118 ( 118 expanded)
%              Number of equality atoms :   66 (  66 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u75,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u49,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u66,negated_conjecture,
    ( r3_orders_2(sK0,sK1,sK1) )).

cnf(u48,axiom,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u35,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u53,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r3_orders_2(X0,X1,X1)
    | v2_struct_0(X0) )).

cnf(u41,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0) )).

cnf(u77,negated_conjecture,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u37,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u62,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_orders_2(sK0,X0,X0) )).

cnf(u65,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u36,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u39,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u91,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1)) )).

cnf(u40,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u54,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u34,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u45,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u51,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u219,axiom,
    ( ~ r2_hidden(sK2(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK2(X14,k1_tarski(X13)) != X12
    | k1_tarski(X12) = k1_tarski(X13)
    | sK2(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u46,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u52,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u89,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK2(X0,k1_tarski(X1)) = X1 )).

cnf(u113,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK2(X2,k1_tarski(X3)) = X4
    | sK2(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u116,axiom,
    ( ~ r2_hidden(X13,k1_tarski(X12))
    | k1_tarski(X12) = k1_tarski(X13)
    | sK2(X11,k1_tarski(X12)) = sK2(X13,k1_tarski(X12))
    | sK2(X11,k1_tarski(X12)) = X11
    | k1_tarski(X12) = k1_tarski(X11) )).

cnf(u69,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u95,axiom,
    ( sK2(sK2(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK2(X1,k1_tarski(X2)))
    | sK2(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u114,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u57,axiom,
    ( sK2(X0,k1_tarski(X1)) = X0
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u57_001,axiom,
    ( sK2(X0,k1_tarski(X1)) = X0
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u114_002,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u114_003,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u109,axiom,
    ( k1_tarski(X5) = k1_tarski(sK2(X4,k1_tarski(X5)))
    | sK2(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u38,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u177,axiom,
    ( sK2(X2,k1_tarski(X1)) != X0
    | sK2(X2,k1_tarski(X1)) = X2
    | sK2(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u175,axiom,
    ( sK2(X2,k1_tarski(X1)) != X0
    | sK2(X0,k1_tarski(X1)) = sK2(X2,k1_tarski(X1))
    | sK2(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u84,axiom,
    ( X0 != X1
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u90,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK2(X0,k1_tarski(X1)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:38:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (32449)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (32466)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (32453)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (32474)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (32458)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (32458)Refutation not found, incomplete strategy% (32458)------------------------------
% 0.22/0.52  % (32458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32458)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32458)Memory used [KB]: 10618
% 0.22/0.52  % (32458)Time elapsed: 0.002 s
% 0.22/0.52  % (32458)------------------------------
% 0.22/0.52  % (32458)------------------------------
% 0.22/0.52  % (32463)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (32459)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (32474)Refutation not found, incomplete strategy% (32474)------------------------------
% 0.22/0.53  % (32474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32474)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32474)Memory used [KB]: 10746
% 0.22/0.53  % (32474)Time elapsed: 0.107 s
% 0.22/0.53  % (32474)------------------------------
% 0.22/0.53  % (32474)------------------------------
% 0.22/0.53  % (32446)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (32459)Refutation not found, incomplete strategy% (32459)------------------------------
% 0.22/0.53  % (32459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32459)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32459)Memory used [KB]: 6268
% 0.22/0.53  % (32459)Time elapsed: 0.107 s
% 0.22/0.53  % (32459)------------------------------
% 0.22/0.53  % (32459)------------------------------
% 0.22/0.53  % (32457)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (32455)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (32453)# SZS output start Saturation.
% 0.22/0.53  cnf(u75,negated_conjecture,
% 0.22/0.53      r1_orders_2(sK0,sK1,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u49,axiom,
% 0.22/0.53      ~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u66,negated_conjecture,
% 0.22/0.53      r3_orders_2(sK0,sK1,sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u48,axiom,
% 0.22/0.53      ~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u35,negated_conjecture,
% 0.22/0.53      v3_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u53,axiom,
% 0.22/0.53      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r3_orders_2(X0,X1,X1) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u41,axiom,
% 0.22/0.53      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u77,negated_conjecture,
% 0.22/0.53      m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.53  
% 0.22/0.53  cnf(u37,negated_conjecture,
% 0.22/0.53      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.53  
% 0.22/0.53  cnf(u62,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u65,negated_conjecture,
% 0.22/0.53      ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.53  
% 0.22/0.53  cnf(u42,axiom,
% 0.22/0.53      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u36,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u39,axiom,
% 0.22/0.53      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u91,negated_conjecture,
% 0.22/0.53      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1))).
% 0.22/0.53  
% 0.22/0.53  cnf(u40,axiom,
% 0.22/0.53      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u54,negated_conjecture,
% 0.22/0.53      l1_struct_0(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u34,negated_conjecture,
% 0.22/0.53      ~v2_struct_0(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u45,axiom,
% 0.22/0.53      r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) = X0 | k1_tarski(X0) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u51,axiom,
% 0.22/0.53      r2_hidden(X3,k1_tarski(X3))).
% 0.22/0.53  
% 0.22/0.53  cnf(u219,axiom,
% 0.22/0.53      ~r2_hidden(sK2(X14,k1_tarski(X13)),k1_tarski(X13)) | sK2(X14,k1_tarski(X13)) != X12 | k1_tarski(X12) = k1_tarski(X13) | sK2(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 0.22/0.53  
% 0.22/0.53  cnf(u46,axiom,
% 0.22/0.53      ~r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) != X0 | k1_tarski(X0) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u52,axiom,
% 0.22/0.53      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 0.22/0.53  
% 0.22/0.53  cnf(u89,axiom,
% 0.22/0.53      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK2(X0,k1_tarski(X1)) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u113,axiom,
% 0.22/0.53      ~r2_hidden(X4,k1_tarski(X3)) | sK2(X2,k1_tarski(X3)) = X4 | sK2(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u116,axiom,
% 0.22/0.53      ~r2_hidden(X13,k1_tarski(X12)) | k1_tarski(X12) = k1_tarski(X13) | sK2(X11,k1_tarski(X12)) = sK2(X13,k1_tarski(X12)) | sK2(X11,k1_tarski(X12)) = X11 | k1_tarski(X12) = k1_tarski(X11)).
% 0.22/0.53  
% 0.22/0.53  cnf(u69,negated_conjecture,
% 0.22/0.53      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u95,axiom,
% 0.22/0.53      sK2(sK2(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK2(X1,k1_tarski(X2))) | sK2(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u114,axiom,
% 0.22/0.53      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.53  
% 0.22/0.53  cnf(u57,axiom,
% 0.22/0.53      sK2(X0,k1_tarski(X1)) = X0 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u57,axiom,
% 0.22/0.53      sK2(X0,k1_tarski(X1)) = X0 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u114,axiom,
% 0.22/0.53      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.53  
% 0.22/0.53  cnf(u114,axiom,
% 0.22/0.53      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.53  
% 0.22/0.53  cnf(u109,axiom,
% 0.22/0.53      k1_tarski(X5) = k1_tarski(sK2(X4,k1_tarski(X5))) | sK2(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 0.22/0.53  
% 0.22/0.53  cnf(u38,axiom,
% 0.22/0.53      k1_tarski(X0) = k2_tarski(X0,X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u177,axiom,
% 0.22/0.53      sK2(X2,k1_tarski(X1)) != X0 | sK2(X2,k1_tarski(X1)) = X2 | sK2(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u175,axiom,
% 0.22/0.53      sK2(X2,k1_tarski(X1)) != X0 | sK2(X0,k1_tarski(X1)) = sK2(X2,k1_tarski(X1)) | sK2(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u84,axiom,
% 0.22/0.53      X0 != X1 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u90,axiom,
% 0.22/0.53      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK2(X0,k1_tarski(X1)) = X0).
% 0.22/0.53  
% 0.22/0.54  % (32453)# SZS output end Saturation.
% 0.22/0.54  % (32453)------------------------------
% 0.22/0.54  % (32453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32453)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (32453)Memory used [KB]: 1791
% 0.22/0.54  % (32453)Time elapsed: 0.113 s
% 0.22/0.54  % (32453)------------------------------
% 0.22/0.54  % (32453)------------------------------
% 0.22/0.54  % (32454)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (32445)Success in time 0.171 s
%------------------------------------------------------------------------------
