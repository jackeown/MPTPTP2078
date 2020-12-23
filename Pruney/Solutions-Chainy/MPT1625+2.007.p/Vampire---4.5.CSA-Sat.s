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
% DateTime   : Thu Dec  3 13:16:54 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   63 (  63 expanded)
%              Number of leaves         :   63 (  63 expanded)
%              Depth                    :    0
%              Number of atoms          :  217 ( 217 expanded)
%              Number of equality atoms :   71 (  71 expanded)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u103,negated_conjecture,
    ( v6_orders_2(sK2(sK0,sK1,sK1),sK0) )).

cnf(u45,axiom,
    ( ~ v6_orders_2(X4,X0)
    | r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
    | r1_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u81,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u62,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | r3_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u53,axiom,
    ( ~ r1_orders_2(X0,X2,X1)
    | r2_hidden(X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u52,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X2,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u51,axiom,
    ( ~ r1_orders_2(X0,X2,X1)
    | r2_hidden(X1,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u50,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(X1,sK2(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u49,axiom,
    ( ~ r1_orders_2(X0,X2,X1)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u48,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u47,axiom,
    ( ~ r1_orders_2(X0,X2,X1)
    | v6_orders_2(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u46,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | v6_orders_2(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0) )).

cnf(u82,negated_conjecture,
    ( r3_orders_2(sK0,sK1,sK1) )).

cnf(u61,axiom,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u41,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u44,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u67,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r3_orders_2(X0,X1,X1)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u40,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u39,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u136,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

cnf(u137,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)) = k1_tarski(sK2(sK0,sK1,sK1)) )).

cnf(u162,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1)) )).

cnf(u161,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

cnf(u152,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u63,axiom,
    ( ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1) )).

cnf(u158,negated_conjecture,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u157,negated_conjecture,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK3(X0,sK2(sK0,sK1,sK1)) = X0
    | k1_tarski(X0) = sK2(sK0,sK1,sK1) )).

cnf(u106,negated_conjecture,
    ( m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u42,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u159,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(X1,X0) )).

cnf(u163,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)) = k1_tarski(sK2(sK0,sK1,sK1))
    | ~ r2_hidden(X1,X0) )).

cnf(u179,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1))
    | ~ r2_hidden(X1,X0) )).

cnf(u282,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r2_hidden(X1,X0) )).

cnf(u153,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(X1,X0) )).

cnf(u74,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u80,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r3_orders_2(sK0,X0,X0) )).

cnf(u133,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,sK2(sK0,sK1,sK1))
    | ~ r2_hidden(X0,sK2(sK0,sK1,sK1))
    | r1_orders_2(sK0,X1,X0)
    | r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u165,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X0)
    | r1_orders_2(sK0,X0,sK1)
    | ~ r2_hidden(X0,sK2(sK0,sK1,sK1)) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X1,X0)
    | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
    | v1_xboole_0(X0) )).

cnf(u109,negated_conjecture,
    ( r2_hidden(sK1,sK2(sK0,sK1,sK1)) )).

cnf(u58,axiom,
    ( r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u65,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

% (2654)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (2654)Refutation not found, incomplete strategy% (2654)------------------------------
% (2654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2654)Termination reason: Refutation not found, incomplete strategy

% (2654)Memory used [KB]: 1663
% (2654)Time elapsed: 0.002 s
% (2654)------------------------------
% (2654)------------------------------
% (2627)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (2638)Termination reason: Refutation not found, incomplete strategy

% (2638)Memory used [KB]: 6396
% (2638)Time elapsed: 0.104 s
% (2638)------------------------------
% (2638)------------------------------
% (2646)Termination reason: Refutation not found, incomplete strategy

% (2646)Memory used [KB]: 6396
% (2646)Time elapsed: 0.118 s
% (2646)------------------------------
% (2646)------------------------------
% (2636)Refutation not found, incomplete strategy% (2636)------------------------------
% (2636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2636)Termination reason: Refutation not found, incomplete strategy

% (2636)Memory used [KB]: 6396
% (2636)Time elapsed: 0.179 s
% (2636)------------------------------
% (2636)------------------------------
% (2642)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
cnf(u281,axiom,
    ( ~ r2_hidden(sK3(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK3(X14,k1_tarski(X13)) != X12
    | k1_tarski(X12) = k1_tarski(X13)
    | sK3(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u59,axiom,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | sK3(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u154,negated_conjecture,
    ( ~ r2_hidden(X0,sK2(sK0,sK1,sK1))
    | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u66,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u122,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK3(X0,k1_tarski(X1)) = X1 )).

cnf(u169,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK3(X2,k1_tarski(X3)) = X4
    | sK3(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u172,axiom,
    ( ~ r2_hidden(X13,k1_tarski(X12))
    | k1_tarski(X12) = k1_tarski(X13)
    | sK3(X11,k1_tarski(X12)) = sK3(X13,k1_tarski(X12))
    | sK3(X11,k1_tarski(X12)) = X11
    | k1_tarski(X12) = k1_tarski(X11) )).

cnf(u151,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u129,axiom,
    ( sK3(sK3(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK3(X1,k1_tarski(X2)))
    | sK3(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u170,axiom,
    ( sK3(X7,k1_tarski(X6)) = X7
    | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6))
    | sK3(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u75,axiom,
    ( sK3(X0,k1_tarski(X1)) = X0
    | sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u75_001,axiom,
    ( sK3(X0,k1_tarski(X1)) = X0
    | sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u170_002,axiom,
    ( sK3(X7,k1_tarski(X6)) = X7
    | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6))
    | sK3(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u170_003,axiom,
    ( sK3(X7,k1_tarski(X6)) = X7
    | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6))
    | sK3(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u149,axiom,
    ( k1_tarski(X5) = k1_tarski(sK3(X4,k1_tarski(X5)))
    | sK3(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u43,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u239,axiom,
    ( sK3(X2,k1_tarski(X1)) != X0
    | sK3(X2,k1_tarski(X1)) = X2
    | sK3(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u237,axiom,
    ( sK3(X2,k1_tarski(X1)) != X0
    | sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1))
    | sK3(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u117,axiom,
    ( X0 != X1
    | sK3(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u123,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK3(X0,k1_tarski(X1)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (2630)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (2625)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (2637)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (2637)Refutation not found, incomplete strategy% (2637)------------------------------
% 0.22/0.54  % (2637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2626)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (2638)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (2628)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (2629)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (2626)Refutation not found, incomplete strategy% (2626)------------------------------
% 0.22/0.54  % (2626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2626)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2626)Memory used [KB]: 1663
% 0.22/0.54  % (2626)Time elapsed: 0.124 s
% 0.22/0.54  % (2626)------------------------------
% 0.22/0.54  % (2626)------------------------------
% 0.22/0.54  % (2647)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (2629)Refutation not found, incomplete strategy% (2629)------------------------------
% 0.22/0.55  % (2629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2629)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2629)Memory used [KB]: 1791
% 0.22/0.55  % (2629)Time elapsed: 0.126 s
% 0.22/0.55  % (2629)------------------------------
% 0.22/0.55  % (2629)------------------------------
% 0.22/0.55  % (2637)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2637)Memory used [KB]: 10746
% 0.22/0.55  % (2637)Time elapsed: 0.125 s
% 0.22/0.55  % (2637)------------------------------
% 0.22/0.55  % (2637)------------------------------
% 0.22/0.55  % (2652)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (2631)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (2652)Refutation not found, incomplete strategy% (2652)------------------------------
% 0.22/0.55  % (2652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2652)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2652)Memory used [KB]: 6140
% 0.22/0.55  % (2652)Time elapsed: 0.137 s
% 0.22/0.55  % (2652)------------------------------
% 0.22/0.55  % (2652)------------------------------
% 0.22/0.55  % (2651)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (2651)Refutation not found, incomplete strategy% (2651)------------------------------
% 0.22/0.55  % (2651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2651)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2651)Memory used [KB]: 6268
% 0.22/0.55  % (2651)Time elapsed: 0.136 s
% 0.22/0.55  % (2651)------------------------------
% 0.22/0.55  % (2651)------------------------------
% 0.22/0.56  % (2645)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (2649)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (2633)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (2641)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (2653)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (2634)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (2639)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (2643)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (2639)Refutation not found, incomplete strategy% (2639)------------------------------
% 0.22/0.56  % (2639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2639)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2639)Memory used [KB]: 1791
% 0.22/0.56  % (2639)Time elapsed: 0.105 s
% 0.22/0.56  % (2639)------------------------------
% 0.22/0.56  % (2639)------------------------------
% 0.22/0.56  % (2643)Refutation not found, incomplete strategy% (2643)------------------------------
% 0.22/0.56  % (2643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2643)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2643)Memory used [KB]: 1663
% 0.22/0.56  % (2643)Time elapsed: 0.148 s
% 0.22/0.56  % (2643)------------------------------
% 0.22/0.56  % (2643)------------------------------
% 0.22/0.56  % (2653)Refutation not found, incomplete strategy% (2653)------------------------------
% 0.22/0.56  % (2653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2653)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2653)Memory used [KB]: 10746
% 0.22/0.56  % (2653)Time elapsed: 0.148 s
% 0.22/0.56  % (2653)------------------------------
% 0.22/0.56  % (2653)------------------------------
% 0.22/0.56  % (2640)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (2644)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (2636)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (2641)Refutation not found, incomplete strategy% (2641)------------------------------
% 0.22/0.56  % (2641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2649)Refutation not found, incomplete strategy% (2649)------------------------------
% 0.22/0.56  % (2649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2648)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (2641)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2641)Memory used [KB]: 10618
% 0.22/0.56  % (2641)Time elapsed: 0.145 s
% 0.22/0.56  % (2641)------------------------------
% 0.22/0.56  % (2641)------------------------------
% 0.22/0.56  % (2638)Refutation not found, incomplete strategy% (2638)------------------------------
% 0.22/0.56  % (2638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2646)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (2649)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (2649)Memory used [KB]: 10746
% 0.22/0.57  % (2649)Time elapsed: 0.145 s
% 0.22/0.57  % (2649)------------------------------
% 0.22/0.57  % (2649)------------------------------
% 0.22/0.57  % (2632)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (2646)Refutation not found, incomplete strategy% (2646)------------------------------
% 0.22/0.57  % (2646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.57  % (2632)# SZS output start Saturation.
% 0.22/0.57  cnf(u103,negated_conjecture,
% 0.22/0.57      v6_orders_2(sK2(sK0,sK1,sK1),sK0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u45,axiom,
% 0.22/0.57      ~v6_orders_2(X4,X0) | r1_orders_2(X0,X1,X2) | ~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u81,negated_conjecture,
% 0.22/0.57      r1_orders_2(sK0,sK1,sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u62,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u53,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X2,X1) | r2_hidden(X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u52,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X1,X2) | r2_hidden(X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u51,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X2,X1) | r2_hidden(X1,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u50,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X1,X2) | r2_hidden(X1,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u49,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X2,X1) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u48,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X1,X2) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u47,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X2,X1) | v6_orders_2(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u46,axiom,
% 0.22/0.57      ~r1_orders_2(X0,X1,X2) | v6_orders_2(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u82,negated_conjecture,
% 0.22/0.57      r3_orders_2(sK0,sK1,sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u61,axiom,
% 0.22/0.57      ~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u41,negated_conjecture,
% 0.22/0.57      l1_orders_2(sK0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u44,axiom,
% 0.22/0.57      ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u67,axiom,
% 0.22/0.57      ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u40,negated_conjecture,
% 0.22/0.57      v3_orders_2(sK0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u39,negated_conjecture,
% 0.22/0.57      ~v2_struct_0(sK0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u136,negated_conjecture,
% 0.22/0.57      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.57  
% 0.22/0.57  cnf(u137,negated_conjecture,
% 0.22/0.57      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)) = k1_tarski(sK2(sK0,sK1,sK1))).
% 0.22/0.57  
% 0.22/0.57  cnf(u162,negated_conjecture,
% 0.22/0.57      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1))).
% 0.22/0.57  
% 0.22/0.57  cnf(u161,negated_conjecture,
% 0.22/0.57      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.57  
% 0.22/0.57  cnf(u152,negated_conjecture,
% 0.22/0.57      v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.57  
% 0.22/0.57  cnf(u63,axiom,
% 0.22/0.57      ~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u158,negated_conjecture,
% 0.22/0.57      m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.57  
% 0.22/0.57  cnf(u157,negated_conjecture,
% 0.22/0.57      m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X0,sK2(sK0,sK1,sK1)) = X0 | k1_tarski(X0) = sK2(sK0,sK1,sK1)).
% 0.22/0.57  
% 0.22/0.57  cnf(u106,negated_conjecture,
% 0.22/0.57      m1_subset_1(sK2(sK0,sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.57  
% 0.22/0.57  cnf(u42,negated_conjecture,
% 0.22/0.57      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u159,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u163,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),sK2(sK0,sK1,sK1)) = k1_tarski(sK2(sK0,sK1,sK1)) | ~r2_hidden(X1,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u179,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1)) | ~r2_hidden(X1,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u282,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u153,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u74,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u80,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u133,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK2(sK0,sK1,sK1)) | ~r2_hidden(X0,sK2(sK0,sK1,sK1)) | r1_orders_2(sK0,X1,X0) | r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.22/0.57  
% 0.22/0.57  cnf(u165,negated_conjecture,
% 0.22/0.57      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0) | r1_orders_2(sK0,X0,sK1) | ~r2_hidden(X0,sK2(sK0,sK1,sK1))).
% 0.22/0.57  
% 0.22/0.57  cnf(u54,axiom,
% 0.22/0.57      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u55,axiom,
% 0.22/0.57      ~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)).
% 0.22/0.57  
% 0.22/0.57  cnf(u109,negated_conjecture,
% 0.22/0.57      r2_hidden(sK1,sK2(sK0,sK1,sK1))).
% 0.22/0.57  
% 0.22/0.57  cnf(u58,axiom,
% 0.22/0.57      r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) = X0 | k1_tarski(X0) = X1).
% 0.22/0.57  
% 0.22/0.57  cnf(u65,axiom,
% 0.22/0.57      r2_hidden(X3,k1_tarski(X3))).
% 0.22/0.57  
% 0.22/0.58  % (2654)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.58  % (2654)Refutation not found, incomplete strategy% (2654)------------------------------
% 0.22/0.58  % (2654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (2654)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (2654)Memory used [KB]: 1663
% 0.22/0.58  % (2654)Time elapsed: 0.002 s
% 0.22/0.58  % (2654)------------------------------
% 0.22/0.58  % (2654)------------------------------
% 0.22/0.58  % (2627)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.58  % (2638)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (2638)Memory used [KB]: 6396
% 0.22/0.58  % (2638)Time elapsed: 0.104 s
% 0.22/0.58  % (2638)------------------------------
% 0.22/0.58  % (2638)------------------------------
% 0.22/0.58  % (2646)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (2646)Memory used [KB]: 6396
% 0.22/0.58  % (2646)Time elapsed: 0.118 s
% 0.22/0.58  % (2646)------------------------------
% 0.22/0.58  % (2646)------------------------------
% 0.22/0.59  % (2636)Refutation not found, incomplete strategy% (2636)------------------------------
% 0.22/0.59  % (2636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (2636)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (2636)Memory used [KB]: 6396
% 0.22/0.59  % (2636)Time elapsed: 0.179 s
% 0.22/0.59  % (2636)------------------------------
% 0.22/0.59  % (2636)------------------------------
% 0.22/0.59  % (2642)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.59  cnf(u281,axiom,
% 0.22/0.59      ~r2_hidden(sK3(X14,k1_tarski(X13)),k1_tarski(X13)) | sK3(X14,k1_tarski(X13)) != X12 | k1_tarski(X12) = k1_tarski(X13) | sK3(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 0.22/0.59  
% 0.22/0.59  cnf(u59,axiom,
% 0.22/0.59      ~r2_hidden(sK3(X0,X1),X1) | sK3(X0,X1) != X0 | k1_tarski(X0) = X1).
% 0.22/0.59  
% 0.22/0.59  cnf(u154,negated_conjecture,
% 0.22/0.59      ~r2_hidden(X0,sK2(sK0,sK1,sK1)) | m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.59  
% 0.22/0.59  cnf(u66,axiom,
% 0.22/0.59      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 0.22/0.59  
% 0.22/0.59  cnf(u122,axiom,
% 0.22/0.59      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK3(X0,k1_tarski(X1)) = X1).
% 0.22/0.59  
% 0.22/0.59  cnf(u169,axiom,
% 0.22/0.59      ~r2_hidden(X4,k1_tarski(X3)) | sK3(X2,k1_tarski(X3)) = X4 | sK3(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 0.22/0.59  
% 0.22/0.59  cnf(u172,axiom,
% 0.22/0.59      ~r2_hidden(X13,k1_tarski(X12)) | k1_tarski(X12) = k1_tarski(X13) | sK3(X11,k1_tarski(X12)) = sK3(X13,k1_tarski(X12)) | sK3(X11,k1_tarski(X12)) = X11 | k1_tarski(X12) = k1_tarski(X11)).
% 0.22/0.59  
% 0.22/0.59  cnf(u151,negated_conjecture,
% 0.22/0.59      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u129,axiom,
% 0.22/0.59      sK3(sK3(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK3(X1,k1_tarski(X2))) | sK3(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 0.22/0.59  
% 0.22/0.59  cnf(u170,axiom,
% 0.22/0.59      sK3(X7,k1_tarski(X6)) = X7 | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6)) | sK3(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.59  
% 0.22/0.59  cnf(u75,axiom,
% 0.22/0.59      sK3(X0,k1_tarski(X1)) = X0 | sK3(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u75,axiom,
% 0.22/0.59      sK3(X0,k1_tarski(X1)) = X0 | sK3(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u170,axiom,
% 0.22/0.59      sK3(X7,k1_tarski(X6)) = X7 | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6)) | sK3(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.59  
% 0.22/0.59  cnf(u170,axiom,
% 0.22/0.59      sK3(X7,k1_tarski(X6)) = X7 | sK3(X5,k1_tarski(X6)) = sK3(X7,k1_tarski(X6)) | sK3(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.22/0.59  
% 0.22/0.59  cnf(u149,axiom,
% 0.22/0.59      k1_tarski(X5) = k1_tarski(sK3(X4,k1_tarski(X5))) | sK3(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 0.22/0.59  
% 0.22/0.59  cnf(u43,axiom,
% 0.22/0.59      k1_tarski(X0) = k2_tarski(X0,X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u239,axiom,
% 0.22/0.59      sK3(X2,k1_tarski(X1)) != X0 | sK3(X2,k1_tarski(X1)) = X2 | sK3(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u237,axiom,
% 0.22/0.59      sK3(X2,k1_tarski(X1)) != X0 | sK3(X0,k1_tarski(X1)) = sK3(X2,k1_tarski(X1)) | sK3(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 0.22/0.59  
% 0.22/0.59  cnf(u117,axiom,
% 0.22/0.59      X0 != X1 | sK3(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u123,axiom,
% 0.22/0.59      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK3(X0,k1_tarski(X1)) = X0).
% 0.22/0.59  
% 0.22/0.59  % (2632)# SZS output end Saturation.
% 0.22/0.59  % (2632)------------------------------
% 0.22/0.59  % (2632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (2632)Termination reason: Satisfiable
% 0.22/0.59  
% 0.22/0.59  % (2632)Memory used [KB]: 1791
% 0.22/0.59  % (2632)Time elapsed: 0.164 s
% 0.22/0.59  % (2632)------------------------------
% 0.22/0.59  % (2632)------------------------------
% 0.22/0.60  % (2624)Success in time 0.219 s
%------------------------------------------------------------------------------
