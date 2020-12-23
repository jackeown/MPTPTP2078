%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:36 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u45,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u57,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u51,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u52,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u42,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u54,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u100,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1),sK1)) )).

cnf(u53,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u78,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u62,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u69,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u25,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u30,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u72,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u22,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u71,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X2) )).

cnf(u70,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u47,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u40,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u27,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u94,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u87,axiom,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X1,X0)))) = X0 )).

cnf(u68,axiom,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 )).

cnf(u56,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u28,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u44,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:51:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (12073)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (12085)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (12073)Refutation not found, incomplete strategy% (12073)------------------------------
% 0.21/0.50  % (12073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12091)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (12073)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12073)Memory used [KB]: 6268
% 0.21/0.50  % (12073)Time elapsed: 0.086 s
% 0.21/0.50  % (12073)------------------------------
% 0.21/0.50  % (12073)------------------------------
% 0.21/0.51  % (12082)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (12091)Refutation not found, incomplete strategy% (12091)------------------------------
% 0.21/0.51  % (12091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12091)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12091)Memory used [KB]: 10746
% 0.21/0.51  % (12091)Time elapsed: 0.102 s
% 0.21/0.51  % (12091)------------------------------
% 0.21/0.51  % (12091)------------------------------
% 0.21/0.52  % (12094)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (12094)Refutation not found, incomplete strategy% (12094)------------------------------
% 0.21/0.52  % (12094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12094)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12094)Memory used [KB]: 1663
% 0.21/0.52  % (12094)Time elapsed: 0.077 s
% 0.21/0.52  % (12094)------------------------------
% 0.21/0.52  % (12094)------------------------------
% 0.21/0.52  % (12074)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (12076)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (12080)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (12074)Refutation not found, incomplete strategy% (12074)------------------------------
% 0.21/0.52  % (12074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12074)Memory used [KB]: 6268
% 0.21/0.52  % (12074)Time elapsed: 0.115 s
% 0.21/0.52  % (12074)------------------------------
% 0.21/0.52  % (12074)------------------------------
% 0.21/0.52  % (12086)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (12086)Refutation not found, incomplete strategy% (12086)------------------------------
% 0.21/0.53  % (12086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12086)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12086)Memory used [KB]: 6140
% 0.21/0.53  % (12086)Time elapsed: 0.001 s
% 0.21/0.53  % (12086)------------------------------
% 0.21/0.53  % (12086)------------------------------
% 0.21/0.53  % (12080)Refutation not found, incomplete strategy% (12080)------------------------------
% 0.21/0.53  % (12080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12080)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12080)Memory used [KB]: 10618
% 0.21/0.53  % (12080)Time elapsed: 0.113 s
% 0.21/0.53  % (12080)------------------------------
% 0.21/0.53  % (12080)------------------------------
% 0.21/0.53  % (12082)Refutation not found, incomplete strategy% (12082)------------------------------
% 0.21/0.53  % (12082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12082)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12082)Memory used [KB]: 6268
% 0.21/0.53  % (12082)Time elapsed: 0.062 s
% 0.21/0.53  % (12082)------------------------------
% 0.21/0.53  % (12082)------------------------------
% 0.21/0.53  % (12072)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (12069)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (12081)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (12069)Refutation not found, incomplete strategy% (12069)------------------------------
% 0.21/0.53  % (12069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12069)Memory used [KB]: 1663
% 0.21/0.53  % (12069)Time elapsed: 0.123 s
% 0.21/0.53  % (12069)------------------------------
% 0.21/0.53  % (12069)------------------------------
% 0.21/0.53  % (12088)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (12081)Refutation not found, incomplete strategy% (12081)------------------------------
% 0.21/0.53  % (12081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12081)Memory used [KB]: 10618
% 0.21/0.53  % (12081)Time elapsed: 0.121 s
% 0.21/0.53  % (12081)------------------------------
% 0.21/0.53  % (12081)------------------------------
% 0.21/0.53  % (12100)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (12070)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (12099)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (12095)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (12096)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (12093)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (12090)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (12092)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (12071)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (12092)Refutation not found, incomplete strategy% (12092)------------------------------
% 0.21/0.54  % (12092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12078)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (12097)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (12071)Refutation not found, incomplete strategy% (12071)------------------------------
% 0.21/0.54  % (12071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12072)Refutation not found, incomplete strategy% (12072)------------------------------
% 0.21/0.54  % (12072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (12076)# SZS output start Saturation.
% 0.21/0.54  cnf(u45,axiom,
% 0.21/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u24,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u36,axiom,
% 0.21/0.54      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u57,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u51,negated_conjecture,
% 0.21/0.54      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u52,axiom,
% 0.21/0.54      r1_tarski(X0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u42,axiom,
% 0.21/0.54      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u54,negated_conjecture,
% 0.21/0.54      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u100,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k5_xboole_0(u1_struct_0(sK0),sK1),sK1))).
% 0.21/0.54  
% 0.21/0.54  cnf(u53,axiom,
% 0.21/0.54      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u78,negated_conjecture,
% 0.21/0.54      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u62,axiom,
% 0.21/0.54      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u69,axiom,
% 0.21/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u59,negated_conjecture,
% 0.21/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u25,axiom,
% 0.21/0.54      k2_subset_1(X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u30,axiom,
% 0.21/0.54      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u72,negated_conjecture,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u22,negated_conjecture,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u71,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u70,axiom,
% 0.21/0.54      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u47,axiom,
% 0.21/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u40,axiom,
% 0.21/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u27,axiom,
% 0.21/0.54      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u94,axiom,
% 0.21/0.54      k5_xboole_0(k1_xboole_0,X0) = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u87,axiom,
% 0.21/0.54      k5_xboole_0(k1_setfam_1(k2_tarski(X1,X0)),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X1,X0)))) = X0).
% 0.21/0.54  
% 0.21/0.55  cnf(u68,axiom,
% 0.21/0.55      k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u56,axiom,
% 0.21/0.55      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u28,axiom,
% 0.21/0.55      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u44,negated_conjecture,
% 0.21/0.55      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.55  
% 0.21/0.55  % (12076)# SZS output end Saturation.
% 0.21/0.55  % (12076)------------------------------
% 0.21/0.55  % (12076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12076)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (12076)Memory used [KB]: 6268
% 0.21/0.55  % (12076)Time elapsed: 0.115 s
% 0.21/0.55  % (12076)------------------------------
% 0.21/0.55  % (12076)------------------------------
% 0.21/0.55  % (12065)Success in time 0.186 s
%------------------------------------------------------------------------------
