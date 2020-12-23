%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:56 EST 2020

% Result     : CounterSatisfiable 1.37s
% Output     : Saturation 1.37s
% Verified   : 
% Statistics : Number of clauses        :   52 (  52 expanded)
%              Number of leaves         :   52 (  52 expanded)
%              Depth                    :    0
%              Number of atoms          :   64 (  64 expanded)
%              Number of equality atoms :   51 (  51 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u45,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u83,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u84,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u63,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u85,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3) )).

cnf(u42,axiom,
    ( r1_xboole_0(X0,X1)
    | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u23,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u41,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u49,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 )).

cnf(u104,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u96,negated_conjecture,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) )).

cnf(u98,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u101,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u97,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) )).

cnf(u90,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u89,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u109,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u22,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u120,axiom,
    ( k1_setfam_1(k2_tarski(X4,k4_subset_1(X4,X4,X4))) = X4 )).

cnf(u47,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 )).

cnf(u39,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 )).

cnf(u78,negated_conjecture,
    ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) )).

cnf(u71,axiom,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0) )).

cnf(u69,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u73,negated_conjecture,
    ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) )).

cnf(u65,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u64,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u115,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

cnf(u114,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

cnf(u110,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u91,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u26,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u112,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u111,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u113,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

cnf(u28,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u92,negated_conjecture,
    ( k5_xboole_0(sK2,sK2) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u93,negated_conjecture,
    ( k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u123,axiom,
    ( k5_xboole_0(k4_subset_1(X0,X0,X0),X0) = k7_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),X0) )).

cnf(u118,axiom,
    ( k5_xboole_0(k4_subset_1(X2,X2,X2),X2) = X2
    | k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X2)) )).

cnf(u77,axiom,
    ( k5_xboole_0(k3_tarski(k2_tarski(X3,X2)),X2) = k7_subset_1(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X3,X2)),X2) )).

cnf(u76,axiom,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) )).

cnf(u56,axiom,
    ( k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) = X0
    | k1_xboole_0 != k1_setfam_1(k2_tarski(X1,X0)) )).

cnf(u55,axiom,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
    | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u116,axiom,
    ( k5_xboole_0(X0,X0) = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0)) )).

cnf(u72,axiom,
    ( k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2))) = k5_xboole_0(X2,X2) )).

cnf(u62,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u50,negated_conjecture,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2)) )).

cnf(u24,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (28301)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (28293)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (28301)Refutation not found, incomplete strategy% (28301)------------------------------
% 0.21/0.50  % (28301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28301)Memory used [KB]: 10746
% 0.21/0.50  % (28301)Time elapsed: 0.036 s
% 0.21/0.50  % (28301)------------------------------
% 0.21/0.50  % (28301)------------------------------
% 1.13/0.52  % (28284)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.13/0.52  % (28291)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.13/0.52  % (28285)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.13/0.52  % (28280)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.13/0.53  % (28283)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.13/0.53  % (28283)Refutation not found, incomplete strategy% (28283)------------------------------
% 1.13/0.53  % (28283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.53  % (28283)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.53  
% 1.13/0.53  % (28283)Memory used [KB]: 6268
% 1.13/0.53  % (28283)Time elapsed: 0.118 s
% 1.13/0.53  % (28283)------------------------------
% 1.13/0.53  % (28283)------------------------------
% 1.13/0.53  % (28282)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.13/0.53  % (28281)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.13/0.53  % (28281)Refutation not found, incomplete strategy% (28281)------------------------------
% 1.13/0.53  % (28281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.53  % (28281)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.53  
% 1.13/0.53  % (28281)Memory used [KB]: 10746
% 1.13/0.53  % (28281)Time elapsed: 0.115 s
% 1.13/0.53  % (28281)------------------------------
% 1.13/0.53  % (28281)------------------------------
% 1.13/0.53  % (28292)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.13/0.54  % (28308)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.13/0.54  % (28296)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.13/0.54  % (28296)Refutation not found, incomplete strategy% (28296)------------------------------
% 1.13/0.54  % (28296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.54  % (28296)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.54  
% 1.13/0.54  % (28296)Memory used [KB]: 10618
% 1.13/0.54  % (28296)Time elapsed: 0.127 s
% 1.13/0.54  % (28296)------------------------------
% 1.13/0.54  % (28296)------------------------------
% 1.13/0.54  % (28298)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.13/0.54  % (28297)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.13/0.54  % (28300)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.13/0.54  % (28287)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.13/0.54  % (28284)Refutation not found, incomplete strategy% (28284)------------------------------
% 1.13/0.54  % (28284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.54  % (28284)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.54  
% 1.13/0.54  % (28284)Memory used [KB]: 6268
% 1.13/0.54  % (28284)Time elapsed: 0.110 s
% 1.13/0.54  % (28284)------------------------------
% 1.13/0.54  % (28284)------------------------------
% 1.13/0.54  % (28291)Refutation not found, incomplete strategy% (28291)------------------------------
% 1.13/0.54  % (28291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (28288)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.54  % (28279)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.55  % (28299)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.37/0.55  % (28285)# SZS output start Saturation.
% 1.37/0.55  cnf(u45,axiom,
% 1.37/0.55      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.37/0.55  
% 1.37/0.55  cnf(u25,negated_conjecture,
% 1.37/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.37/0.55  
% 1.37/0.55  cnf(u21,negated_conjecture,
% 1.37/0.55      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.37/0.55  
% 1.37/0.55  cnf(u83,negated_conjecture,
% 1.37/0.55      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 1.37/0.55  
% 1.37/0.55  cnf(u84,negated_conjecture,
% 1.37/0.55      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 1.37/0.55  
% 1.37/0.55  cnf(u63,axiom,
% 1.37/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.37/0.55  
% 1.37/0.55  cnf(u44,axiom,
% 1.37/0.55      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 1.37/0.55  
% 1.37/0.55  cnf(u85,axiom,
% 1.37/0.55      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3)).
% 1.37/0.55  
% 1.37/0.55  cnf(u42,axiom,
% 1.37/0.55      r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))).
% 1.37/0.55  
% 1.37/0.55  cnf(u23,negated_conjecture,
% 1.37/0.55      r1_xboole_0(sK1,sK2)).
% 1.37/0.55  
% 1.37/0.55  cnf(u41,axiom,
% 1.37/0.55      ~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))).
% 1.37/0.55  
% 1.37/0.55  cnf(u49,axiom,
% 1.37/0.55      ~r1_xboole_0(X0,X1) | k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0).
% 1.37/0.55  
% 1.37/0.55  cnf(u104,negated_conjecture,
% 1.37/0.55      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.37/0.55  
% 1.37/0.55  cnf(u96,negated_conjecture,
% 1.37/0.55      sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))).
% 1.37/0.55  
% 1.37/0.55  cnf(u98,negated_conjecture,
% 1.37/0.55      sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)).
% 1.37/0.55  
% 1.37/0.55  cnf(u101,negated_conjecture,
% 1.37/0.55      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 1.37/0.55  
% 1.37/0.55  cnf(u97,negated_conjecture,
% 1.37/0.55      sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))).
% 1.37/0.55  
% 1.37/0.55  cnf(u90,negated_conjecture,
% 1.37/0.55      sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)).
% 1.37/0.55  
% 1.37/0.55  cnf(u89,negated_conjecture,
% 1.37/0.55      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 1.37/0.55  
% 1.37/0.55  cnf(u109,negated_conjecture,
% 1.37/0.55      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 1.37/0.55  
% 1.37/0.55  cnf(u22,negated_conjecture,
% 1.37/0.55      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 1.37/0.55  
% 1.37/0.55  cnf(u120,axiom,
% 1.37/0.55      k1_setfam_1(k2_tarski(X4,k4_subset_1(X4,X4,X4))) = X4).
% 1.37/0.55  
% 1.37/0.55  cnf(u47,axiom,
% 1.37/0.55      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0).
% 1.37/0.55  
% 1.37/0.55  cnf(u39,axiom,
% 1.37/0.55      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0).
% 1.37/0.55  
% 1.37/0.55  cnf(u78,negated_conjecture,
% 1.37/0.55      k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0)).
% 1.37/0.55  
% 1.37/0.55  cnf(u71,axiom,
% 1.37/0.55      k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0)).
% 1.37/0.55  
% 1.37/0.55  cnf(u69,axiom,
% 1.37/0.55      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 1.37/0.55  
% 1.37/0.55  cnf(u73,negated_conjecture,
% 1.37/0.55      k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0)).
% 1.37/0.55  
% 1.37/0.55  cnf(u65,negated_conjecture,
% 1.37/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 1.37/0.55  
% 1.37/0.55  cnf(u64,negated_conjecture,
% 1.37/0.55      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 1.37/0.55  
% 1.37/0.55  cnf(u115,negated_conjecture,
% 1.37/0.55      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)).
% 1.37/0.55  
% 1.37/0.55  cnf(u114,negated_conjecture,
% 1.37/0.55      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)).
% 1.37/0.55  
% 1.37/0.55  cnf(u110,negated_conjecture,
% 1.37/0.55      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 1.37/0.55  
% 1.37/0.55  cnf(u91,negated_conjecture,
% 1.37/0.55      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 1.37/0.55  
% 1.37/0.55  cnf(u26,axiom,
% 1.37/0.55      k2_subset_1(X0) = X0).
% 1.37/0.55  
% 1.37/0.55  cnf(u112,negated_conjecture,
% 1.37/0.55      k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.37/0.55  
% 1.37/0.55  cnf(u111,negated_conjecture,
% 1.37/0.55      k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 1.37/0.55  
% 1.37/0.55  cnf(u113,axiom,
% 1.37/0.55      k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0)).
% 1.37/0.55  
% 1.37/0.55  cnf(u28,axiom,
% 1.37/0.55      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 1.37/0.55  
% 1.37/0.55  cnf(u92,negated_conjecture,
% 1.37/0.55      k5_xboole_0(sK2,sK2) = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 1.37/0.55  
% 1.37/0.55  cnf(u93,negated_conjecture,
% 1.37/0.55      k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 1.37/0.55  
% 1.37/0.55  cnf(u123,axiom,
% 1.37/0.55      k5_xboole_0(k4_subset_1(X0,X0,X0),X0) = k7_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),X0)).
% 1.37/0.55  
% 1.37/0.55  cnf(u118,axiom,
% 1.37/0.55      k5_xboole_0(k4_subset_1(X2,X2,X2),X2) = X2 | k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X2))).
% 1.37/0.55  
% 1.37/0.55  cnf(u77,axiom,
% 1.37/0.55      k5_xboole_0(k3_tarski(k2_tarski(X3,X2)),X2) = k7_subset_1(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X3,X2)),X2)).
% 1.37/0.55  
% 1.37/0.55  cnf(u76,axiom,
% 1.37/0.55      k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0)).
% 1.37/0.55  
% 1.37/0.55  cnf(u56,axiom,
% 1.37/0.55      k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) = X0 | k1_xboole_0 != k1_setfam_1(k2_tarski(X1,X0))).
% 1.37/0.55  
% 1.37/0.55  cnf(u55,axiom,
% 1.37/0.55      k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))).
% 1.37/0.55  
% 1.37/0.55  cnf(u116,axiom,
% 1.37/0.55      k5_xboole_0(X0,X0) = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0))).
% 1.37/0.55  
% 1.37/0.55  cnf(u72,axiom,
% 1.37/0.55      k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2))) = k5_xboole_0(X2,X2)).
% 1.37/0.55  
% 1.37/0.55  cnf(u62,axiom,
% 1.37/0.55      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 1.37/0.55  
% 1.37/0.55  cnf(u50,negated_conjecture,
% 1.37/0.55      k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2))).
% 1.37/0.55  
% 1.37/0.55  cnf(u24,negated_conjecture,
% 1.37/0.55      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.37/0.55  
% 1.37/0.55  % (28285)# SZS output end Saturation.
% 1.37/0.55  % (28285)------------------------------
% 1.37/0.55  % (28285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (28285)Termination reason: Satisfiable
% 1.37/0.55  
% 1.37/0.55  % (28285)Memory used [KB]: 6268
% 1.37/0.55  % (28285)Time elapsed: 0.108 s
% 1.37/0.55  % (28285)------------------------------
% 1.37/0.55  % (28285)------------------------------
% 1.37/0.55  % (28290)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.55  % (28278)Success in time 0.18 s
%------------------------------------------------------------------------------
