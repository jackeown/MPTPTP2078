%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:34 EST 2020

% Result     : CounterSatisfiable 1.87s
% Output     : Saturation 1.87s
% Verified   : 
% Statistics : Number of clauses        :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u27,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u39,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u114,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u41,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u35,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u117,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u115,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u116,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u88,axiom,
    ( k7_subset_1(X1,X1,X2) = k7_subset_1(k2_xboole_0(X2,X1),k2_xboole_0(X2,X1),X2) )).

cnf(u77,axiom,
    ( k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3) )).

cnf(u57,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u84,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u63,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

cnf(u18,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u56,axiom,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X0,X1)))) = k7_subset_1(X0,X0,X1) )).

cnf(u54,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u28,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u73,axiom,
    ( k7_subset_1(X1,X1,X2) = k5_xboole_0(k2_xboole_0(X2,X1),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X2,X1)))) )).

cnf(u79,axiom,
    ( k1_xboole_0 = k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X5))) )).

cnf(u58,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u29,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u62,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u22,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u24,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u45,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u25,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u38,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:10:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.57  % (7438)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (7430)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.58  % (7430)Refutation not found, incomplete strategy% (7430)------------------------------
% 0.22/0.58  % (7430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (7430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (7430)Memory used [KB]: 6140
% 0.22/0.58  % (7430)Time elapsed: 0.004 s
% 0.22/0.58  % (7430)------------------------------
% 0.22/0.58  % (7430)------------------------------
% 0.22/0.58  % (7438)Refutation not found, incomplete strategy% (7438)------------------------------
% 0.22/0.58  % (7438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (7438)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (7438)Memory used [KB]: 1791
% 1.49/0.58  % (7438)Time elapsed: 0.082 s
% 1.49/0.58  % (7438)------------------------------
% 1.49/0.58  % (7438)------------------------------
% 1.49/0.58  % (7422)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.58  % (7422)Refutation not found, incomplete strategy% (7422)------------------------------
% 1.49/0.58  % (7422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (7422)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (7422)Memory used [KB]: 6268
% 1.49/0.59  % (7422)Time elapsed: 0.078 s
% 1.49/0.59  % (7422)------------------------------
% 1.49/0.59  % (7422)------------------------------
% 1.49/0.59  % (7420)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.49/0.59  % (7416)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.60  % (7437)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.60  % (7415)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.87/0.61  % (7424)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.87/0.61  % (7421)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.87/0.61  % (7443)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.87/0.61  % (7427)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.87/0.61  % (7426)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.87/0.61  % (7425)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.87/0.61  % SZS status CounterSatisfiable for theBenchmark
% 1.87/0.61  % (7421)# SZS output start Saturation.
% 1.87/0.61  cnf(u21,negated_conjecture,
% 1.87/0.61      l1_struct_0(sK0)).
% 1.87/0.61  
% 1.87/0.61  cnf(u27,axiom,
% 1.87/0.61      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 1.87/0.61  
% 1.87/0.61  cnf(u39,axiom,
% 1.87/0.61      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.87/0.61  
% 1.87/0.61  cnf(u20,negated_conjecture,
% 1.87/0.61      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.87/0.61  
% 1.87/0.61  cnf(u114,negated_conjecture,
% 1.87/0.61      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 1.87/0.61  
% 1.87/0.61  cnf(u55,axiom,
% 1.87/0.61      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.87/0.61  
% 1.87/0.61  cnf(u41,axiom,
% 1.87/0.61      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 1.87/0.61  
% 1.87/0.61  cnf(u35,axiom,
% 1.87/0.61      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 1.87/0.61  
% 1.87/0.61  cnf(u117,negated_conjecture,
% 1.87/0.61      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 1.87/0.61  
% 1.87/0.61  cnf(u115,negated_conjecture,
% 1.87/0.61      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.87/0.61  
% 1.87/0.61  cnf(u116,negated_conjecture,
% 1.87/0.61      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 1.87/0.61  
% 1.87/0.61  cnf(u88,axiom,
% 1.87/0.61      k7_subset_1(X1,X1,X2) = k7_subset_1(k2_xboole_0(X2,X1),k2_xboole_0(X2,X1),X2)).
% 1.87/0.61  
% 1.87/0.61  cnf(u77,axiom,
% 1.87/0.61      k7_subset_1(X2,X2,X3) = k7_subset_1(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3),X3)).
% 1.87/0.61  
% 1.87/0.61  cnf(u57,negated_conjecture,
% 1.87/0.61      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.87/0.61  
% 1.87/0.61  cnf(u84,axiom,
% 1.87/0.61      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.87/0.61  
% 1.87/0.61  cnf(u63,axiom,
% 1.87/0.61      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)).
% 1.87/0.61  
% 1.87/0.61  cnf(u18,negated_conjecture,
% 1.87/0.61      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.87/0.61  
% 1.87/0.61  cnf(u56,axiom,
% 1.87/0.61      k5_xboole_0(k2_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X1,k2_xboole_0(X0,X1)))) = k7_subset_1(X0,X0,X1)).
% 1.87/0.61  
% 1.87/0.61  cnf(u54,axiom,
% 1.87/0.61      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.87/0.61  
% 1.87/0.61  cnf(u28,axiom,
% 1.87/0.61      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 1.87/0.61  
% 1.87/0.61  cnf(u73,axiom,
% 1.87/0.61      k7_subset_1(X1,X1,X2) = k5_xboole_0(k2_xboole_0(X2,X1),k1_setfam_1(k2_tarski(X2,k2_xboole_0(X2,X1))))).
% 1.87/0.61  
% 1.87/0.61  cnf(u79,axiom,
% 1.87/0.61      k1_xboole_0 = k5_xboole_0(X5,k1_setfam_1(k2_tarski(X5,X5)))).
% 1.87/0.61  
% 1.87/0.61  cnf(u58,axiom,
% 1.87/0.61      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 1.87/0.61  
% 1.87/0.61  cnf(u29,axiom,
% 1.87/0.61      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 1.87/0.61  
% 1.87/0.61  cnf(u62,axiom,
% 1.87/0.61      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.87/0.61  
% 1.87/0.61  cnf(u22,axiom,
% 1.87/0.61      k2_subset_1(X0) = X0).
% 1.87/0.61  
% 1.87/0.61  cnf(u24,axiom,
% 1.87/0.61      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.87/0.61  
% 1.87/0.61  cnf(u45,axiom,
% 1.87/0.61      k2_xboole_0(k1_xboole_0,X0) = X0).
% 1.87/0.61  
% 1.87/0.61  cnf(u25,axiom,
% 1.87/0.61      k2_xboole_0(X0,k1_xboole_0) = X0).
% 1.87/0.61  
% 1.87/0.61  cnf(u38,negated_conjecture,
% 1.87/0.61      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.87/0.61  
% 1.87/0.61  % (7421)# SZS output end Saturation.
% 1.87/0.61  % (7421)------------------------------
% 1.87/0.61  % (7421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (7421)Termination reason: Satisfiable
% 1.87/0.61  
% 1.87/0.61  % (7421)Memory used [KB]: 6268
% 1.87/0.61  % (7421)Time elapsed: 0.169 s
% 1.87/0.61  % (7421)------------------------------
% 1.87/0.61  % (7421)------------------------------
% 1.87/0.61  % (7420)Refutation not found, incomplete strategy% (7420)------------------------------
% 1.87/0.61  % (7420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (7420)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (7420)Memory used [KB]: 6268
% 1.87/0.61  % (7420)Time elapsed: 0.173 s
% 1.87/0.61  % (7420)------------------------------
% 1.87/0.61  % (7420)------------------------------
% 1.87/0.61  % (7426)Refutation not found, incomplete strategy% (7426)------------------------------
% 1.87/0.61  % (7426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (7426)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (7426)Memory used [KB]: 10618
% 1.87/0.61  % (7426)Time elapsed: 0.167 s
% 1.87/0.61  % (7426)------------------------------
% 1.87/0.61  % (7426)------------------------------
% 1.87/0.61  % (7414)Success in time 0.241 s
%------------------------------------------------------------------------------
