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
% DateTime   : Thu Dec  3 13:08:56 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   51 (  51 expanded)
%              Number of leaves         :   51 (  51 expanded)
%              Depth                    :    0
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :   47 (  47 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u47,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u107,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u108,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u71,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u109,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3) )).

cnf(u25,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u75,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_tarski(k2_tarski(k7_subset_1(X2,X2,X0),X1)) = k7_subset_1(k3_tarski(k2_tarski(X2,X1)),k3_tarski(k2_tarski(X2,X1)),X0) )).

cnf(u160,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u156,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u74,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u73,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u158,negated_conjecture,
    ( k4_subset_1(sK2,sK2,sK2) = k7_subset_1(k4_subset_1(sK2,sK2,sK2),k4_subset_1(sK2,sK2,sK2),sK1) )).

cnf(u150,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) = k7_subset_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK2,X0)),sK1) )).

cnf(u116,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u115,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u139,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0)) )).

cnf(u83,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2))) )).

cnf(u82,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) )).

cnf(u84,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X6) )).

cnf(u90,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u70,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u129,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u24,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u135,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

cnf(u134,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

cnf(u132,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u131,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u133,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

cnf(u136,axiom,
    ( k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) )).

cnf(u124,negated_conjecture,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) )).

cnf(u130,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u114,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u113,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u33,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u79,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u117,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) )).

cnf(u118,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) )).

cnf(u57,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )).

cnf(u55,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1))) )).

cnf(u56,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u141,axiom,
    ( k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k4_subset_1(X2,X2,X2)))) )).

cnf(u52,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))) )).

cnf(u43,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )).

cnf(u42,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u48,axiom,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

cnf(u41,axiom,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 )).

cnf(u28,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u26,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:42:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (15443)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (15435)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (15414)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (15427)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (15420)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (15416)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (15425)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (15425)Refutation not found, incomplete strategy% (15425)------------------------------
% 0.22/0.53  % (15425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15425)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15425)Memory used [KB]: 10746
% 0.22/0.53  % (15425)Time elapsed: 0.123 s
% 0.22/0.53  % (15425)------------------------------
% 0.22/0.53  % (15425)------------------------------
% 0.22/0.54  % (15437)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (15417)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (15423)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (15436)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (15430)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (15442)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (15429)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (15415)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (15429)Refutation not found, incomplete strategy% (15429)------------------------------
% 0.22/0.54  % (15429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15429)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15429)Memory used [KB]: 6140
% 0.22/0.54  % (15429)Time elapsed: 0.002 s
% 0.22/0.54  % (15429)------------------------------
% 0.22/0.54  % (15429)------------------------------
% 0.22/0.54  % (15414)Refutation not found, incomplete strategy% (15414)------------------------------
% 0.22/0.54  % (15414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15414)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15414)Memory used [KB]: 1663
% 0.22/0.54  % (15414)Time elapsed: 0.134 s
% 0.22/0.54  % (15414)------------------------------
% 0.22/0.54  % (15414)------------------------------
% 0.22/0.54  % (15418)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (15419)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (15428)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.55  % (15431)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (15421)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (15422)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (15438)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (15433)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (15441)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (15439)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (15426)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (15420)# SZS output start Saturation.
% 0.22/0.56  cnf(u47,axiom,
% 0.22/0.56      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u27,negated_conjecture,
% 0.22/0.56      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u23,negated_conjecture,
% 0.22/0.56      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u107,negated_conjecture,
% 0.22/0.56      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 0.22/0.56  
% 0.22/0.56  cnf(u108,negated_conjecture,
% 0.22/0.56      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 0.22/0.56  
% 0.22/0.56  cnf(u71,axiom,
% 0.22/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u46,axiom,
% 0.22/0.56      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 0.22/0.56  
% 0.22/0.56  cnf(u109,axiom,
% 0.22/0.56      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3)).
% 0.22/0.56  
% 0.22/0.56  cnf(u25,negated_conjecture,
% 0.22/0.56      r1_xboole_0(sK1,sK2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u75,axiom,
% 0.22/0.56      ~r1_xboole_0(X0,X1) | k3_tarski(k2_tarski(k7_subset_1(X2,X2,X0),X1)) = k7_subset_1(k3_tarski(k2_tarski(X2,X1)),k3_tarski(k2_tarski(X2,X1)),X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u160,negated_conjecture,
% 0.22/0.56      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u156,negated_conjecture,
% 0.22/0.56      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u74,negated_conjecture,
% 0.22/0.56      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u73,negated_conjecture,
% 0.22/0.56      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u158,negated_conjecture,
% 0.22/0.56      k4_subset_1(sK2,sK2,sK2) = k7_subset_1(k4_subset_1(sK2,sK2,sK2),k4_subset_1(sK2,sK2,sK2),sK1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u150,negated_conjecture,
% 0.22/0.56      k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) = k7_subset_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK2,X0)),sK1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u116,negated_conjecture,
% 0.22/0.56      k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u115,negated_conjecture,
% 0.22/0.56      k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u139,axiom,
% 0.22/0.56      k1_xboole_0 = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u83,axiom,
% 0.22/0.56      k1_xboole_0 = k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u82,axiom,
% 0.22/0.56      k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u84,axiom,
% 0.22/0.56      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X6)).
% 0.22/0.56  
% 0.22/0.56  cnf(u90,axiom,
% 0.22/0.56      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u70,axiom,
% 0.22/0.56      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u129,negated_conjecture,
% 0.22/0.56      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u24,negated_conjecture,
% 0.22/0.56      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u135,negated_conjecture,
% 0.22/0.56      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)).
% 0.22/0.56  
% 0.22/0.56  cnf(u134,negated_conjecture,
% 0.22/0.56      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)).
% 0.22/0.56  
% 0.22/0.56  cnf(u132,negated_conjecture,
% 0.22/0.56      k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u131,negated_conjecture,
% 0.22/0.56      k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.22/0.56  
% 0.22/0.56  cnf(u133,axiom,
% 0.22/0.56      k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u136,axiom,
% 0.22/0.56      k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u124,negated_conjecture,
% 0.22/0.56      k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u130,negated_conjecture,
% 0.22/0.56      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u114,negated_conjecture,
% 0.22/0.56      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u113,negated_conjecture,
% 0.22/0.56      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 0.22/0.56  
% 0.22/0.56  cnf(u33,axiom,
% 0.22/0.56      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u79,axiom,
% 0.22/0.56      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u117,negated_conjecture,
% 0.22/0.56      k1_xboole_0 = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))).
% 0.22/0.56  
% 0.22/0.56  cnf(u118,negated_conjecture,
% 0.22/0.56      k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))))).
% 0.22/0.56  
% 0.22/0.56  cnf(u57,axiom,
% 0.22/0.56      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u55,axiom,
% 0.22/0.56      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))).
% 0.22/0.56  
% 0.22/0.56  cnf(u56,axiom,
% 0.22/0.56      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.22/0.56  
% 0.22/0.56  cnf(u141,axiom,
% 0.22/0.56      k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k4_subset_1(X2,X2,X2))))).
% 0.22/0.56  
% 0.22/0.56  cnf(u52,axiom,
% 0.22/0.56      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))))).
% 0.22/0.56  
% 0.22/0.56  cnf(u43,axiom,
% 0.22/0.56      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))).
% 0.22/0.56  
% 0.22/0.56  cnf(u42,axiom,
% 0.22/0.56      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.22/0.56  
% 0.22/0.56  cnf(u48,axiom,
% 0.22/0.56      k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0).
% 0.22/0.56  
% 0.22/0.56  cnf(u41,axiom,
% 0.22/0.56      k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0).
% 0.22/0.56  
% 0.22/0.56  cnf(u28,axiom,
% 0.22/0.56      k2_subset_1(X0) = X0).
% 0.22/0.56  
% 0.22/0.56  cnf(u26,negated_conjecture,
% 0.22/0.56      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.22/0.56  
% 0.22/0.56  % (15420)# SZS output end Saturation.
% 0.22/0.56  % (15420)------------------------------
% 0.22/0.56  % (15420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15420)Termination reason: Satisfiable
% 0.22/0.56  
% 0.22/0.56  % (15420)Memory used [KB]: 6396
% 0.22/0.56  % (15420)Time elapsed: 0.117 s
% 0.22/0.56  % (15420)------------------------------
% 0.22/0.56  % (15420)------------------------------
% 0.22/0.56  % (15413)Success in time 0.194 s
%------------------------------------------------------------------------------
