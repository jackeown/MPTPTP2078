%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:46 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u45,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u46,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u47,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u55,axiom,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = X1 )).

cnf(u39,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u85,axiom,
    ( k1_setfam_1(k2_tarski(X2,k7_subset_1(X2,X2,X3))) = k7_subset_1(X2,X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u71,axiom,
    ( k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3)) )).

cnf(u57,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u75,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u22,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u53,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u89,axiom,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1)))) )).

cnf(u74,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u58,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u40,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u65,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u25,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u27,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u44,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (23360)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (23368)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (23360)Refutation not found, incomplete strategy% (23360)------------------------------
% 0.20/0.50  % (23360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23360)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (23360)Memory used [KB]: 10746
% 0.20/0.50  % (23360)Time elapsed: 0.073 s
% 0.20/0.50  % (23360)------------------------------
% 0.20/0.50  % (23360)------------------------------
% 0.20/0.52  % (23352)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (23355)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (23366)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (23357)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (23357)Refutation not found, incomplete strategy% (23357)------------------------------
% 0.20/0.53  % (23357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23357)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23357)Memory used [KB]: 6268
% 0.20/0.53  % (23357)Time elapsed: 0.116 s
% 0.20/0.53  % (23357)------------------------------
% 0.20/0.53  % (23357)------------------------------
% 0.20/0.54  % (23356)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (23353)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (23356)Refutation not found, incomplete strategy% (23356)------------------------------
% 0.20/0.54  % (23356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23356)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23356)Memory used [KB]: 6140
% 0.20/0.54  % (23356)Time elapsed: 0.130 s
% 0.20/0.54  % (23356)------------------------------
% 0.20/0.54  % (23356)------------------------------
% 0.20/0.54  % (23358)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.54  % (23358)# SZS output start Saturation.
% 0.20/0.54  cnf(u45,axiom,
% 0.20/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u24,negated_conjecture,
% 0.20/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u35,axiom,
% 0.20/0.54      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u54,axiom,
% 0.20/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u46,negated_conjecture,
% 0.20/0.54      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u47,axiom,
% 0.20/0.54      r1_tarski(X0,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u55,axiom,
% 0.20/0.54      ~r1_tarski(X0,X1) | k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = X1).
% 0.20/0.54  
% 0.20/0.54  cnf(u39,axiom,
% 0.20/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.20/0.54  
% 0.20/0.54  cnf(u85,axiom,
% 0.20/0.54      k1_setfam_1(k2_tarski(X2,k7_subset_1(X2,X2,X3))) = k7_subset_1(X2,X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 0.20/0.54  
% 0.20/0.54  cnf(u71,axiom,
% 0.20/0.54      k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3))).
% 0.20/0.54  
% 0.20/0.54  cnf(u57,negated_conjecture,
% 0.20/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u75,axiom,
% 0.20/0.54      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u22,negated_conjecture,
% 0.20/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u53,axiom,
% 0.20/0.54      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u89,axiom,
% 0.20/0.54      k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1))))).
% 0.20/0.54  
% 0.20/0.54  cnf(u74,axiom,
% 0.20/0.54      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u58,negated_conjecture,
% 0.20/0.54      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.20/0.54  
% 0.20/0.54  cnf(u40,axiom,
% 0.20/0.54      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u65,axiom,
% 0.20/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u25,axiom,
% 0.20/0.54      k2_subset_1(X0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u27,axiom,
% 0.20/0.54      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.54  
% 0.20/0.54  cnf(u44,negated_conjecture,
% 0.20/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.54  
% 0.20/0.54  % (23358)# SZS output end Saturation.
% 0.20/0.54  % (23358)------------------------------
% 0.20/0.54  % (23358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23358)Termination reason: Satisfiable
% 0.20/0.54  
% 0.20/0.54  % (23358)Memory used [KB]: 6268
% 0.20/0.54  % (23358)Time elapsed: 0.111 s
% 0.20/0.54  % (23358)------------------------------
% 0.20/0.54  % (23358)------------------------------
% 0.20/0.54  % (23354)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (23379)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (23367)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (23367)Refutation not found, incomplete strategy% (23367)------------------------------
% 0.20/0.54  % (23367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23367)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23367)Memory used [KB]: 6140
% 0.20/0.54  % (23367)Time elapsed: 0.001 s
% 0.20/0.54  % (23367)------------------------------
% 0.20/0.54  % (23367)------------------------------
% 0.20/0.54  % (23374)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (23352)Refutation not found, incomplete strategy% (23352)------------------------------
% 0.20/0.54  % (23352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23352)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23352)Memory used [KB]: 1663
% 0.20/0.54  % (23352)Time elapsed: 0.144 s
% 0.20/0.54  % (23352)------------------------------
% 0.20/0.54  % (23352)------------------------------
% 0.20/0.55  % (23371)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (23374)Refutation not found, incomplete strategy% (23374)------------------------------
% 0.20/0.55  % (23374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23374)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (23374)Memory used [KB]: 10618
% 0.20/0.55  % (23374)Time elapsed: 0.115 s
% 0.20/0.55  % (23374)------------------------------
% 0.20/0.55  % (23374)------------------------------
% 0.20/0.55  % (23380)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (23373)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (23355)Refutation not found, incomplete strategy% (23355)------------------------------
% 0.20/0.55  % (23355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23355)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (23355)Memory used [KB]: 10746
% 0.20/0.55  % (23355)Time elapsed: 0.127 s
% 0.20/0.55  % (23355)------------------------------
% 0.20/0.55  % (23355)------------------------------
% 0.20/0.55  % (23365)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (23370)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (23363)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (23376)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (23351)Success in time 0.197 s
%------------------------------------------------------------------------------
