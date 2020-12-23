%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:42 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :   46 (  46 expanded)
%              Number of equality atoms :   29 (  29 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u31,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u46,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u56,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u45,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u42,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u54,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 )).

cnf(u40,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u35,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u38,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u75,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = sK1 )).

cnf(u57,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u49,negated_conjecture,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u61,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u55,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u28,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u66,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u29,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u67,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u65,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u30,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u52,axiom,
    ( k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u48,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u74,axiom,
    ( k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k3_xboole_0(X0,X1))) )).

cnf(u34,axiom,
    ( k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )).

cnf(u32,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u59,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u51,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u33,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u25,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (26971)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (26963)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (26963)Refutation not found, incomplete strategy% (26963)------------------------------
% 0.21/0.52  % (26963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26983)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (26965)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (26963)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26963)Memory used [KB]: 1663
% 0.21/0.52  % (26963)Time elapsed: 0.100 s
% 0.21/0.52  % (26963)------------------------------
% 0.21/0.52  % (26963)------------------------------
% 0.21/0.53  % (26966)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (26967)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (26964)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (26968)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (26969)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (26977)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (26989)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (26988)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (26984)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (26987)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (26986)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (26988)Refutation not found, incomplete strategy% (26988)------------------------------
% 0.21/0.54  % (26988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26988)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26988)Memory used [KB]: 6268
% 0.21/0.54  % (26988)Time elapsed: 0.141 s
% 0.21/0.54  % (26988)------------------------------
% 0.21/0.54  % (26988)------------------------------
% 0.21/0.54  % (26985)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (26981)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (26980)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (26979)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (26980)Refutation not found, incomplete strategy% (26980)------------------------------
% 0.21/0.54  % (26980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26980)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26980)Memory used [KB]: 1663
% 0.21/0.54  % (26980)Time elapsed: 0.140 s
% 0.21/0.54  % (26980)------------------------------
% 0.21/0.54  % (26980)------------------------------
% 0.21/0.54  % (26973)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (26978)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (26979)Refutation not found, incomplete strategy% (26979)------------------------------
% 0.21/0.55  % (26979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26979)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26979)Memory used [KB]: 1791
% 0.21/0.55  % (26979)Time elapsed: 0.139 s
% 0.21/0.55  % (26979)------------------------------
% 0.21/0.55  % (26979)------------------------------
% 0.21/0.55  % (26978)Refutation not found, incomplete strategy% (26978)------------------------------
% 0.21/0.55  % (26978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26978)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26978)Memory used [KB]: 10618
% 0.21/0.55  % (26978)Time elapsed: 0.137 s
% 0.21/0.55  % (26978)------------------------------
% 0.21/0.55  % (26978)------------------------------
% 0.21/0.55  % (26975)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (26974)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (26976)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (26976)Refutation not found, incomplete strategy% (26976)------------------------------
% 0.21/0.55  % (26976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26976)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26976)Memory used [KB]: 1663
% 0.21/0.55  % (26976)Time elapsed: 0.149 s
% 0.21/0.55  % (26976)------------------------------
% 0.21/0.55  % (26976)------------------------------
% 0.21/0.55  % (26974)Refutation not found, incomplete strategy% (26974)------------------------------
% 0.21/0.55  % (26974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26974)Memory used [KB]: 10618
% 0.21/0.55  % (26974)Time elapsed: 0.151 s
% 0.21/0.55  % (26974)------------------------------
% 0.21/0.55  % (26974)------------------------------
% 0.21/0.55  % (26972)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (26972)Refutation not found, incomplete strategy% (26972)------------------------------
% 0.21/0.55  % (26972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26972)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26972)Memory used [KB]: 10746
% 0.21/0.55  % (26972)Time elapsed: 0.149 s
% 0.21/0.55  % (26972)------------------------------
% 0.21/0.55  % (26972)------------------------------
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (26969)# SZS output start Saturation.
% 0.21/0.55  cnf(u23,negated_conjecture,
% 0.21/0.55      l1_struct_0(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u31,axiom,
% 0.21/0.55      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u46,axiom,
% 0.21/0.55      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u24,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u56,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u39,axiom,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u41,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u45,negated_conjecture,
% 0.21/0.55      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u42,axiom,
% 0.21/0.55      r1_tarski(X1,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u54,negated_conjecture,
% 0.21/0.55      ~r1_tarski(u1_struct_0(sK0),sK1) | u1_struct_0(sK0) = sK1).
% 0.21/0.55  
% 0.21/0.55  cnf(u40,axiom,
% 0.21/0.55      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u35,axiom,
% 0.21/0.55      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u38,axiom,
% 0.21/0.55      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u75,negated_conjecture,
% 0.21/0.55      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = sK1).
% 0.21/0.55  
% 0.21/0.55  cnf(u57,negated_conjecture,
% 0.21/0.55      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u49,negated_conjecture,
% 0.21/0.55      sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u61,negated_conjecture,
% 0.21/0.55      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u55,negated_conjecture,
% 0.21/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u28,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.21/0.55  
% 0.21/0.55  cnf(u66,axiom,
% 0.21/0.55      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u29,axiom,
% 0.21/0.55      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u67,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u65,axiom,
% 0.21/0.55      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u30,axiom,
% 0.21/0.55      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u52,axiom,
% 0.21/0.55      k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u48,axiom,
% 0.21/0.55      k3_xboole_0(X0,X0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u74,axiom,
% 0.21/0.55      k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k3_xboole_0(X0,X1)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u34,axiom,
% 0.21/0.55      k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u32,axiom,
% 0.21/0.55      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u59,axiom,
% 0.21/0.55      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u51,axiom,
% 0.21/0.55      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u33,axiom,
% 0.21/0.55      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u25,negated_conjecture,
% 0.21/0.55      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1).
% 0.21/0.55  
% 0.21/0.55  % (26969)# SZS output end Saturation.
% 0.21/0.55  % (26969)------------------------------
% 0.21/0.55  % (26969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26969)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (26969)Memory used [KB]: 1791
% 0.21/0.55  % (26969)Time elapsed: 0.097 s
% 0.21/0.55  % (26969)------------------------------
% 0.21/0.55  % (26969)------------------------------
% 0.21/0.56  % (26961)Success in time 0.192 s
%------------------------------------------------------------------------------
