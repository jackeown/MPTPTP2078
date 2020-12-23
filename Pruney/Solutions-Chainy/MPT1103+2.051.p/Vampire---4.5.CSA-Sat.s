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
% DateTime   : Thu Dec  3 13:08:41 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u61,axiom,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) )).

cnf(u45,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u66,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
    | ~ l1_struct_0(X0) )).

cnf(u68,axiom,
    ( r1_tarski(X0,X1)
    | k1_xboole_0 != k7_subset_1(X0,X0,X1) )).

cnf(u42,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u37,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u37_001,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u69,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_xboole_0 = k7_subset_1(X0,X0,X1) )).

cnf(u65,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = sK1 )).

cnf(u64,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u86,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u75,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u70,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u38,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u58,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

cnf(u31,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u49,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

cnf(u32,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u72,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u26,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u63,negated_conjecture,
    ( k2_struct_0(sK0) != sK1 )).

cnf(u59,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))
    | k2_struct_0(sK0) != sK1 )).

cnf(u67,axiom,
    ( k1_xboole_0 != k7_subset_1(X2,X2,X3)
    | ~ r1_tarski(X3,X2)
    | X2 = X3 )).

cnf(u44,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k2_struct_0(sK0) != sK1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (15544)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.50  % (15560)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.50  % (15560)Refutation not found, incomplete strategy% (15560)------------------------------
% 0.22/0.50  % (15560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15560)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (15560)Memory used [KB]: 6140
% 0.22/0.50  % (15560)Time elapsed: 0.096 s
% 0.22/0.50  % (15560)------------------------------
% 0.22/0.50  % (15560)------------------------------
% 0.22/0.50  % (15544)Refutation not found, incomplete strategy% (15544)------------------------------
% 0.22/0.50  % (15544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15544)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (15544)Memory used [KB]: 6140
% 0.22/0.50  % (15544)Time elapsed: 0.094 s
% 0.22/0.50  % (15544)------------------------------
% 0.22/0.50  % (15544)------------------------------
% 0.22/0.51  % (15535)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (15552)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.51  % (15547)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (15542)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (15547)Refutation not found, incomplete strategy% (15547)------------------------------
% 0.22/0.51  % (15547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15547)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15547)Memory used [KB]: 1663
% 0.22/0.51  % (15547)Time elapsed: 0.064 s
% 0.22/0.51  % (15547)------------------------------
% 0.22/0.51  % (15547)------------------------------
% 0.22/0.51  % (15537)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (15542)Refutation not found, incomplete strategy% (15542)------------------------------
% 0.22/0.51  % (15542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15542)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15542)Memory used [KB]: 1791
% 0.22/0.51  % (15542)Time elapsed: 0.098 s
% 0.22/0.51  % (15542)------------------------------
% 0.22/0.51  % (15542)------------------------------
% 0.22/0.51  % (15543)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (15539)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (15543)Refutation not found, incomplete strategy% (15543)------------------------------
% 0.22/0.52  % (15543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15543)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15543)Memory used [KB]: 10746
% 0.22/0.52  % (15543)Time elapsed: 0.107 s
% 0.22/0.52  % (15543)------------------------------
% 0.22/0.52  % (15543)------------------------------
% 0.22/0.52  % (15533)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (15550)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (15550)Refutation not found, incomplete strategy% (15550)------------------------------
% 0.22/0.52  % (15550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15550)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15550)Memory used [KB]: 1663
% 0.22/0.52  % (15550)Time elapsed: 0.110 s
% 0.22/0.52  % (15550)------------------------------
% 0.22/0.52  % (15550)------------------------------
% 0.22/0.52  % (15548)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (15552)Refutation not found, incomplete strategy% (15552)------------------------------
% 0.22/0.52  % (15552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15538)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (15553)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (15552)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (15552)Memory used [KB]: 1791
% 0.22/0.52  % (15552)Time elapsed: 0.107 s
% 0.22/0.52  % (15552)------------------------------
% 0.22/0.52  % (15552)------------------------------
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (15538)# SZS output start Saturation.
% 0.22/0.52  cnf(u21,negated_conjecture,
% 0.22/0.52      l1_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u61,axiom,
% 0.22/0.52      ~l1_struct_0(X0) | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))).
% 0.22/0.52  
% 0.22/0.52  cnf(u45,axiom,
% 0.22/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u22,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  cnf(u66,axiom,
% 0.22/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u28,axiom,
% 0.22/0.52      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~l1_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u68,axiom,
% 0.22/0.52      r1_tarski(X0,X1) | k1_xboole_0 != k7_subset_1(X0,X0,X1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u42,axiom,
% 0.22/0.52      r1_tarski(X1,X1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u37,axiom,
% 0.22/0.52      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 0.22/0.52  
% 0.22/0.52  cnf(u37,axiom,
% 0.22/0.52      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 0.22/0.52  
% 0.22/0.52  cnf(u69,axiom,
% 0.22/0.52      ~r1_tarski(X0,X1) | k1_xboole_0 = k7_subset_1(X0,X0,X1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u65,negated_conjecture,
% 0.22/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = sK1).
% 0.22/0.52  
% 0.22/0.52  cnf(u64,negated_conjecture,
% 0.22/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.52  
% 0.22/0.52  cnf(u86,negated_conjecture,
% 0.22/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.22/0.52  
% 0.22/0.52  cnf(u75,axiom,
% 0.22/0.52      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u70,negated_conjecture,
% 0.22/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u38,axiom,
% 0.22/0.52      k2_subset_1(X0) = X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u58,axiom,
% 0.22/0.52      k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u31,axiom,
% 0.22/0.52      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u49,axiom,
% 0.22/0.52      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))).
% 0.22/0.52  
% 0.22/0.52  cnf(u32,axiom,
% 0.22/0.52      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u72,axiom,
% 0.22/0.52      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u26,negated_conjecture,
% 0.22/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.22/0.52  
% 0.22/0.52  cnf(u63,negated_conjecture,
% 0.22/0.52      k2_struct_0(sK0) != sK1).
% 0.22/0.52  
% 0.22/0.52  cnf(u59,negated_conjecture,
% 0.22/0.52      k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) | k2_struct_0(sK0) != sK1).
% 0.22/0.52  
% 0.22/0.52  cnf(u67,axiom,
% 0.22/0.52      k1_xboole_0 != k7_subset_1(X2,X2,X3) | ~r1_tarski(X3,X2) | X2 = X3).
% 0.22/0.52  
% 0.22/0.52  cnf(u44,negated_conjecture,
% 0.22/0.52      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) | k2_struct_0(sK0) != sK1).
% 0.22/0.52  
% 0.22/0.52  % (15538)# SZS output end Saturation.
% 0.22/0.52  % (15538)------------------------------
% 0.22/0.52  % (15538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15538)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (15538)Memory used [KB]: 1791
% 0.22/0.52  % (15538)Time elapsed: 0.108 s
% 0.22/0.52  % (15538)------------------------------
% 0.22/0.52  % (15538)------------------------------
% 0.22/0.53  % (15532)Success in time 0.165 s
%------------------------------------------------------------------------------
