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
% DateTime   : Thu Dec  3 13:08:43 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u31,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u44,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u28,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u52,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u36,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u43,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u42,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u39,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u49,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 )).

cnf(u55,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u37,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u35,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u60,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = sK1 )).

cnf(u53,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u59,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u51,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2) )).

cnf(u50,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u29,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u54,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u47,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u57,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u32,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u30,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u24,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:41:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (10811)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (10819)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (10819)Refutation not found, incomplete strategy% (10819)------------------------------
% 0.21/0.52  % (10819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10819)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10819)Memory used [KB]: 6268
% 0.21/0.52  % (10819)Time elapsed: 0.106 s
% 0.21/0.52  % (10819)------------------------------
% 0.21/0.52  % (10819)------------------------------
% 0.21/0.53  % (10806)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (10812)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (10801)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (10807)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (10811)Refutation not found, incomplete strategy% (10811)------------------------------
% 0.21/0.53  % (10811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10811)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10811)Memory used [KB]: 6396
% 0.21/0.53  % (10811)Time elapsed: 0.097 s
% 0.21/0.53  % (10811)------------------------------
% 0.21/0.53  % (10811)------------------------------
% 0.21/0.53  % (10820)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (10802)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (10809)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (10809)Refutation not found, incomplete strategy% (10809)------------------------------
% 0.21/0.53  % (10809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10809)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10809)Memory used [KB]: 6268
% 0.21/0.53  % (10809)Time elapsed: 0.123 s
% 0.21/0.53  % (10809)------------------------------
% 0.21/0.53  % (10809)------------------------------
% 0.21/0.53  % (10808)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (10804)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (10808)Refutation not found, incomplete strategy% (10808)------------------------------
% 0.21/0.53  % (10808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10808)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10808)Memory used [KB]: 10746
% 0.21/0.53  % (10808)Time elapsed: 0.121 s
% 0.21/0.53  % (10808)------------------------------
% 0.21/0.53  % (10808)------------------------------
% 0.21/0.53  % (10798)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (10799)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (10803)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (10824)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (10800)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (10813)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (10799)Refutation not found, incomplete strategy% (10799)------------------------------
% 0.21/0.54  % (10799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10799)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10799)Memory used [KB]: 1663
% 0.21/0.54  % (10799)Time elapsed: 0.134 s
% 0.21/0.54  % (10799)------------------------------
% 0.21/0.54  % (10799)------------------------------
% 0.21/0.54  % (10817)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (10803)Refutation not found, incomplete strategy% (10803)------------------------------
% 0.21/0.54  % (10803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10803)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10803)Memory used [KB]: 1791
% 0.21/0.54  % (10803)Time elapsed: 0.135 s
% 0.21/0.54  % (10803)------------------------------
% 0.21/0.54  % (10803)------------------------------
% 0.21/0.54  % (10816)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (10820)Refutation not found, incomplete strategy% (10820)------------------------------
% 0.21/0.54  % (10820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10820)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10820)Memory used [KB]: 6268
% 0.21/0.54  % (10820)Time elapsed: 0.102 s
% 0.21/0.54  % (10820)------------------------------
% 0.21/0.54  % (10820)------------------------------
% 0.21/0.54  % (10805)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (10812)Refutation not found, incomplete strategy% (10812)------------------------------
% 0.21/0.54  % (10812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10812)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10812)Memory used [KB]: 1663
% 0.21/0.54  % (10812)Time elapsed: 0.101 s
% 0.21/0.54  % (10812)------------------------------
% 0.21/0.54  % (10812)------------------------------
% 0.21/0.54  % (10818)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (10805)# SZS output start Saturation.
% 0.21/0.54  cnf(u22,negated_conjecture,
% 0.21/0.54      l1_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u31,axiom,
% 0.21/0.54      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u44,axiom,
% 0.21/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u28,axiom,
% 0.21/0.54      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u23,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.55  cnf(u52,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u36,axiom,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u38,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u43,axiom,
% 0.21/0.55      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u42,negated_conjecture,
% 0.21/0.55      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u39,axiom,
% 0.21/0.55      r1_tarski(X1,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u49,negated_conjecture,
% 0.21/0.55      ~r1_tarski(u1_struct_0(sK0),sK1) | u1_struct_0(sK0) = sK1).
% 0.21/0.55  
% 0.21/0.55  cnf(u55,axiom,
% 0.21/0.55      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u37,axiom,
% 0.21/0.55      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u35,axiom,
% 0.21/0.55      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u60,negated_conjecture,
% 0.21/0.55      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = sK1).
% 0.21/0.55  
% 0.21/0.55  cnf(u53,negated_conjecture,
% 0.21/0.55      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u59,negated_conjecture,
% 0.21/0.55      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u51,axiom,
% 0.21/0.55      k7_subset_1(X1,k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u50,negated_conjecture,
% 0.21/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u29,axiom,
% 0.21/0.55      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u54,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u27,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.21/0.55  
% 0.21/0.55  cnf(u47,axiom,
% 0.21/0.55      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u57,axiom,
% 0.21/0.55      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u32,axiom,
% 0.21/0.55      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u30,axiom,
% 0.21/0.55      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u24,negated_conjecture,
% 0.21/0.55      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1).
% 0.21/0.55  
% 0.21/0.55  % (10805)# SZS output end Saturation.
% 0.21/0.55  % (10805)------------------------------
% 0.21/0.55  % (10805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10805)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (10805)Memory used [KB]: 1791
% 0.21/0.55  % (10805)Time elapsed: 0.137 s
% 0.21/0.55  % (10805)------------------------------
% 0.21/0.55  % (10805)------------------------------
% 0.21/0.55  % (10824)Refutation not found, incomplete strategy% (10824)------------------------------
% 0.21/0.55  % (10824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10816)Refutation not found, incomplete strategy% (10816)------------------------------
% 0.21/0.55  % (10816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10826)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (10815)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (10816)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10816)Memory used [KB]: 1663
% 0.21/0.55  % (10816)Time elapsed: 0.147 s
% 0.21/0.55  % (10816)------------------------------
% 0.21/0.55  % (10816)------------------------------
% 0.21/0.55  % (10824)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10824)Memory used [KB]: 6268
% 0.21/0.55  % (10824)Time elapsed: 0.147 s
% 0.21/0.55  % (10824)------------------------------
% 0.21/0.55  % (10824)------------------------------
% 0.21/0.55  % (10826)Refutation not found, incomplete strategy% (10826)------------------------------
% 0.21/0.55  % (10826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10826)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10826)Memory used [KB]: 10746
% 0.21/0.55  % (10826)Time elapsed: 0.148 s
% 0.21/0.55  % (10826)------------------------------
% 0.21/0.55  % (10826)------------------------------
% 0.21/0.55  % (10810)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (10814)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (10822)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (10807)Refutation not found, incomplete strategy% (10807)------------------------------
% 0.21/0.55  % (10807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10807)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10807)Memory used [KB]: 1791
% 0.21/0.55  % (10807)Time elapsed: 0.143 s
% 0.21/0.55  % (10807)------------------------------
% 0.21/0.55  % (10807)------------------------------
% 0.21/0.55  % (10814)Refutation not found, incomplete strategy% (10814)------------------------------
% 0.21/0.55  % (10814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10814)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10814)Memory used [KB]: 10618
% 0.21/0.55  % (10814)Time elapsed: 0.148 s
% 0.21/0.55  % (10814)------------------------------
% 0.21/0.55  % (10814)------------------------------
% 0.21/0.55  % (10823)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (10822)Refutation not found, incomplete strategy% (10822)------------------------------
% 0.21/0.55  % (10822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10822)Memory used [KB]: 10618
% 0.21/0.55  % (10822)Time elapsed: 0.147 s
% 0.21/0.55  % (10822)------------------------------
% 0.21/0.55  % (10822)------------------------------
% 0.21/0.55  % (10810)Refutation not found, incomplete strategy% (10810)------------------------------
% 0.21/0.55  % (10810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10810)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10810)Memory used [KB]: 10746
% 0.21/0.55  % (10810)Time elapsed: 0.149 s
% 0.21/0.55  % (10810)------------------------------
% 0.21/0.55  % (10810)------------------------------
% 0.21/0.55  % (10823)Refutation not found, incomplete strategy% (10823)------------------------------
% 0.21/0.55  % (10823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10823)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10823)Memory used [KB]: 6140
% 0.21/0.55  % (10823)Time elapsed: 0.146 s
% 0.21/0.55  % (10823)------------------------------
% 0.21/0.55  % (10823)------------------------------
% 0.21/0.55  % (10797)Success in time 0.192 s
%------------------------------------------------------------------------------
