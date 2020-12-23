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
% DateTime   : Thu Dec  3 13:08:45 EST 2020

% Result     : CounterSatisfiable 1.54s
% Output     : Saturation 1.54s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u27,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

% (24049)Refutation not found, incomplete strategy% (24049)------------------------------
% (24049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u20,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u21,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u29,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u28,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u22,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u24,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u39,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u41,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) )).

cnf(u38,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u18,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u33,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u42,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u35,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u15,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u40,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u32,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u16,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

cnf(u25,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:02:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (24030)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (24035)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (24030)Refutation not found, incomplete strategy% (24030)------------------------------
% 0.20/0.50  % (24030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24035)Refutation not found, incomplete strategy% (24035)------------------------------
% 0.20/0.51  % (24035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24043)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (24035)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24035)Memory used [KB]: 10746
% 0.20/0.51  % (24035)Time elapsed: 0.080 s
% 0.20/0.51  % (24035)------------------------------
% 0.20/0.51  % (24035)------------------------------
% 0.20/0.51  % (24032)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (24032)Refutation not found, incomplete strategy% (24032)------------------------------
% 0.20/0.52  % (24032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24032)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24032)Memory used [KB]: 10618
% 0.20/0.52  % (24032)Time elapsed: 0.080 s
% 0.20/0.52  % (24032)------------------------------
% 0.20/0.52  % (24032)------------------------------
% 0.20/0.52  % (24040)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (24030)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24030)Memory used [KB]: 10618
% 0.20/0.52  % (24030)Time elapsed: 0.073 s
% 0.20/0.52  % (24030)------------------------------
% 0.20/0.52  % (24030)------------------------------
% 0.20/0.52  % (24040)Refutation not found, incomplete strategy% (24040)------------------------------
% 0.20/0.52  % (24040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24040)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24040)Memory used [KB]: 10618
% 0.20/0.52  % (24040)Time elapsed: 0.092 s
% 0.20/0.52  % (24040)------------------------------
% 0.20/0.52  % (24040)------------------------------
% 1.28/0.53  % (24033)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.28/0.53  % (24033)Refutation not found, incomplete strategy% (24033)------------------------------
% 1.28/0.53  % (24033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (24033)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (24033)Memory used [KB]: 1663
% 1.28/0.53  % (24033)Time elapsed: 0.102 s
% 1.28/0.53  % (24033)------------------------------
% 1.28/0.53  % (24033)------------------------------
% 1.28/0.53  % (24034)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.28/0.53  % (24038)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.28/0.53  % (24031)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.28/0.54  % (24038)Refutation not found, incomplete strategy% (24038)------------------------------
% 1.28/0.54  % (24038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (24038)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (24038)Memory used [KB]: 10746
% 1.28/0.54  % (24038)Time elapsed: 0.102 s
% 1.28/0.54  % (24038)------------------------------
% 1.28/0.54  % (24038)------------------------------
% 1.28/0.55  % (24045)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.54/0.55  % (24036)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.54/0.55  % (24049)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.54/0.55  % (24041)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.55  % (24046)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.54/0.55  % (24037)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.54/0.55  % (24042)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.54/0.55  % (24041)Refutation not found, incomplete strategy% (24041)------------------------------
% 1.54/0.55  % (24041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.55  % (24041)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.55  
% 1.54/0.55  % (24041)Memory used [KB]: 6012
% 1.54/0.55  % (24041)Time elapsed: 0.002 s
% 1.54/0.55  % (24041)------------------------------
% 1.54/0.55  % (24041)------------------------------
% 1.54/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.54/0.55  % (24046)# SZS output start Saturation.
% 1.54/0.55  cnf(u17,negated_conjecture,
% 1.54/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.54/0.55  
% 1.54/0.55  cnf(u27,axiom,
% 1.54/0.55      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.54/0.55  
% 1.54/0.55  cnf(u23,axiom,
% 1.54/0.55      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.54/0.55  
% 1.54/0.55  % (24049)Refutation not found, incomplete strategy% (24049)------------------------------
% 1.54/0.55  % (24049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.55  cnf(u20,axiom,
% 1.54/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 1.54/0.55  
% 1.54/0.55  cnf(u21,axiom,
% 1.54/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 1.54/0.55  
% 1.54/0.55  cnf(u26,axiom,
% 1.54/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 1.54/0.55  
% 1.54/0.55  cnf(u29,negated_conjecture,
% 1.54/0.55      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.54/0.55  
% 1.54/0.55  cnf(u28,axiom,
% 1.54/0.55      r1_tarski(X0,X0)).
% 1.54/0.55  
% 1.54/0.55  cnf(u22,axiom,
% 1.54/0.55      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 1.54/0.55  
% 1.54/0.55  cnf(u24,axiom,
% 1.54/0.55      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 1.54/0.55  
% 1.54/0.55  cnf(u39,negated_conjecture,
% 1.54/0.55      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 1.54/0.55  
% 1.54/0.55  cnf(u41,negated_conjecture,
% 1.54/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)).
% 1.54/0.55  
% 1.54/0.55  cnf(u38,axiom,
% 1.54/0.55      k3_subset_1(X0,k1_xboole_0) = X0).
% 1.54/0.55  
% 1.54/0.55  cnf(u18,axiom,
% 1.54/0.55      k2_subset_1(X0) = X0).
% 1.54/0.55  
% 1.54/0.55  cnf(u33,axiom,
% 1.54/0.55      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 1.54/0.55  
% 1.54/0.55  cnf(u42,negated_conjecture,
% 1.54/0.55      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 1.54/0.55  
% 1.54/0.55  cnf(u35,axiom,
% 1.54/0.55      k1_xboole_0 = k3_subset_1(X0,X0)).
% 1.54/0.55  
% 1.54/0.55  cnf(u15,negated_conjecture,
% 1.54/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.54/0.55  
% 1.54/0.55  cnf(u40,axiom,
% 1.54/0.55      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 1.54/0.55  
% 1.54/0.55  cnf(u32,negated_conjecture,
% 1.54/0.55      k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 1.54/0.55  
% 1.54/0.55  cnf(u16,negated_conjecture,
% 1.54/0.55      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 1.54/0.55  
% 1.54/0.55  cnf(u25,axiom,
% 1.54/0.55      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 1.54/0.55  
% 1.54/0.55  % (24046)# SZS output end Saturation.
% 1.54/0.55  % (24046)------------------------------
% 1.54/0.55  % (24046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.55  % (24046)Termination reason: Satisfiable
% 1.54/0.55  
% 1.54/0.55  % (24046)Memory used [KB]: 1663
% 1.54/0.55  % (24046)Time elapsed: 0.088 s
% 1.54/0.55  % (24046)------------------------------
% 1.54/0.55  % (24046)------------------------------
% 1.54/0.55  % (24049)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.55  
% 1.54/0.55  % (24049)Memory used [KB]: 10490
% 1.54/0.55  % (24049)Time elapsed: 0.126 s
% 1.54/0.55  % (24049)------------------------------
% 1.54/0.55  % (24049)------------------------------
% 1.54/0.56  % (24044)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.54/0.56  % (24028)Success in time 0.193 s
%------------------------------------------------------------------------------
