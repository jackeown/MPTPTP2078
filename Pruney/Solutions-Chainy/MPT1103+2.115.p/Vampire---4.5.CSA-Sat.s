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
% DateTime   : Thu Dec  3 13:08:49 EST 2020

% Result     : CounterSatisfiable 1.28s
% Output     : Saturation 1.28s
% Verified   : 
% Statistics : Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u35,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u38,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2) )).

cnf(u37,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u32,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u30,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u22,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u36,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u17,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u29,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u28,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (29331)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (29331)Refutation not found, incomplete strategy% (29331)------------------------------
% 0.21/0.52  % (29331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29331)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29331)Memory used [KB]: 1663
% 0.21/0.52  % (29331)Time elapsed: 0.065 s
% 0.21/0.52  % (29331)------------------------------
% 0.21/0.52  % (29331)------------------------------
% 0.21/0.52  % (29315)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (29319)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (29308)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (29325)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (29308)Refutation not found, incomplete strategy% (29308)------------------------------
% 0.21/0.52  % (29308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29308)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29308)Memory used [KB]: 1663
% 0.21/0.52  % (29308)Time elapsed: 0.097 s
% 0.21/0.52  % (29308)------------------------------
% 0.21/0.52  % (29308)------------------------------
% 0.21/0.53  % (29317)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (29310)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (29323)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.53  % (29328)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.53  % (29313)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  % (29323)Refutation not found, incomplete strategy% (29323)------------------------------
% 1.28/0.53  % (29323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (29323)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (29323)Memory used [KB]: 6140
% 1.28/0.53  % (29323)Time elapsed: 0.004 s
% 1.28/0.53  % (29323)------------------------------
% 1.28/0.53  % (29323)------------------------------
% 1.28/0.54  % (29320)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.54  % (29336)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.54  % (29309)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (29333)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.54  % (29314)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.54  % (29310)Refutation not found, incomplete strategy% (29310)------------------------------
% 1.28/0.54  % (29310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (29310)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (29310)Memory used [KB]: 10618
% 1.28/0.54  % (29310)Time elapsed: 0.127 s
% 1.28/0.54  % (29310)------------------------------
% 1.28/0.54  % (29310)------------------------------
% 1.28/0.54  % (29313)Refutation not found, incomplete strategy% (29313)------------------------------
% 1.28/0.54  % (29313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (29313)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (29313)Memory used [KB]: 6140
% 1.28/0.54  % (29313)Time elapsed: 0.128 s
% 1.28/0.54  % (29313)------------------------------
% 1.28/0.54  % (29313)------------------------------
% 1.28/0.54  % (29333)Refutation not found, incomplete strategy% (29333)------------------------------
% 1.28/0.54  % (29333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (29333)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (29333)Memory used [KB]: 6268
% 1.28/0.54  % (29333)Time elapsed: 0.130 s
% 1.28/0.54  % (29333)------------------------------
% 1.28/0.54  % (29333)------------------------------
% 1.28/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.28/0.54  % (29314)# SZS output start Saturation.
% 1.28/0.54  cnf(u20,axiom,
% 1.28/0.54      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 1.28/0.54  
% 1.28/0.54  cnf(u19,negated_conjecture,
% 1.28/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.28/0.54  
% 1.28/0.54  cnf(u24,axiom,
% 1.28/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 1.28/0.54  
% 1.28/0.54  cnf(u25,axiom,
% 1.28/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 1.28/0.54  
% 1.28/0.54  cnf(u26,axiom,
% 1.28/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 1.28/0.54  
% 1.28/0.54  cnf(u35,negated_conjecture,
% 1.28/0.54      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 1.28/0.54  
% 1.28/0.54  cnf(u38,axiom,
% 1.28/0.54      k7_subset_1(X1,k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2)).
% 1.28/0.54  
% 1.28/0.54  cnf(u37,negated_conjecture,
% 1.28/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 1.28/0.54  
% 1.28/0.54  cnf(u32,axiom,
% 1.28/0.54      k3_subset_1(X0,k1_xboole_0) = X0).
% 1.28/0.54  
% 1.28/0.54  cnf(u30,negated_conjecture,
% 1.28/0.54      k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 1.28/0.54  
% 1.28/0.54  cnf(u22,axiom,
% 1.28/0.54      k4_xboole_0(X0,k1_xboole_0) = X0).
% 1.28/0.54  
% 1.28/0.54  cnf(u36,axiom,
% 1.28/0.54      k1_xboole_0 = k3_subset_1(X0,X0)).
% 1.28/0.54  
% 1.28/0.54  cnf(u17,negated_conjecture,
% 1.28/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.28/0.54  
% 1.28/0.54  cnf(u29,axiom,
% 1.28/0.54      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 1.28/0.54  
% 1.28/0.54  cnf(u28,negated_conjecture,
% 1.28/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.28/0.54  
% 1.28/0.54  % (29314)# SZS output end Saturation.
% 1.28/0.54  % (29314)------------------------------
% 1.28/0.54  % (29314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (29314)Termination reason: Satisfiable
% 1.28/0.54  
% 1.28/0.54  % (29314)Memory used [KB]: 6140
% 1.28/0.54  % (29314)Time elapsed: 0.118 s
% 1.28/0.54  % (29314)------------------------------
% 1.28/0.54  % (29314)------------------------------
% 1.28/0.54  % (29325)Refutation not found, incomplete strategy% (29325)------------------------------
% 1.28/0.54  % (29325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (29325)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (29325)Memory used [KB]: 10618
% 1.28/0.54  % (29325)Time elapsed: 0.127 s
% 1.28/0.54  % (29325)------------------------------
% 1.28/0.54  % (29325)------------------------------
% 1.28/0.54  % (29320)Refutation not found, incomplete strategy% (29320)------------------------------
% 1.28/0.54  % (29320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (29320)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (29320)Memory used [KB]: 6268
% 1.28/0.54  % (29320)Time elapsed: 0.126 s
% 1.28/0.54  % (29320)------------------------------
% 1.28/0.54  % (29320)------------------------------
% 1.28/0.54  % (29318)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.54  % (29307)Success in time 0.173 s
%------------------------------------------------------------------------------
