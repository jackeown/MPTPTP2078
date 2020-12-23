%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u39,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0) )).

cnf(u40,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u21,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u27,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 )).

cnf(u35,negated_conjecture,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u36,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u47,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u30,negated_conjecture,
    ( sK1 = k4_xboole_0(sK1,sK2) )).

cnf(u45,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u20,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u38,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1) )).

cnf(u37,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) )).

cnf(u44,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u42,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

cnf(u41,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u32,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u31,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2) )).

cnf(u24,axiom,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) )).

cnf(u22,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:38:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (27996)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (27996)Refutation not found, incomplete strategy% (27996)------------------------------
% 0.21/0.50  % (27996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27992)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (28004)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (27990)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (27992)Refutation not found, incomplete strategy% (27992)------------------------------
% 0.21/0.51  % (27992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27999)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (27992)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27992)Memory used [KB]: 10746
% 0.21/0.51  % (27992)Time elapsed: 0.056 s
% 0.21/0.51  % (27992)------------------------------
% 0.21/0.51  % (27992)------------------------------
% 0.21/0.52  % (28000)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (27996)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27996)Memory used [KB]: 6140
% 0.21/0.52  % (27996)Time elapsed: 0.067 s
% 0.21/0.52  % (27996)------------------------------
% 0.21/0.52  % (27996)------------------------------
% 0.21/0.53  % (27999)Refutation not found, incomplete strategy% (27999)------------------------------
% 0.21/0.53  % (27999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27999)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27999)Memory used [KB]: 1663
% 0.21/0.53  % (27999)Time elapsed: 0.083 s
% 0.21/0.53  % (27999)------------------------------
% 0.21/0.53  % (27999)------------------------------
% 0.21/0.54  % (27989)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.54  % (27989)Refutation not found, incomplete strategy% (27989)------------------------------
% 0.21/0.54  % (27989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27989)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27989)Memory used [KB]: 1663
% 0.21/0.54  % (27989)Time elapsed: 0.098 s
% 0.21/0.54  % (27989)------------------------------
% 0.21/0.54  % (27989)------------------------------
% 0.21/0.54  % (28001)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.54  % (27986)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (28001)Refutation not found, incomplete strategy% (28001)------------------------------
% 0.21/0.54  % (28001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28001)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28001)Memory used [KB]: 6140
% 0.21/0.54  % (28001)Time elapsed: 0.111 s
% 0.21/0.54  % (28001)------------------------------
% 0.21/0.54  % (28001)------------------------------
% 0.21/0.54  % (27986)Refutation not found, incomplete strategy% (27986)------------------------------
% 0.21/0.54  % (27986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27986)Memory used [KB]: 10618
% 0.21/0.54  % (27986)Time elapsed: 0.106 s
% 0.21/0.54  % (27986)------------------------------
% 0.21/0.54  % (27986)------------------------------
% 0.21/0.55  % (27995)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.55  % (27985)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (27995)Refutation not found, incomplete strategy% (27995)------------------------------
% 0.21/0.55  % (27995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27988)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (27995)Memory used [KB]: 10618
% 0.21/0.55  % (27995)Time elapsed: 0.067 s
% 0.21/0.55  % (27995)------------------------------
% 0.21/0.55  % (27995)------------------------------
% 0.21/0.55  % (27985)Refutation not found, incomplete strategy% (27985)------------------------------
% 0.21/0.55  % (27985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27985)Memory used [KB]: 6268
% 0.21/0.55  % (27985)Time elapsed: 0.106 s
% 0.21/0.55  % (27985)------------------------------
% 0.21/0.55  % (27985)------------------------------
% 0.21/0.55  % (27993)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.55  % (28005)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.55  % (27988)Refutation not found, incomplete strategy% (27988)------------------------------
% 0.21/0.55  % (27988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27988)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27988)Memory used [KB]: 10618
% 0.21/0.55  % (27988)Time elapsed: 0.106 s
% 0.21/0.55  % (27988)------------------------------
% 0.21/0.55  % (27988)------------------------------
% 0.21/0.55  % (27994)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.55  % (28005)Refutation not found, incomplete strategy% (28005)------------------------------
% 0.21/0.55  % (28005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28005)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28005)Memory used [KB]: 6140
% 0.21/0.55  % (28005)Time elapsed: 0.122 s
% 0.21/0.55  % (28005)------------------------------
% 0.21/0.55  % (28005)------------------------------
% 0.21/0.55  % (27998)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (28003)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.55  % (27998)Refutation not found, incomplete strategy% (27998)------------------------------
% 0.21/0.55  % (27998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27998)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27998)Memory used [KB]: 6012
% 0.21/0.55  % (27998)Time elapsed: 0.001 s
% 0.21/0.55  % (27998)------------------------------
% 0.21/0.55  % (27998)------------------------------
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (28003)# SZS output start Saturation.
% 0.21/0.55  cnf(u23,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u19,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u39,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u40,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u25,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u26,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u28,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u29,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u21,negated_conjecture,
% 0.21/0.55      r1_xboole_0(sK1,sK2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u27,axiom,
% 0.21/0.55      ~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u35,negated_conjecture,
% 0.21/0.55      sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.21/0.55  
% 0.21/0.55  cnf(u36,negated_conjecture,
% 0.21/0.55      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u47,negated_conjecture,
% 0.21/0.55      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u30,negated_conjecture,
% 0.21/0.55      sK1 = k4_xboole_0(sK1,sK2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u45,negated_conjecture,
% 0.21/0.55      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u20,negated_conjecture,
% 0.21/0.55      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u38,negated_conjecture,
% 0.21/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u37,negated_conjecture,
% 0.21/0.55      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u44,negated_conjecture,
% 0.21/0.55      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u42,negated_conjecture,
% 0.21/0.55      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u41,negated_conjecture,
% 0.21/0.55      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u32,negated_conjecture,
% 0.21/0.55      k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u31,negated_conjecture,
% 0.21/0.55      k4_xboole_0(u1_struct_0(sK0),sK2) = k3_subset_1(u1_struct_0(sK0),sK2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u24,axiom,
% 0.21/0.55      k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u22,negated_conjecture,
% 0.21/0.55      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.55  
% 0.21/0.55  % (28003)# SZS output end Saturation.
% 0.21/0.55  % (28003)------------------------------
% 0.21/0.55  % (28003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28003)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (28003)Memory used [KB]: 1663
% 0.21/0.55  % (28003)Time elapsed: 0.075 s
% 0.21/0.55  % (28003)------------------------------
% 0.21/0.55  % (28003)------------------------------
% 0.21/0.55  % (28006)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.56  % (27984)Success in time 0.19 s
%------------------------------------------------------------------------------
