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
% DateTime   : Thu Dec  3 13:08:46 EST 2020

% Result     : CounterSatisfiable 1.25s
% Output     : Saturation 1.25s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u26,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u37,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u51,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u54,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u52,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u53,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u46,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u42,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u22,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u48,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k3_tarski(k2_tarski(X2,X3))) )).

cnf(u47,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u18,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u38,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u23,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u40,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

cnf(u24,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u34,axiom,
    ( k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 )).

cnf(u27,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u36,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:49:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (10132)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (10148)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (10142)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (10126)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (10140)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (10132)Refutation not found, incomplete strategy% (10132)------------------------------
% 0.20/0.51  % (10132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (10132)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (10132)Memory used [KB]: 6268
% 0.20/0.51  % (10132)Time elapsed: 0.102 s
% 0.20/0.51  % (10132)------------------------------
% 0.20/0.51  % (10132)------------------------------
% 0.20/0.51  % (10136)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (10137)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (10130)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (10140)Refutation not found, incomplete strategy% (10140)------------------------------
% 0.20/0.52  % (10140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10130)Refutation not found, incomplete strategy% (10130)------------------------------
% 0.20/0.52  % (10130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10130)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10130)Memory used [KB]: 6268
% 0.20/0.52  % (10130)Time elapsed: 0.109 s
% 0.20/0.52  % (10130)------------------------------
% 0.20/0.52  % (10130)------------------------------
% 0.20/0.52  % (10140)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10140)Memory used [KB]: 6140
% 0.20/0.52  % (10140)Time elapsed: 0.004 s
% 0.20/0.52  % (10140)------------------------------
% 0.20/0.52  % (10140)------------------------------
% 0.20/0.52  % (10139)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (10148)Refutation not found, incomplete strategy% (10148)------------------------------
% 0.20/0.52  % (10148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10148)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10148)Memory used [KB]: 1791
% 0.20/0.52  % (10148)Time elapsed: 0.105 s
% 0.20/0.52  % (10148)------------------------------
% 0.20/0.52  % (10148)------------------------------
% 1.25/0.52  % (10146)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.52  % (10147)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.52  % (10142)Refutation not found, incomplete strategy% (10142)------------------------------
% 1.25/0.52  % (10142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (10134)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.52  % (10146)Refutation not found, incomplete strategy% (10146)------------------------------
% 1.25/0.52  % (10146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (10146)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (10146)Memory used [KB]: 1663
% 1.25/0.52  % (10146)Time elapsed: 0.125 s
% 1.25/0.52  % (10146)------------------------------
% 1.25/0.52  % (10146)------------------------------
% 1.25/0.52  % (10147)Refutation not found, incomplete strategy% (10147)------------------------------
% 1.25/0.52  % (10147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (10147)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (10147)Memory used [KB]: 10618
% 1.25/0.52  % (10147)Time elapsed: 0.083 s
% 1.25/0.52  % (10147)------------------------------
% 1.25/0.52  % (10147)------------------------------
% 1.25/0.52  % (10141)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.52  % (10142)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (10142)Memory used [KB]: 10618
% 1.25/0.52  % (10142)Time elapsed: 0.116 s
% 1.25/0.52  % (10142)------------------------------
% 1.25/0.52  % (10142)------------------------------
% 1.25/0.52  % (10135)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.52  % (10134)Refutation not found, incomplete strategy% (10134)------------------------------
% 1.25/0.52  % (10134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (10134)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (10134)Memory used [KB]: 10618
% 1.25/0.52  % (10134)Time elapsed: 0.116 s
% 1.25/0.52  % (10134)------------------------------
% 1.25/0.52  % (10134)------------------------------
% 1.25/0.53  % (10135)Refutation not found, incomplete strategy% (10135)------------------------------
% 1.25/0.53  % (10135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (10135)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (10135)Memory used [KB]: 10618
% 1.25/0.53  % (10135)Time elapsed: 0.114 s
% 1.25/0.53  % (10135)------------------------------
% 1.25/0.53  % (10135)------------------------------
% 1.25/0.53  % (10131)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % SZS status CounterSatisfiable for theBenchmark
% 1.25/0.53  % (10131)# SZS output start Saturation.
% 1.25/0.53  cnf(u21,negated_conjecture,
% 1.25/0.53      l1_struct_0(sK0)).
% 1.25/0.53  
% 1.25/0.53  cnf(u26,axiom,
% 1.25/0.53      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 1.25/0.53  
% 1.25/0.53  cnf(u37,axiom,
% 1.25/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.25/0.53  
% 1.25/0.53  cnf(u20,negated_conjecture,
% 1.25/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.25/0.53  
% 1.25/0.53  cnf(u51,negated_conjecture,
% 1.25/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 1.25/0.53  
% 1.25/0.53  cnf(u41,axiom,
% 1.25/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.25/0.53  
% 1.25/0.53  cnf(u54,negated_conjecture,
% 1.25/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 1.25/0.53  
% 1.25/0.53  cnf(u52,negated_conjecture,
% 1.25/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.25/0.53  
% 1.25/0.53  cnf(u53,negated_conjecture,
% 1.25/0.53      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 1.25/0.53  
% 1.25/0.53  cnf(u46,axiom,
% 1.25/0.53      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.25/0.53  
% 1.25/0.53  cnf(u42,negated_conjecture,
% 1.25/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.25/0.53  
% 1.25/0.53  cnf(u22,axiom,
% 1.25/0.53      k2_subset_1(X0) = X0).
% 1.25/0.53  
% 1.25/0.53  cnf(u48,axiom,
% 1.25/0.53      k1_xboole_0 = k7_subset_1(X2,X2,k3_tarski(k2_tarski(X2,X3)))).
% 1.25/0.53  
% 1.25/0.53  cnf(u47,axiom,
% 1.25/0.53      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 1.25/0.53  
% 1.25/0.53  cnf(u18,negated_conjecture,
% 1.25/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.25/0.53  
% 1.25/0.53  cnf(u38,axiom,
% 1.25/0.53      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.25/0.53  
% 1.25/0.53  cnf(u23,axiom,
% 1.25/0.53      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 1.25/0.53  
% 1.25/0.53  cnf(u40,axiom,
% 1.25/0.53      k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2)).
% 1.25/0.53  
% 1.25/0.53  cnf(u24,axiom,
% 1.25/0.53      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.25/0.53  
% 1.25/0.53  cnf(u34,axiom,
% 1.25/0.53      k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0).
% 1.25/0.53  
% 1.25/0.53  cnf(u27,axiom,
% 1.25/0.53      k3_xboole_0(X0,X0) = X0).
% 1.25/0.53  
% 1.25/0.53  cnf(u36,negated_conjecture,
% 1.25/0.53      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.25/0.53  
% 1.25/0.53  % (10131)# SZS output end Saturation.
% 1.25/0.53  % (10131)------------------------------
% 1.25/0.53  % (10131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (10131)Termination reason: Satisfiable
% 1.25/0.53  
% 1.25/0.53  % (10131)Memory used [KB]: 6268
% 1.25/0.53  % (10131)Time elapsed: 0.099 s
% 1.25/0.53  % (10131)------------------------------
% 1.25/0.53  % (10131)------------------------------
% 1.25/0.53  % (10138)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.53  % (10129)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.53  % (10128)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.25/0.53  % (10125)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.53  % (10129)Refutation not found, incomplete strategy% (10129)------------------------------
% 1.25/0.53  % (10129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (10129)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (10129)Memory used [KB]: 6268
% 1.25/0.53  % (10129)Time elapsed: 0.127 s
% 1.25/0.53  % (10129)------------------------------
% 1.25/0.53  % (10129)------------------------------
% 1.25/0.53  % (10125)Refutation not found, incomplete strategy% (10125)------------------------------
% 1.25/0.53  % (10125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (10125)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (10125)Memory used [KB]: 1663
% 1.25/0.53  % (10125)Time elapsed: 0.124 s
% 1.25/0.53  % (10125)------------------------------
% 1.25/0.53  % (10125)------------------------------
% 1.25/0.53  % (10128)Refutation not found, incomplete strategy% (10128)------------------------------
% 1.25/0.53  % (10128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (10128)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (10128)Memory used [KB]: 10746
% 1.25/0.53  % (10128)Time elapsed: 0.126 s
% 1.25/0.53  % (10128)------------------------------
% 1.25/0.53  % (10128)------------------------------
% 1.25/0.53  % (10137)Refutation not found, incomplete strategy% (10137)------------------------------
% 1.25/0.53  % (10137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (10137)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (10137)Memory used [KB]: 6268
% 1.25/0.53  % (10137)Time elapsed: 0.107 s
% 1.25/0.53  % (10137)------------------------------
% 1.25/0.53  % (10137)------------------------------
% 1.25/0.53  % (10127)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.54  % (10136)Refutation not found, incomplete strategy% (10136)------------------------------
% 1.25/0.54  % (10136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (10136)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (10136)Memory used [KB]: 10618
% 1.25/0.54  % (10136)Time elapsed: 0.125 s
% 1.25/0.54  % (10136)------------------------------
% 1.25/0.54  % (10136)------------------------------
% 1.25/0.54  % (10153)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.25/0.54  % (10145)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.54  % (10133)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.54  % (10149)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.54  % (10152)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.54  % (10154)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.54  % (10133)Refutation not found, incomplete strategy% (10133)------------------------------
% 1.52/0.54  % (10133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.54  % (10133)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.54  
% 1.52/0.54  % (10133)Memory used [KB]: 10746
% 1.52/0.54  % (10133)Time elapsed: 0.138 s
% 1.52/0.54  % (10133)------------------------------
% 1.52/0.54  % (10133)------------------------------
% 1.52/0.54  % (10124)Success in time 0.183 s
%------------------------------------------------------------------------------
