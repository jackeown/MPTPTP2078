%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:49 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u19,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u56,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) )).

cnf(u39,negated_conjecture,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) )).

cnf(u32,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u29,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u25,axiom,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) )).

cnf(u26,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u59,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

cnf(u57,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u36,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u35,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) )).

cnf(u24,axiom,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 )).

cnf(u41,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) )).

cnf(u30,axiom,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )).

cnf(u33,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) )).

cnf(u31,axiom,
    ( k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2)) )).

cnf(u37,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u14,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u28,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:48:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (20467)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (20474)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (20491)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (20485)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (20478)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (20478)Refutation not found, incomplete strategy% (20478)------------------------------
% 0.20/0.53  % (20478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20478)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20478)Memory used [KB]: 6140
% 0.20/0.53  % (20478)Time elapsed: 0.001 s
% 0.20/0.53  % (20478)------------------------------
% 0.20/0.53  % (20478)------------------------------
% 0.20/0.53  % (20477)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (20466)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (20474)Refutation not found, incomplete strategy% (20474)------------------------------
% 0.20/0.53  % (20474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20473)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (20475)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (20469)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (20467)Refutation not found, incomplete strategy% (20467)------------------------------
% 0.20/0.53  % (20467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20467)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20467)Memory used [KB]: 6140
% 0.20/0.53  % (20467)Time elapsed: 0.116 s
% 0.20/0.53  % (20467)------------------------------
% 0.20/0.53  % (20467)------------------------------
% 0.20/0.53  % (20466)Refutation not found, incomplete strategy% (20466)------------------------------
% 0.20/0.53  % (20466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20466)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20466)Memory used [KB]: 10746
% 0.20/0.53  % (20466)Time elapsed: 0.115 s
% 0.20/0.53  % (20466)------------------------------
% 0.20/0.53  % (20466)------------------------------
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (20469)# SZS output start Saturation.
% 0.20/0.53  cnf(u17,negated_conjecture,
% 0.20/0.53      l1_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u19,axiom,
% 0.20/0.53      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.20/0.53  
% 0.20/0.53  cnf(u16,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u56,negated_conjecture,
% 0.20/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u27,axiom,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))).
% 0.20/0.53  
% 0.20/0.53  cnf(u39,negated_conjecture,
% 0.20/0.53      r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u32,axiom,
% 0.20/0.53      r1_tarski(k1_xboole_0,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u29,axiom,
% 0.20/0.53      r1_tarski(X0,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u25,axiom,
% 0.20/0.53      r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u26,axiom,
% 0.20/0.53      ~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u59,negated_conjecture,
% 0.20/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u57,negated_conjecture,
% 0.20/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u36,negated_conjecture,
% 0.20/0.53      sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u35,negated_conjecture,
% 0.20/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u24,axiom,
% 0.20/0.53      k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u41,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k5_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u30,axiom,
% 0.20/0.53      k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u33,axiom,
% 0.20/0.53      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u31,axiom,
% 0.20/0.53      k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,X2))).
% 0.20/0.53  
% 0.20/0.53  cnf(u37,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u14,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u28,negated_conjecture,
% 0.20/0.53      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.53  
% 0.20/0.53  % (20469)# SZS output end Saturation.
% 0.20/0.53  % (20469)------------------------------
% 0.20/0.53  % (20469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20469)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (20469)Memory used [KB]: 6268
% 0.20/0.53  % (20469)Time elapsed: 0.080 s
% 0.20/0.53  % (20469)------------------------------
% 0.20/0.53  % (20469)------------------------------
% 0.20/0.53  % (20474)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20474)Memory used [KB]: 10618
% 0.20/0.53  % (20474)Time elapsed: 0.115 s
% 0.20/0.53  % (20474)------------------------------
% 0.20/0.53  % (20474)------------------------------
% 0.20/0.53  % (20462)Success in time 0.171 s
%------------------------------------------------------------------------------
