%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:39 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u20,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u23,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u32,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u68,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u33,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u34,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u71,negated_conjecture,
    ( ~ r1_tarski(X0,u1_struct_0(sK0))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u43,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_xboole_0 = k7_subset_1(X0,X0,X1) )).

cnf(u46,axiom,
    ( ~ r1_tarski(X4,X3)
    | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5) )).

cnf(u72,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u69,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u70,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u53,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) )).

cnf(u45,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u18,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u40,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

cnf(u36,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

cnf(u38,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,u1_struct_0(sK0))) )).

cnf(u47,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u48,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u14,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u21,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u44,axiom,
    ( k1_xboole_0 != k7_subset_1(X0,X0,X1)
    | r1_tarski(X0,X1) )).

cnf(u31,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (18911)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (18931)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (18908)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (18913)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (18912)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (18915)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (18913)Refutation not found, incomplete strategy% (18913)------------------------------
% 0.21/0.51  % (18913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18913)Memory used [KB]: 6268
% 0.21/0.51  % (18913)Time elapsed: 0.110 s
% 0.21/0.51  % (18913)------------------------------
% 0.21/0.51  % (18913)------------------------------
% 0.21/0.52  % (18912)Refutation not found, incomplete strategy% (18912)------------------------------
% 0.21/0.52  % (18912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18912)Memory used [KB]: 6140
% 0.21/0.52  % (18912)Time elapsed: 0.108 s
% 0.21/0.52  % (18912)------------------------------
% 0.21/0.52  % (18912)------------------------------
% 0.21/0.52  % (18930)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18923)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (18922)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (18911)Refutation not found, incomplete strategy% (18911)------------------------------
% 0.21/0.52  % (18911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18915)Refutation not found, incomplete strategy% (18915)------------------------------
% 0.21/0.52  % (18915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18915)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18915)Memory used [KB]: 6268
% 0.21/0.52  % (18915)Time elapsed: 0.102 s
% 0.21/0.52  % (18915)------------------------------
% 0.21/0.52  % (18915)------------------------------
% 0.21/0.52  % (18910)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (18910)Refutation not found, incomplete strategy% (18910)------------------------------
% 0.21/0.52  % (18910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18910)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18910)Memory used [KB]: 10746
% 0.21/0.52  % (18910)Time elapsed: 0.108 s
% 0.21/0.52  % (18910)------------------------------
% 0.21/0.52  % (18910)------------------------------
% 0.21/0.52  % (18914)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (18936)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (18923)Refutation not found, incomplete strategy% (18923)------------------------------
% 0.21/0.52  % (18923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18923)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18923)Memory used [KB]: 6140
% 0.21/0.52  % (18923)Time elapsed: 0.003 s
% 0.21/0.52  % (18923)------------------------------
% 0.21/0.52  % (18923)------------------------------
% 0.21/0.52  % (18921)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (18914)# SZS output start Saturation.
% 0.21/0.52  cnf(u17,negated_conjecture,
% 0.21/0.52      l1_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u20,axiom,
% 0.21/0.52      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u23,axiom,
% 0.21/0.52      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u32,axiom,
% 0.21/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u16,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u68,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u24,axiom,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u42,axiom,
% 0.21/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u33,negated_conjecture,
% 0.21/0.52      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u34,axiom,
% 0.21/0.52      r1_tarski(X0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u71,negated_conjecture,
% 0.21/0.52      ~r1_tarski(X0,u1_struct_0(sK0)) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u43,axiom,
% 0.21/0.52      ~r1_tarski(X0,X1) | k1_xboole_0 = k7_subset_1(X0,X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u46,axiom,
% 0.21/0.52      ~r1_tarski(X4,X3) | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5)).
% 0.21/0.52  
% 0.21/0.52  cnf(u72,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u69,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u70,negated_conjecture,
% 0.21/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u53,axiom,
% 0.21/0.52      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u45,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u18,axiom,
% 0.21/0.52      k2_subset_1(X0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u40,axiom,
% 0.21/0.52      k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u36,axiom,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u38,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u47,axiom,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u48,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u14,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u21,axiom,
% 0.21/0.52      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u44,axiom,
% 0.21/0.52      k1_xboole_0 != k7_subset_1(X0,X0,X1) | r1_tarski(X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u31,negated_conjecture,
% 0.21/0.52      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.52  
% 0.21/0.52  % (18914)# SZS output end Saturation.
% 0.21/0.52  % (18914)------------------------------
% 0.21/0.52  % (18914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18914)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (18914)Memory used [KB]: 6268
% 0.21/0.52  % (18914)Time elapsed: 0.074 s
% 0.21/0.52  % (18914)------------------------------
% 0.21/0.52  % (18914)------------------------------
% 0.21/0.52  % (18918)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (18907)Success in time 0.161 s
%------------------------------------------------------------------------------
