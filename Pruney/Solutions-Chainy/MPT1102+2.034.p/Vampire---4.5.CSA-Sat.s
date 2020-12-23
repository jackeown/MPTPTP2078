%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:33 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u29,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u33,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u22,axiom,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) )).

cnf(u31,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u37,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | u1_struct_0(sK0) = sK1 )).

cnf(u36,axiom,
    ( ~ r1_tarski(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X1,X2) = X1 )).

cnf(u27,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 )).

cnf(u39,axiom,
    ( ~ r1_tarski(X1,X0)
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u44,axiom,
    ( ~ r1_tarski(X1,X0)
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u77,axiom,
    ( ~ r1_tarski(X2,X1)
    | k4_xboole_0(X2,X3) = k7_subset_1(X1,X2,X3) )).

cnf(u79,axiom,
    ( k4_xboole_0(k4_xboole_0(X2,X3),X4) = k7_subset_1(X2,k4_xboole_0(X2,X3),X4) )).

cnf(u78,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u45,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u61,axiom,
    ( k4_xboole_0(X1,X2) = k3_subset_1(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) )).

cnf(u41,axiom,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_subset_1(X1,k4_xboole_0(X1,X2)) )).

cnf(u40,axiom,
    ( k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) )).

cnf(u38,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u76,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u66,axiom,
    ( k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) )).

cnf(u51,negated_conjecture,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u52,axiom,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

cnf(u49,axiom,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 )).

cnf(u21,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:16:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30774)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (30772)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (30783)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (30772)Refutation not found, incomplete strategy% (30772)------------------------------
% 0.22/0.51  % (30772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30772)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30772)Memory used [KB]: 6140
% 0.22/0.51  % (30772)Time elapsed: 0.082 s
% 0.22/0.51  % (30772)------------------------------
% 0.22/0.51  % (30772)------------------------------
% 0.22/0.51  % (30771)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (30789)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (30774)Refutation not found, incomplete strategy% (30774)------------------------------
% 0.22/0.51  % (30774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30774)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30774)Memory used [KB]: 10490
% 0.22/0.51  % (30774)Time elapsed: 0.082 s
% 0.22/0.51  % (30774)------------------------------
% 0.22/0.51  % (30774)------------------------------
% 0.22/0.51  % (30771)Refutation not found, incomplete strategy% (30771)------------------------------
% 0.22/0.51  % (30771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30771)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30771)Memory used [KB]: 6140
% 0.22/0.51  % (30771)Time elapsed: 0.089 s
% 0.22/0.51  % (30771)------------------------------
% 0.22/0.51  % (30771)------------------------------
% 0.22/0.51  % (30790)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (30773)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (30783)Refutation not found, incomplete strategy% (30783)------------------------------
% 0.22/0.51  % (30783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30783)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30783)Memory used [KB]: 6140
% 0.22/0.51  % (30783)Time elapsed: 0.046 s
% 0.22/0.51  % (30783)------------------------------
% 0.22/0.51  % (30783)------------------------------
% 0.22/0.51  % (30773)Refutation not found, incomplete strategy% (30773)------------------------------
% 0.22/0.51  % (30773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30773)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30773)Memory used [KB]: 6140
% 0.22/0.51  % (30773)Time elapsed: 0.085 s
% 0.22/0.51  % (30773)------------------------------
% 0.22/0.51  % (30773)------------------------------
% 0.22/0.51  % (30782)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (30790)Refutation not found, incomplete strategy% (30790)------------------------------
% 0.22/0.51  % (30790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30790)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30790)Memory used [KB]: 10618
% 0.22/0.51  % (30790)Time elapsed: 0.098 s
% 0.22/0.51  % (30790)------------------------------
% 0.22/0.51  % (30790)------------------------------
% 0.22/0.51  % (30769)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (30789)# SZS output start Saturation.
% 0.22/0.51  cnf(u19,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,axiom,
% 0.22/0.51      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u28,axiom,
% 0.22/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u23,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u24,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u33,negated_conjecture,
% 0.22/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,axiom,
% 0.22/0.51      r1_tarski(k4_xboole_0(X0,X1),X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u31,axiom,
% 0.22/0.51      r1_tarski(X1,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u37,negated_conjecture,
% 0.22/0.51      ~r1_tarski(u1_struct_0(sK0),sK1) | u1_struct_0(sK0) = sK1).
% 0.22/0.51  
% 0.22/0.51  cnf(u36,axiom,
% 0.22/0.51      ~r1_tarski(X1,k4_xboole_0(X1,X2)) | k4_xboole_0(X1,X2) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u27,axiom,
% 0.22/0.51      ~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,axiom,
% 0.22/0.51      ~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u44,axiom,
% 0.22/0.51      ~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u77,axiom,
% 0.22/0.51      ~r1_tarski(X2,X1) | k4_xboole_0(X2,X3) = k7_subset_1(X1,X2,X3)).
% 0.22/0.51  
% 0.22/0.51  cnf(u79,axiom,
% 0.22/0.51      k4_xboole_0(k4_xboole_0(X2,X3),X4) = k7_subset_1(X2,k4_xboole_0(X2,X3),X4)).
% 0.22/0.51  
% 0.22/0.51  cnf(u78,axiom,
% 0.22/0.51      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u45,negated_conjecture,
% 0.22/0.51      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u61,axiom,
% 0.22/0.51      k4_xboole_0(X1,X2) = k3_subset_1(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,axiom,
% 0.22/0.51      k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_subset_1(X1,k4_xboole_0(X1,X2))).
% 0.22/0.51  
% 0.22/0.51  cnf(u40,axiom,
% 0.22/0.51      k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,negated_conjecture,
% 0.22/0.51      k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u76,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u66,axiom,
% 0.22/0.51      k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u51,negated_conjecture,
% 0.22/0.51      sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u52,axiom,
% 0.22/0.51      k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u49,axiom,
% 0.22/0.51      k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u21,negated_conjecture,
% 0.22/0.51      sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  % (30789)# SZS output end Saturation.
% 0.22/0.51  % (30789)------------------------------
% 0.22/0.51  % (30789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30789)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (30789)Memory used [KB]: 6140
% 0.22/0.51  % (30789)Time elapsed: 0.101 s
% 0.22/0.51  % (30789)------------------------------
% 0.22/0.51  % (30789)------------------------------
% 0.22/0.51  % (30767)Success in time 0.148 s
%------------------------------------------------------------------------------
