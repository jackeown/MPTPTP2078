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
% DateTime   : Thu Dec  3 13:08:46 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u23,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u37,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u55,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u41,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u33,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )).

cnf(u58,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u56,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u57,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u46,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u48,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) )).

cnf(u50,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u17,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u44,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u38,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 )).

cnf(u34,axiom,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 )).

cnf(u32,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

% (28702)Refutation not found, incomplete strategy% (28702)------------------------------
% (28702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28702)Termination reason: Refutation not found, incomplete strategy

% (28702)Memory used [KB]: 10618
% (28715)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (28702)Time elapsed: 0.116 s
% (28702)------------------------------
% (28702)------------------------------
% (28704)Refutation not found, incomplete strategy% (28704)------------------------------
% (28704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28704)Termination reason: Refutation not found, incomplete strategy

% (28704)Memory used [KB]: 10618
% (28704)Time elapsed: 0.115 s
% (28704)------------------------------
% (28704)------------------------------
% (28715)Refutation not found, incomplete strategy% (28715)------------------------------
% (28715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28715)Termination reason: Refutation not found, incomplete strategy

% (28715)Memory used [KB]: 10618
% (28715)Time elapsed: 0.130 s
% (28715)------------------------------
% (28715)------------------------------
cnf(u21,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u36,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.55  % (28699)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (28702)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (28704)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.56  % (28699)# SZS output start Saturation.
% 0.21/0.56  cnf(u20,negated_conjecture,
% 0.21/0.56      l1_struct_0(sK0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u23,axiom,
% 0.21/0.56      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.56  
% 0.21/0.56  cnf(u37,axiom,
% 0.21/0.56      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.56  
% 0.21/0.56  cnf(u19,negated_conjecture,
% 0.21/0.56      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u55,negated_conjecture,
% 0.21/0.56      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u45,axiom,
% 0.21/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u41,axiom,
% 0.21/0.56      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u33,axiom,
% 0.21/0.56      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))).
% 0.21/0.56  
% 0.21/0.56  cnf(u58,negated_conjecture,
% 0.21/0.56      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u56,negated_conjecture,
% 0.21/0.56      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.56  
% 0.21/0.56  cnf(u57,negated_conjecture,
% 0.21/0.56      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u46,negated_conjecture,
% 0.21/0.56      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u48,axiom,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1)))).
% 0.21/0.56  
% 0.21/0.56  cnf(u50,axiom,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u17,negated_conjecture,
% 0.21/0.56      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.56  
% 0.21/0.56  cnf(u44,axiom,
% 0.21/0.56      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.21/0.56  
% 0.21/0.56  cnf(u38,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X0,X0)) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u34,axiom,
% 0.21/0.56      k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u32,axiom,
% 0.21/0.56      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.21/0.56  
% 0.21/0.56  % (28702)Refutation not found, incomplete strategy% (28702)------------------------------
% 0.21/0.56  % (28702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28702)Memory used [KB]: 10618
% 0.21/0.56  % (28715)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (28702)Time elapsed: 0.116 s
% 0.21/0.56  % (28702)------------------------------
% 0.21/0.56  % (28702)------------------------------
% 0.21/0.56  % (28704)Refutation not found, incomplete strategy% (28704)------------------------------
% 0.21/0.56  % (28704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28704)Memory used [KB]: 10618
% 0.21/0.56  % (28704)Time elapsed: 0.115 s
% 0.21/0.56  % (28704)------------------------------
% 0.21/0.56  % (28704)------------------------------
% 0.21/0.56  % (28715)Refutation not found, incomplete strategy% (28715)------------------------------
% 0.21/0.56  % (28715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28715)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28715)Memory used [KB]: 10618
% 0.21/0.56  % (28715)Time elapsed: 0.130 s
% 0.21/0.56  % (28715)------------------------------
% 0.21/0.56  % (28715)------------------------------
% 0.21/0.56  cnf(u21,axiom,
% 0.21/0.56      k2_subset_1(X0) = X0).
% 0.21/0.56  
% 0.21/0.56  cnf(u36,negated_conjecture,
% 0.21/0.56      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.56  
% 0.21/0.56  % (28699)# SZS output end Saturation.
% 0.21/0.56  % (28699)------------------------------
% 0.21/0.56  % (28699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28699)Termination reason: Satisfiable
% 0.21/0.56  
% 0.21/0.56  % (28699)Memory used [KB]: 6268
% 0.21/0.56  % (28699)Time elapsed: 0.118 s
% 0.21/0.56  % (28699)------------------------------
% 0.21/0.56  % (28699)------------------------------
% 0.21/0.56  % (28710)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (28692)Success in time 0.192 s
%------------------------------------------------------------------------------
